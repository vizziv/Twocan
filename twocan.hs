{-# LANGUAGE
  NoMonomorphismRestriction,
  LambdaCase,
  RecursiveDo,
  RankNTypes,
  ExplicitForAll #-}

module Twocan where

import Useful
import UnionFind

import Prelude hiding (exp, lookup, any, all, foldl, foldr)
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.State
import Data.Foldable
import Data.STRef
import Data.Traversable
import qualified Data.Map as M
import qualified Data.Set as S


-- Language Definition

type Prim = Integer
type Nm = String
type Var = String

data Op = Plus | Minus | Times | Over deriving (Eq, Ord, Show)

data Exp =
    EPrim Prim
  | EVar Var
  | EOp Op Exp Exp
  | EFun Var Exp
  | EApp Exp Exp
  | ELet Var Exp Exp
  -- Temporary branch if (<= 0) operator until we have real booleans.
  | EBranch Exp Exp Exp
  | ESum Nm Exp
  -- Expressions in the map are functions handling each case.
  | ECase Exp (M.Map Nm Exp)
  | EProd (M.Map Nm Exp)
  | EProj Nm Exp
  deriving (Eq, Ord, Show)

data Typ =
    TPrim
  | TVar Var Kind
  | TFun Typ Typ
  | TSum (M.Map Nm Typ)
  | TProd (M.Map Nm Typ)
  deriving (Eq, Ord, Show)

data Kind =
    KAny
  | KSum Bound
  | KProd Bound
  -- A temporary KAny (w.r.t. writing this program, not executing it).
  | KTmp
  deriving (Eq, Ord, Show)

type Bound = ((S.Set Nm), (Maybe (S.Set Nm)), (M.Map Nm Typ))

type Env t = M.Map Var t

data Val =
    VPrim Prim
  | VFun Var Exp (Env Val)
  | VSum Nm Val
  | VProd (M.Map Nm Val)
  deriving (Eq, Ord, Show)


-- Conventions

{-

Abbreviations:
  exp = expression
  typ = type (which we avoid because it's a Haskell keyword)
  val = value
  inf = inference
  env = environment

Tags:
  X = argument of a function (e.g. TFun typX typY)
  Y = result of a function (e.g. EFun evar expY)
  F = function itself

In effectful code, use
  pure and *> when (almost) completely applicative,
  return and >> when monadic or when resulting in much nicer infix precedence.

I've grown accustomed to SML's fn, thus the extensive \ case use....

-}


-- Expression Evaluation

eval :: Exp -> Reader (Env Val) Val
eval = \ case
  EPrim prim -> return $ VPrim prim
  EVar var -> lookup var <$> getEnv
  EOp op expL expR -> evalOp op <$> eval expL <*> eval expR
  EFun var exp -> VFun var exp <$> getEnv
  EApp expF expX -> do
    valF <- eval expF
    valX <- eval expX
    apply valF valX
  ELet var expX expY -> do
    rec (valX, valY) <- withVar var valX $ (,) <$> eval expX <*> eval expY
    return valY
  EBranch expI expT expE -> do
    VPrim n <- eval expI
    eval $ if n <= 0 then expT else expE
  ESum nm exp -> VSum nm <$> eval exp
  ECase exp exps -> do
    (VSum nm valX) <- eval exp
    valF <- eval $ lookup nm exps
    apply valF valX
  EProd exps -> VProd <$> traverse eval exps
  EProj nm exp -> do
    (VProd vals) <- eval exp
    return $ lookup nm vals

apply (VFun var expY env) valX = withEnv env . withVar var valX $ eval expY

evalOp op (VPrim primL) (VPrim primR) = VPrim (f primL primR)
  where
    f = case op of
          Plus -> (+)
          Minus -> (-)
          Times -> (*)
          Over -> div

getEnv = ask

withVar = local .: M.insert

withEnv = local . const

runEval = flip runReader M.empty . eval


-- Type Inference

data TypInf s =
    TIPrim
  -- Only used in type environment ("between" generalize and specialize).
  | TIVar Var (KindInf s)
  | TIFun (TypInf s) (TypInf s)
  | TISum (M.Map Nm (TypInf s))
  | TIProd (M.Map Nm (TypInf s))
  | TIMyst (Ufr s (Myst s))

data KindInf s =
    KIAny
  | KISum (BoundInf s)
  | KIProd (BoundInf s)
  -- A temporary KAny (w.r.t. writing this program, not executing it).
  | KITmp

type BoundInf s = ((S.Set Nm), (Maybe (S.Set Nm)), (M.Map Nm (TypInf s)))

data Myst s = MVar Var (KindInf s) | MTypInf (TypInf s)

infer :: Exp -> forall s. ReaderT (Env (TypInf s)) (StateT [Var] (ST s)) (TypInf s)
infer = (. debug "infer") $ \ case
  EPrim _ -> return TIPrim
  EVar var -> lookup var <$> getEnv >>= specialize
  EOp op expL expR -> do
    infer expL >>= unify TIPrim
    infer expR >>= unify TIPrim
    return TIPrim
  EFun var exp -> do
    typX <- unknown
    withVar var typX $ TIFun typX <$> infer exp
  EApp expF expX -> do
    typX <- infer expX
    typY <- unknown
    infer expF >>= unify (TIFun typX typY)
    return typY
  ELet var expX expY -> do
    typX <- unknown
    withVar var typX $ infer expX >>= unify typX
    typXGen <- generalize typX
    withVar var typXGen $ infer expY
  EBranch expI expT expE -> do
    infer expI >>= unify TIPrim
    typT <- infer expT
    typE <- infer expE
    typ <- unknown
    unify typT typ
    unify typE typ
    return typ
  ESum nm exp -> TISum . M.singleton nm <$> infer exp
  -- ECase expX expsF -> do
  --   typsF <- traverse infer expsF
  --   typX <- infer exp
  -- TODO: make new type variables, ensure things match up.
  EProd exps -> TIProd <$> traverse infer exps
  EProj nm exp -> do
    typ <- unknown
    infer exp >>= unify (TIProd (M.fromList [(nm, typ)]))
    return typ

unknown = do
  (var : vars) <- get
  put vars
  TIMyst <$> newUfr (MVar var KITmp)

unify typ1 typ2 =
  ((,) <$> typOfTypInf typ1 <*> typOfTypInf typ2) >>=
  -- TODO: be less evil....
  (\ x -> debug "unify" x `seq` unify' (typ1, typ2))

-- TODO: deal with structural subtyping.
unify' = \ case
  (TIPrim, TIPrim) -> pure ()
  (TIFun typX1 typY1, TIFun typX2 typY2) ->
    unify typX2 typX1 *> unify typY1 typY2
  (TISum typs1, TISum typs2) ->
    traverse_ unifySum $ union typs1 typs2
  (TIProd typs1, TIProd typs2) ->
    traverse_ unifyProd $ union typs1 typs2
  (TIMyst mystr1, TIMyst mystr2) -> unifyMyst mystr1 mystr2
  (TIMyst mystr1, typ2) -> do
    myst1 <- readUfr mystr1
    case myst1 of
      MVar _ _ -> writeTypInf mystr1 typ2
      MTypInf typ1 -> unify typ1 typ2
  (typ1, TIMyst mystr2) -> do
    myst2 <- readUfr mystr2
    case myst2 of
      MVar _ _ -> writeTypInf mystr2 typ1
      MTypInf typ2 -> unify typ1 typ2
  where
    unifySum = \ case
      Fst _ -> error "unifySum"
      Snd _ -> pure ()
      Both typ1 typ2 -> unify typ1 typ2
    unifyProd = \ case
      Fst _ -> pure ()
      Snd _ -> error "unifyProd"
      Both typ1 typ2 -> unify typ1 typ2
    -- TODO
    unifyMyst mystr1 mystr2 =
      (,) <$> readUfr mystr1 <*> readUfr mystr2 >>= \ case
        (MVar _ _, MVar _ _) -> mergeUfr const mystr1 mystr2
        (MVar _ _, MTypInf typ2) -> writeTypInf mystr1 typ2
        (MTypInf typ1, MVar _ _) -> writeTypInf mystr2 typ1
        (MTypInf typ1, MTypInf typ2) -> unify typ1 typ2

generalize typGen = do
  boundVars <- envBoundVars
  let gen = \ case
        TIPrim -> pure TIPrim
        TIFun typX typY -> TIFun <$> gen typX <*> gen typY
        TISum typs -> TISum <$> traverse gen typs
        TIProd typs -> TIProd <$> traverse gen typs
        TIMyst mystr -> readUfr mystr >>= \ case
                         MVar var _ -> pure $ if S.member var boundVars
                                              then TIMyst mystr
                                              else TIVar var KITmp
                         MTypInf typ -> gen typ
  typ <- gen typGen
  -- TODO: stop continuing not being less evil....
  typOfTypInf typ >>= (\typDebug -> debug "generalized" typDebug `seq` pure typ)
  where
    envBoundVars :: ReaderT (Env (TypInf s)) (StateT [Var] (ST s)) (S.Set Var)
    envBoundVars =
      getEnv >>= foldlM (\vars typ -> S.union vars <$> typBoundVars typ) S.empty
    typBoundVars = \ case
      TIPrim -> pure S.empty
      TIVar _ _ -> pure S.empty
      TIFun typX typY -> S.union <$> typBoundVars typX <*> typBoundVars typY
      TISum typs -> foldl S.union S.empty <$> traverse typBoundVars typs
      TIProd typs -> foldl S.union S.empty <$> traverse typBoundVars typs
      TIMyst mystr -> readUfr mystr >>= \ case
                       MVar var _ -> pure $ S.singleton var
                       MTypInf typ -> typBoundVars typ

specialize = flip evalStateT M.empty . spc
  where
    spc :: TypInf s -> StateT (Env (TypInf s)) (ReaderT (Env (TypInf s)) (StateT [Var] (ST s))) (TypInf s)
    spc = \ case
      TIPrim -> pure TIPrim
      TIVar var _ -> M.lookup var <$> get >>= \ case
                    Nothing -> do
                      -- Lift from the StateT [Var].
                      typ <- lift unknown
                      modify $ M.insert var typ
                      pure typ
                    Just typ -> pure typ
      TIFun typX typY -> TIFun <$> spc typX <*> spc typY
      TISum typs -> TISum <$> traverse spc typs
      TIProd typs -> TIProd <$> traverse spc typs
      TIMyst mystr -> readUfr mystr >>= \ case
                       MVar var _ -> pure $ TIMyst mystr
                       MTypInf typ -> spc typ

writeTypInf mystr typ = do
  infinite <- appearsIn typ
  if debug "infinite" infinite
  then error "unify: infinite type"
  else writeUfr mystr $ MTypInf typ
  where
    appearsIn = \ case
      TIPrim -> pure False
      TIFun typX typY -> (||) <$> appearsIn typX <*> appearsIn typY
      TISum typs -> any id <$> traverse appearsIn typs
      TIProd typs -> any id <$> traverse appearsIn typs
      TIMyst mystrOther -> readUfr mystrOther >>= \ case
                            MVar var _ -> equalUfr mystr mystrOther
                            MTypInf typ -> appearsIn typ

typOfTypInf = \ case
  TIPrim -> pure TPrim
  TIVar var _ -> pure $ TVar var KTmp
  TIFun typX typY -> TFun <$> typOfTypInf typX <*> typOfTypInf typY
  TISum typs -> TSum <$> traverse typOfTypInf typs
  TIProd typs -> TProd <$> traverse typOfTypInf typs
  TIMyst mystr -> readUfr mystr >>= \ case
                   MVar var _ -> pure $ TVar ('_':var) KTmp
                   MTypInf typ -> typOfTypInf typ

vars = map (('t':) . show) [0..]

-- Eta-expansion enables inference of higher rank type needed for runST.
runInfer exp = runST $
  (>>= typOfTypInf)
  . flip evalStateT vars
  . flip runReaderT M.empty
  $ infer exp
