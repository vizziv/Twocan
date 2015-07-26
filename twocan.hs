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
  | TVar Var
  | TFun Typ Typ
  | TSum (Limits Typ)
  | TProd (Limits Typ)
  deriving (Eq, Ord, Show)

-- Required fields, possible fields (Nothing = all allowed), types of fields.
type Limits t = ((S.Set Nm), (Maybe (S.Set Nm)), (M.Map Nm t))

type Env t = M.Map Var t

data Val =
    VPrim Prim
  | VFun Var Exp (Env Val)
  | VSum Nm Val
  | VProd (M.Map Nm Val)
  deriving (Eq, Ord, Show)


-- Naming Conventions

{-

Sorts and modifiers are information that's usually coarser than a Haskell type.
Tags give extra qualitative information that's usually finer than the type.
These conventions are followed pretty consistently outside of top-level names.
The lists below aren't necessarily exhaustive.

Sorts:
  exp = expression
  typ = type (which we avoid writing in full because it's a Haskell keyword)
  val = value
  var = variable
  nm = name
  env = environment
  prim = primitive

Modifiers:
  q = optional (q is for "question"): Maybe, Either
  r = reference: Ufr, STRef
  s = collection: [], S.Set, M.Map

Tags:
  F, X, Y = a function, its argument, its result
  L, R = left, right
  I, T, E = if, then, else
  Req, Pos = required, possible (think "permissable")
  1, 2, ... = generic disambiguation

Examples:
  typF@(TFun typX typY) = types of a function, its argument, and its result
  nmsqPos = optional collection of possible names

-}


-- Expression Evaluation

eval :: Exp -> Reader (Env Val) Val
eval = \ case
  EPrim prim -> pure $ VPrim prim
  EVar var -> lookup var <$> getEnv
  EOp op expL expR -> evalOp op <$> eval expL <*> eval expR
  EFun var exp -> VFun var exp <$> getEnv
  EApp expF expX -> do
    valF <- eval expF
    valX <- eval expX
    apply valF valX
  ELet var expX expY -> do
    rec (valX, valY) <- withVar var valX $ (,) <$> eval expX <*> eval expY
    pure valY
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
    pure $ lookup nm vals

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
  | TIVar Var
  | TIFun (TypInf s) (TypInf s)
  | TISum (Limits (TypInf s))
  | TIProd (Limits (TypInf s))
  | TIMyst (Ufr s (Myst s))

data Myst s = MVar Var | MTypInf (TypInf s)

infer :: Exp -> forall s. ReaderT (Env (TypInf s)) (StateT [Var] (ST s)) (TypInf s)
infer = (. debug "infer") $ \ case
  EPrim _ -> pure TIPrim
  EVar var -> lookup var <$> getEnv >>= specialize
  EOp op expL expR -> do
    infer expL >>= unify TIPrim
    infer expR >>= unify TIPrim
    pure TIPrim
  EFun var exp -> do
    typX <- unknown
    withVar var typX $ TIFun typX <$> infer exp
  EApp expF expX -> do
    typX <- infer expX
    typY <- unknown
    infer expF >>= unify (TIFun typX typY)
    pure typY
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
    pure typ
  -- ESum nm exp -> TISum . M.singleton nm <$> infer exp
  -- ECase expX expsF -> do
  --   typsF <- traverse infer expsF
  --   typX <- infer exp
  -- TODO: make new type variables, ensure things match up.
  -- EProd exps -> TIProd <$> traverse infer exps
  -- EProj nm exp -> do
  --   typ <- unknown
  --   infer exp >>= unify (TIProd (M.fromList [(nm, typ)]))
  --   pure typ

unknown = do
  (var : vars) <- get
  put vars
  TIMyst <$> newUfr (MVar var)

unify typ1 typ2 =
  ((,) <$> purify typ1 <*> purify typ2) >>=
  -- TODO: be less evil....
  (\ x -> debug "unify" x `seq` unify' (typ1, typ2))

-- TODO: deal with structural subtyping.
unify' = \ case
  (TIPrim, TIPrim) -> pure ()
  (TIFun typX1 typY1, TIFun typX2 typY2) ->
    unify typX2 typX1 *> unify typY1 typY2
  (TISum (_, _, typs1), TISum (_, _, typs2)) ->
    traverse_ unifySum $ union typs1 typs2
  (TIProd (_, _, typs1), TIProd (_, _, typs2)) ->
    traverse_ unifyProd $ union typs1 typs2
  (TIMyst mystr1, TIMyst mystr2) -> unifyMyst mystr1 mystr2
  (TIMyst mystr1, typ2) -> do
    myst1 <- readUfr mystr1
    case myst1 of
      MVar _ -> writeTypInf mystr1 typ2
      MTypInf typ1 -> unify typ1 typ2
  (typ1, TIMyst mystr2) -> do
    myst2 <- readUfr mystr2
    case myst2 of
      MVar _ -> writeTypInf mystr2 typ1
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
        (MVar _, MVar _) -> mergeUfr const mystr1 mystr2
        (MVar _, MTypInf typ2) -> writeTypInf mystr1 typ2
        (MTypInf typ1, MVar _) -> writeTypInf mystr2 typ1
        (MTypInf typ1, MTypInf typ2) -> unify typ1 typ2

generalize typGen = do
  boundVars <- boundInEnv
  let gen = \ case
        TIPrim -> pure TIPrim
        TIFun typX typY -> TIFun <$> gen typX <*> gen typY
        TISum (nmsReq, nmsqPos, typs) ->
          TISum . (,,) nmsReq nmsqPos <$> traverse gen typs
        TIProd (nmsReq, nmsqPos, typs) ->
          TIProd . (,,) nmsReq nmsqPos <$> traverse gen typs
        TIMyst mystr -> readUfr mystr >>= \ case
                          MVar var -> pure $ if S.member var boundVars
                                             then TIMyst mystr
                                             else TIVar var
                          MTypInf typ -> gen typ
  typ <- gen typGen
  -- TODO: stop continuing not being less evil....
  purify typ >>= (\typDebug -> debug "generalized" typDebug `seq` pure typ)
  where
    boundInEnv =
      getEnv >>= foldlM (\vars typ -> S.union vars <$> boundInTyp typ) S.empty
    boundInTyp = \ case
      TIPrim -> pure S.empty
      TIVar _ -> pure S.empty
      TIFun typX typY -> S.union <$> boundInTyp typX <*> boundInTyp typY
      TISum (_, _, typs) -> foldl S.union S.empty <$> traverse boundInTyp typs
      TIProd (_, _, typs) -> foldl S.union S.empty <$> traverse boundInTyp typs
      TIMyst mystr -> readUfr mystr >>= \ case
                        MVar var -> pure $ S.singleton var
                        MTypInf typ -> boundInTyp typ

specialize = flip evalStateT M.empty . spc
  where
    spc = \ case
      TIPrim -> pure TIPrim
      TIVar var -> M.lookup var <$> get >>= \ case
                     Nothing -> do
                       -- Lift from the StateT [Var].
                       typ <- lift unknown
                       modify $ M.insert var typ
                       pure typ
                     Just typ -> pure typ
      TIFun typX typY -> TIFun <$> spc typX <*> spc typY
      -- TISum typs -> TISum <$> traverse spc typs
      -- TIProd typs -> TIProd <$> traverse spc typs
      TIMyst mystr -> readUfr mystr >>= \ case
                        MVar var -> pure $ TIMyst mystr
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
      -- TISum typs -> any id <$> traverse appearsIn typs
      -- TIProd typs -> any id <$> traverse appearsIn typs
      TIMyst mystrOther -> readUfr mystrOther >>= \ case
                             MVar var -> equalUfr mystr mystrOther
                             MTypInf typ -> appearsIn typ

purify = \ case
  TIPrim -> pure TPrim
  TIVar var -> pure $ TVar var
  TIFun typX typY -> TFun <$> purify typX <*> purify typY
  -- TISum typs -> TSum <$> traverse purify typs
  -- TIProd typs -> TProd <$> traverse purify typs
  TIMyst mystr -> readUfr mystr >>= \ case
                    MVar var -> pure $ TVar ('_':var)
                    MTypInf typ -> purify typ

vars = map (('t':) . show) [0..]

-- Eta-expansion enables inference of higher rank type needed for runST.
runTypInfer exp = runST $
  (>>= purify)
  . flip evalStateT vars
  . flip runReaderT M.empty
  $ infer exp
