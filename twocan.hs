{-# LANGUAGE
  NoMonomorphismRestriction,
  LambdaCase,
  RecursiveDo,
  RankNTypes,
  ExplicitForAll #-}

module Twocan where

import Useful
import UnionFind

import Prelude hiding (exp, lookup, all)
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.ST.Class
import Control.Monad.State
import Data.Foldable
import Data.STRef
import Data.Traversable
import Data.Tuple
import qualified Data.Map as M
import Debug.Trace


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
  | TSum (M.Map Nm Typ)
  | TProd (M.Map Nm Typ)
  deriving (Eq, Ord, Show)

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
  where f = case op of
              Plus -> (+)
              Minus -> (-)
              Times -> (*)
              Over -> div

getEnv = ask

withVar = local .: M.insert

withEnv = local . const

runEval = flip runReader M.empty . eval


-- Type Inference

data Inf s =
    IPrim
  | IFun (Inf s) (Inf s)
  | ISum (M.Map Nm (Inf s))
  | IProd (M.Map Nm (Inf s))
  | IMyst (Ufr s (Myst s))

data Myst s = MVar Var | MInf (Inf s)

infer :: Exp -> forall s. ReaderT (Env (Inf s)) (StateT [Var] (ST s)) (Inf s)
infer = (. debug "infer") $ \ case
  EPrim _ -> return IPrim
  EVar var -> lookup var <$> getEnv
  EOp op expL expR -> do
    infer expL >>= liftST . unify IPrim
    infer expR >>= liftST . unify IPrim
    return IPrim
  EFun var exp -> do
    typX <- unknown
    withVar var typX $ IFun typX <$> infer exp
  EApp expF expX -> do
    typX <- infer expX
    typY <- unknown
    infer expF >>= liftST . unify (IFun typX typY)
    return typY
  ELet var expX expY -> do
    typX <- unknown
    withVar var typX $ infer expX >>= liftST . unify typX >> infer expY
  EBranch expI expT expE -> do
    infer expI >>= liftST . unify IPrim
    typT <- infer expT
    typE <- infer expE
    typ <- unknown
    liftST $ unify typT typ
    liftST $ unify typE typ
    return typ
  ESum nm exp -> ISum . M.singleton nm <$> infer exp
  -- ECase expX expsF -> do
  --   typsF <- traverse infer expsF
  --   typX <- infer exp
  -- TODO: make new type variables, ensure things match up.
  EProd exps -> IProd <$> traverse infer exps
  EProj nm exp -> do
    typ <- unknown
    infer exp >>= liftST . unify (IProd (M.fromList [(nm, typ)]))
    return typ

unknown = do
  (var : vars) <- get
  put vars
  liftST $ IMyst <$> newUfr (MVar var)

unify typ1 typ2 =
  ((,) <$> typOfInf typ1 <*> typOfInf typ2) >>=
  -- TODO: be less evil....
  (\ x -> debug "unify" x `seq` unify' (typ1, typ2))

-- TODO: deal with structural subtyping.
unify' = \ case
  (IPrim, IPrim) -> pure ()
  (IFun typX1 typY1, IFun typX2 typY2) ->
    unify typX2 typX1 *> unify typY1 typY2
  (ISum typs1, ISum typs2) ->
    traverse_ unifySum $ union typs1 typs2
  (IProd typs1, IProd typs2) ->
    traverse_ unifyProd $ union typs1 typs2
  (IMyst mystr1, IMyst mystr2) -> unifyMyst mystr1 mystr2
  (IMyst mystr1, typ2) -> do
    myst1 <- readUfr mystr1
    case myst1 of
      MVar _ -> writeUfr mystr1 $ MInf typ2
      MInf typ1 -> unify typ1 typ2
  (typ1, IMyst mystr2) -> do
    myst2 <- readUfr mystr2
    case myst2 of
      MVar _ -> writeUfr mystr2 $ MInf typ1
      MInf typ2 -> unify typ1 typ2
  where
    unifySum = \case
      Fst _ -> error "unifySum"
      Snd _ -> pure ()
      Both typ1 typ2 -> unify typ1 typ2
    unifyProd = \case
      Fst _ -> pure ()
      Snd _ -> error "unifyProd"
      Both typ1 typ2 -> unify typ1 typ2
    -- TODO
    unifyMyst = mergeUfr . curry $ \ case
      (MVar _, myst) -> pure myst
      (myst, MVar _) -> pure myst
      (MInf typ1, MInf typ2) -> unify typ1 typ2 *> pure (MInf typ2)

typOfInf :: Inf s -> ST s Typ
typOfInf = \ case
  IPrim -> pure TPrim
  IMyst mystr -> readUfr mystr >>= \ case
                 MVar var -> pure $ TVar var
                 MInf typ -> typOfInf typ
  IFun typX typY -> TFun <$> typOfInf typX <*> typOfInf typY
  ISum typs -> TSum <$> traverse typOfInf typs
  IProd typs -> TProd <$> traverse typOfInf typs

vars = map (('t':) . show) [0..]

runInfer exp = runST ((>>= typOfInf)
                      . flip evalStateT vars
                      . flip runReaderT M.empty
                      $ infer exp
                      :: forall s. ST s Typ)
