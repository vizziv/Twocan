{-# LANGUAGE
  NoMonomorphismRestriction,
  LambdaCase,
  RecursiveDo,
  RankNTypes,
  ExplicitForAll #-}

module Coli where

import Prelude hiding (exp, lookup, all)
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.ST
import Data.Foldable
import Data.Maybe (fromMaybe)
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
  typ = TYPe
  exp = EXPression

Tags:
  X = argument of a function (e.g. TFun typX typY)
  Y = result of a function (e.g. EFun evar expY)
  F = function itself

In effectful code, use
  pure and *> when (almost) completely applicative,
  return and >> when monadic or when resulting in much nicer infix precedence.

I've grown accustomed to SML's fn, thus the extensive \ case use....

-}


-- General

(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) = fmap . fmap

lookup key = fromMaybe (error $ "no entry for " ++ key) . M.lookup key

data OneOrTwo a = Fst a | Snd a | Both a a

onBoth f = \ case
  Fst x -> x
  Snd y -> y
  Both x y -> f x y

union m1 m2 = M.unionWith both (fmap Fst m1) (fmap Snd m2)
  where both (Fst x) (Snd y) = Both x y

intersect = M.intersectionWith Both

unreachable = error "unreachable"

debug on prefix x = if on then trace (prefix ++ ": " ++ show x) x else x


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
  | IUnknown
  | IRef (STRef s (Inf s))
  | IFun (Inf s) (Inf s)
  | ISum (M.Map Nm (Inf s))
  | IProd (M.Map Nm (Inf s))
  deriving (Eq)

data Constraint s = Inf s :<: Inf s

-- Order explicit throughout because subst and infer don't commute.
infer :: Exp -> forall s. ReaderT (Env (Inf s)) (ST s) (Inf s)
infer = (. debug True "infer") $ \ case
  EPrim _ -> pure IPrim
  EVar var -> lookup var <$> getEnv
  EOp op expL expR -> do
    infer expL >>= ensure . (:<: IPrim)
    infer expR >>= ensure . (:<: IPrim)
    return IPrim
  EFun var exp -> do
    typX <- unknown
    withVar var typX $ IFun typX <$> infer exp
  EApp expF expX -> do
    typX <- infer expX
    typY <- unknown
    infer expF >>= ensure . (:<: IFun typX typY)
    return typY
  ELet var expX expY -> do
    typX <- unknown
    withVar var typX $ infer expX >>= ensure . (:<: typX) >> infer expY
  EBranch expI expT expE -> do
    infer expI >>= ensure . (:<: IPrim)
    typT <- infer expT
    typE <- infer expE
    typ <- unknown
    ensure $ typT :<: typ
    ensure $ typE :<: typ
    return typ
  ESum nm exp -> ISum . M.singleton nm <$> infer exp
  -- ECase expX expsF -> do
  --   typsF <- traverse infer expsF
  --   typX <- infer exp
  -- TODO: make new type variables, ensure things match up.
  EProd exps -> IProd <$> traverse infer exps
  EProj nm exp -> do
    typ <- unknown
    infer exp >>= ensure . (:<: IProd (M.fromList [(nm, typ)]))
    return typ

ensure = undefined

unknown = undefined
