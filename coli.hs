{-# LANGUAGE NoMonomorphismRestriction, LambdaCase, RecursiveDo #-}

module Coli where

import Prelude hiding (exp, lookup)
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable (foldlM)
import Data.Maybe (fromMaybe)
import Data.Traversable (traverse)
import qualified Data.Map as M


-- Language Definition

type Prim = Integer
type Nm = String
type EVar = String
type TVar = String

data Op = Plus | Minus | Times | Over deriving (Eq, Ord, Show)

data Exp =
    EPrim Prim
  | EVar EVar
  | EOp Op Exp Exp
  | EFun EVar Exp
  | EApp Exp Exp
  | ELet EVar Exp Exp
  | EBranch Exp Exp Exp
  | ESum Nm Exp
  | ECase Exp (M.Map Nm Exp)
  | EProd (M.Map Nm Exp)
  | EProj Nm Exp
  deriving (Eq, Ord, Show)

data Typ =
    TPrim
  | TVar TVar
  | TFun Typ Typ
  | TSum (M.Map Nm Typ)
  | TProd (M.Map Nm Typ)
  deriving (Eq, Ord, Show)

type Env = M.Map EVar Val

data Val =
    VPrim Prim
  | VFun EVar Exp Env
  | VSum Nm Val
  | VProd (M.Map Nm Val)
  deriving (Eq, Ord, Show)


-- General

infixl 1 >>==
(>>==) :: Monad m => m b -> (a -> b -> m c) -> a -> m c
x >>== f = (x >>=) . f

(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) = fmap . fmap

lookup key = fromMaybe (error $ "no entry for " ++ key) . M.lookup key


-- Expression Evaluation

eval :: Exp -> Reader Env Val
eval = \case
  EPrim prim -> pure $ VPrim prim
  EVar var -> lookup var <$> getEnv
  EOp op expL expR -> evalOp op <$> eval expL <*> eval expR
  EFun var exp -> VFun var exp <$> getEnv
  EApp expF expX -> do
    valF <- eval expF
    valX <- eval expX
    apply valF valX
  ELet var expX expY -> mdo
    (valX, valY) <- withVar var valX $ (,) <$> eval expX <*> eval expY
    pure valY
  EBranch expI expT expE -> do
    valI <- eval expI
    eval $ if valI <= VPrim 0 then expT else expE
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

type EEnv = M.Map EVar Typ
type TEnv = M.Map TVar Typ

infer :: Exp -> State ([TVar], TEnv, EEnv) Typ
infer = \case
  EPrim _ -> pure TPrim
  EVar evar -> lookup evar <$> getEEnv
  EOp op expL expR -> do
    infer expL >>= unify TPrim
    infer expR >>= unify TPrim
    pure TPrim
  EFun evar exp -> do
    typX <- freshTyp
    withEVar evar typX $ do
      typY <- infer exp
      TFun <$> subst typX <*> pure typY
  EApp expF expX -> do
    typF <- infer expF
    typX <- infer expX
    typY <- freshTyp
    -- TODO: check for subtype.
    subst typF >>= unify (TFun typX typY)
    subst typY
  ELet evar expX expY -> mdo
    typX <- freshTyp
    withEVar evar typX $ do
      infer expX >>= unify typX
      infer expY
  EBranch expI expT expE -> do
    infer expI >>= unify TPrim
    typT <- infer expT
    typE <- infer expE
    subst typT >>= unify typE
    subst typE
  -- ESum nm exp -> TSum . M.singleton nm <$> infer exp
  -- ECase expX expsF -> do
  --   TSum typsX <- infer exp
  --   typsF <- traverse infer expsF
  --   M.foldM typsY
  -- EProd exps -> TProd <$> traverse infer exps
  -- EProj nm exp -> do
  --   TProd typs <-

unify = curry $ \case
  (TPrim, TPrim) -> pure TPrim
  (TVar tvar, typ) -> setTVar tvar typ
  (typ, TVar tvar) -> setTVar tvar typ
  (TFun typX1 typY1, TFun typX2 typY2) ->
    TFun <$> unify typX1 typX2 <*> unify typY1 typY2
  -- (TSum typs1, TSum typs2) ->
  --   TSum <$> traverse unify' (union typs1 typs2)
  -- (TProd typs1, TProd typs2) ->
  --   TProd <$> traverse unify' (intersect typs1 typs2)
  (typ1, typ2) -> error $ "can't unify " ++ show typ1 ++ " with " ++ show typ2

data OneOrTwo a = One a | Two a a

union m1 m2 = M.unionWith both (fmap One m1) (fmap One m2)
    where both (One x) (One y) = Two x y

intersect = M.intersectionWith Two

unify' = \case
  One typ -> pure typ
  Two typ1 typ2 -> unify typ1 typ2

subst = \case
  typ@(TVar tvar) -> fromMaybe typ . M.lookup tvar <$> getTEnv
  TFun typX typY -> TFun <$> subst typX <*> subst typY
  typ -> pure typ

withEVar evar typ action = do
  typqOld <- M.lookup evar <$> getEEnv
  modifyEEnv $ M.insert evar typ
  result <- action
  case typqOld of
    Nothing -> modifyEEnv (M.delete evar)
    Just typOld -> modifyEEnv $ M.insert evar typOld
  pure result

setTVar tvar typ =
  if tvar `isFreeTVarIn` typ
  then error $ "infinite type " ++ show (TVar tvar) ++ " = " ++ show typ
  else modifyTEnv (M.insert tvar typ) *> substEnvs *> pure typ

-- TODO: maybe use lenses to factor this nicely?

substEnvs = do
  eenv <- getEEnv
  eenvSubst <- traverse subst eenv
  modifyEEnv (const eenvSubst)
  tenv <- getTEnv
  tenvSubst <- traverse subst tenv
  modifyTEnv (const tenvSubst)

getEEnv = (\ (_, eenv, _) -> eenv) <$> get

getTEnv = (\ (_, _, tenv) -> tenv) <$> get

modifyEEnv f = modify (\(tvars, eenv, tenv) -> (tvars, f eenv, tenv))

modifyTEnv f = modify (\(tvars, eenv, tenv) -> (tvars, eenv, f tenv))

isFreeTVarIn tvar = \case
  TVar tvarOther -> tvar == tvarOther
  TFun typX typY -> tvar `isFreeTVarIn` typX || tvar `isFreeTVarIn` typY
  _ -> False

noFreeTVars = \case
  TVar _ -> False
  TFun typX typY -> noFreeTVars typX && noFreeTVars typY
  _ -> True

freshTyp = do
  (tvar : tvars, _, _) <- get
  modify (\(_, eenv, tenv) -> (tvars, eenv, tenv))
  pure (TVar tvar)

names = map (:[]) ['a'..'s'] ++ map (('t':) . show) [0..]

runInfer = fst . flip runState (names, M.empty, M.empty) . infer
