{-# LANGUAGE RecursiveDo #-}

module Coli where

import Prelude hiding (exp)
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe (fromMaybe)
import Data.Traversable (traverse)
import qualified Data.Map as M


-- Expression Definition

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
  | EIfZero Exp Exp Exp
  -- EInj Nm Exp
  -- EDes Exp (M.Map Typ Exp)
  -- ECon (M.Map Typ Exp)
  -- EProj Nm Exp
  deriving (Eq, Ord, Show)


-- Type Definition

data Typ =
    TPrim
  | TVar TVar
  | TFun Typ Typ
  deriving (Eq, Ord, Show)


-- General

envLookup var = fromMaybe (error $ "not found: " ++ var ++ ".") . M.lookup var


-- Expression Evaluation

type Env = M.Map EVar Val

data Val =
    VPrim Prim
  | VFun EVar Exp Env
  deriving (Eq, Ord, Show)

eval :: Exp -> Reader Env Val
eval exp = case exp of
  EPrim prim -> pure $ VPrim prim
  EVar var -> envLookup var <$> getEnv
  EOp op expL expR -> evalOp op <$> eval expL <*> eval expR
  EFun var exp -> VFun var exp <$> getEnv
  EApp expF expX -> do
    (VFun var expY env) <- eval expF
    valX <- eval expX
    withEnv env . withVar var valX $ eval expY
  ELet var expX expY -> mdo
    (valX, valY) <- withVar var valX $ (,) <$> eval expX <*> eval expY
    pure valY
  EIfZero expI expT expE -> do
    valI <- eval expI
    eval $ if valI == VPrim 0 then expT else expE

evalOp op (VPrim primL) (VPrim primR) = VPrim (f primL primR)
    where
      f = case op of
            Plus -> (+)
            Minus -> (-)
            Times -> (*)
            Over -> div

getEnv = ask

withVar var val = local $ M.insert var val

withEnv = local . const

runEval = flip runReader M.empty . eval


-- Type Inference

type EEnv = M.Map EVar Typ
type TEnv = M.Map TVar Typ

infer :: Exp -> StateT ([TVar], TEnv) (Reader EEnv) Typ
infer exp =
    case exp of
      EPrim _ -> pure TPrim
      EVar evar -> envLookup evar <$> getEEnv
      EOp op expL expR -> do
        infer expL >>= unify TPrim
        substEEnv $ do
        infer expR >>= unify TPrim
        pure TPrim
      EFun evar exp -> do
        typX <- freshTyp
        setEvar evar typX $ do
        typF <- infer exp
        TFun <$> subst typX <*> pure typF
      EApp expF expX -> do
        typF <- infer expF
        substEEnv $ do
        typX <- infer expX
        typFSubst <- subst typF
        case typFSubst of
          TFun typXSubst typY | noFreeTvars typFSubst ->
            unify typX typXSubst *> subst typY
          _ -> do
            typY <- freshTyp
            subst typF >>= unify (TFun typX typY)
            subst typY

unify typ1 typ2 =
    case (typ1, typ2) of
      (TPrim, TPrim) -> pure ()
      (TVar tvar, typ) -> setTvar tvar typ
      (typ, TVar tvar) -> setTvar tvar typ
      (TFun typX1 typY1, TFun typX2 typY2) ->
        unify typX1 typX2 *> unify typY1 typY2
      _ -> error $ "have: " ++ show typ1 ++ ", need: " ++ show typ2 ++ "."

subst typ =
    case typ of
      TVar tvar -> fromMaybe typ . M.lookup tvar <$> getTEnv
      TFun typX typY -> TFun <$> subst typX <*> subst typY
      _ -> pure typ

setEvar evar typ = local (M.insert evar typ)

setTvar tvar typ =
    if tvar `isFreeTvarIn` typ
    then error $ "infinite: " ++ show (TVar tvar) ++ " = " ++ show typ ++ "."
    else modifyTEnv (M.insert tvar typ) *> substTEnv

substEEnv next = do
  eenv <- getEEnv
  eenvSubst <- traverse subst eenv
  modifyEEnv (const eenvSubst) next

substTEnv = do
  tenv <- getTEnv
  tenvSubst <- traverse subst tenv
  modifyTEnv (const tenvSubst)

getEEnv = ask

getTEnv = snd <$> get

modifyEEnv = local

modifyTEnv f = modify (\(tvars, tenv) -> (tvars, f tenv))

isFreeTvarIn tvar typ =
    case typ of
      TVar tvarOther -> tvar == tvarOther
      TFun typX typY -> tvar `isFreeTvarIn` typX || tvar `isFreeTvarIn` typY
      _ -> False

noFreeTvars typ =
    case typ of
      TVar _ -> False
      TFun typX typY -> noFreeTvars typX && noFreeTvars typY
      _ -> True

freshTyp = do
  (tvar : tvars, _) <- get
  modify (\(_, tenv) -> (tvars, tenv))
  pure (TVar tvar)

names = map (:[]) ['a'..'s'] ++ map (('t':) . show) [0..]

runInfer =
    fst
    . flip runReader M.empty
    . flip runStateT (names, M.empty)
    . infer
