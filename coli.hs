module Coli where

import Prelude hiding (exp)
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.Traversable (traverse)
import qualified Data.Map as M


-- Expression Definition

type Prim = Integer
type ExpVar = String
type TypVar = String

data Op = Plus | Minus | Times | Over deriving (Eq, Ord, Show)

data Exp =
    EPrim Prim
  | EVar ExpVar
  | EOp Op Exp Exp
  | EFun ExpVar Exp
  | EApp Exp Exp
  deriving (Eq, Ord, Show)


-- Type Definition

data Typ =
    TPrim
  | TVar TypVar
  | TFun Typ Typ
  deriving (Eq, Ord, Show)


-- Expression Evaluation

type Env = M.Map ExpVar Val

data Val =
    VPrim Prim
  | VFun ExpVar Exp Env
  deriving (Eq, Ord, Show)

eval :: Exp -> Reader Env Val
eval exp = case exp of
  EPrim prim -> pure $ VPrim prim
  EVar var -> envLookup var <$> getEnv
  EOp op expL expR -> evalOp op <$> eval expL <*> eval expR
  EFun var exp -> VFun var exp <$> getEnv
  EApp expF expX -> do
    valF <- eval expF
    valX <- eval expX
    evalApp valF valX

evalOp op (VPrim primL) (VPrim primR) = VPrim (f primL primR)
    where
      f = case op of
            Plus -> (+)
            Minus -> (-)
            Times -> (*)
            Over -> div

evalApp (VFun var exp env) val = putVar env var val $ eval exp

getEnv = ask

putVar env var val = local $ M.insert var val . const env

runEval = flip runReader M.empty . eval


-- Type Inference

type Eenv = M.Map ExpVar Typ
type Tenv = M.Map TypVar Typ

infer :: Exp -> StateT ([TypVar], Tenv) (Reader Eenv) Typ
infer exp =
    case exp of
      EPrim _ -> pure TPrim
      EVar evar -> envLookup evar <$> getEenv
      EOp op expL expR -> do
        infer expL >>= unify TPrim
        substEenv $ do
        infer expR >>= unify TPrim
        pure TPrim
      EFun evar exp -> do
        typX <- freshTyp
        setEvar evar typX $ do
        typF <- infer exp
        TFun <$> subst typX <*> pure typF
      EApp expF expX -> do
        typF <- infer expF
        substEenv $ do
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
      TVar tvar -> fromMaybe typ . M.lookup tvar <$> getTenv
      TFun typX typY -> TFun <$> subst typX <*> subst typY
      _ -> pure typ

setEvar evar typ = local (M.insert evar typ)

setTvar tvar typ =
    if tvar `isFreeTvarIn` typ
    then error $ "infinite: " ++ show (TVar tvar) ++ " = " ++ show typ ++ "."
    else modifyTenv (M.insert tvar typ) *> substTenv

substEenv next = do
  eenv <- getEenv
  eenvSubst <- traverse subst eenv
  modifyEenv (const eenvSubst) next

substTenv = do
  tenv <- getTenv
  tenvSubst <- traverse subst tenv
  modifyTenv (const tenvSubst)

getEenv = ask

getTenv = snd <$> get

modifyEenv = local

modifyTenv f = modify (\(tvars, tenv) -> (tvars, f tenv))

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
    fst . flip runReader M.empty . flip runStateT (names, M.empty) . infer


-- General

envLookup var = fromMaybe (error $ "not found: " ++ var ++ ".") . M.lookup var
