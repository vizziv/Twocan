module Coli where

import Prelude hiding (exp)
import Control.Applicative
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.Map ((!))
import Data.Traversable (traverse)
import qualified Data.Map as M


-- Expression Definition

type Prim = Integer
type ExpVar = String
type TypVar = String

data Op = Plus | Minus | Times deriving (Eq, Ord, Show)

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
  | VFun Env ExpVar Exp
  deriving (Eq, Ord, Show)

eval env exp = case exp of
  EPrim prim -> VPrim prim
  EVar var -> env ! var
  EOp op expL expR -> evalOp op (eval env expL) (eval env expR)
  EFun var exp -> VFun env var exp
  EApp expF expX -> evalApp (eval env expF) (eval env expX)

evalOp op (VPrim primL) (VPrim primR) = VPrim (f primL primR)
    where
      f = case op of
            Plus -> (+)
            Minus -> (-)
            Times -> (*)

evalApp (VFun env var exp) val = eval (M.insert var val env) exp


-- Type Inference

type Eenv = M.Map ExpVar Typ
type Tenv = M.Map TypVar Typ

infer :: Eenv -> Exp -> State ([TypVar], Tenv) Typ
infer eenv exp =
    case exp of
      EPrim _ -> pure TPrim
      EVar evar -> pure (eenv ! evar)
      EOp op expL expR -> do
        infer eenv expL >>= unify TPrim
        infer eenv expR >>= unify TPrim
        pure TPrim
      EFun evar exp -> do
        typX <- freshTyp
        typF <- infer (M.insert evar typX eenv) exp
        TFun <$> subst typX <*> pure typF
      EApp expF expX -> do
        typF <- infer eenv expF
        eenvF <- traverse subst eenv
        typX <- infer eenvF expX
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

setTvar tvar typ =
    if tvar `isFreeTvarIn` typ
    then error $ "infinite: " ++ show (TVar tvar) ++ " = " ++ show typ ++ "."
    else modifyTenv (M.insert tvar typ) *> substTenv

substTenv = do
  tenv <- getTenv
  tenvSubst <- traverse subst tenv
  modifyTenv (const tenvSubst)

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

getTenv = snd <$> get

modifyTenv f = modify (\(tvars, tenv) -> (tvars, f tenv))

names = map (:[]) ['a'..'s'] ++ map (('t':) . show) [0..]
