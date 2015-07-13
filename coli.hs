{-# LANGUAGE NoMonomorphismRestriction, LambdaCase, RecursiveDo #-}

module Coli where

import Prelude hiding (exp, lookup, all)
import Control.Applicative
import Control.Monad hiding (lub)
import Control.Monad.Identity hiding (lub)
import Control.Monad.Reader hiding (lub)
import Control.Monad.State hiding (lub)
import Control.Monad.Writer hiding (lub)
import Data.Foldable
import Data.Maybe (fromMaybe)
import Data.Traversable
import qualified Data.Map as M
import Debug.Trace


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
  | TVar TVar
  | TFun Typ Typ
  | TSum (M.Map Nm Typ)
  | TProd (M.Map Nm Typ)
  -- Only for type inference.
  | TBot
  | TTop
  -- If we have two non-variable types, we can combine them.
  | TGlb TVar Typ
  | TLub TVar Typ
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

unreachable = error "unreachable"

debug on prefix x = if on then trace (prefix ++ ": " ++ show x) x else x


-- Expression Evaluation

eval :: Exp -> Reader Env Val
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

type EEnv = M.Map EVar Typ
type TEnv = M.Map TVar Typ

-- Order explicit throughout because subst and infer don't commute.
infer :: Exp -> State ([TVar], TEnv, EEnv) Typ
infer = (. debug True "infer") $ \ case
  EPrim _ -> pure TPrim
  EVar evar -> lookup evar <$> getEEnv
  EOp op expL expR -> do
    infer expL >>= ensureSubOf TPrim
    infer expR >>= ensureSubOf TPrim
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
    subst typF >>= ensureSubOf (TFun typX typY)
    subst typY
  ELet evar expX expY -> do
    typX <- freshTyp
    withEVar evar typX $ do
      infer expX >>= ensureSubOf typX
      infer expY
  EBranch expI expT expE -> do
    infer expI >>= ensureSubOf TPrim
    typT <- infer expT
    typE <- infer expE
    lub typE <$> subst typT
  ESum nm exp -> TSum . M.singleton nm <$> infer exp
  -- ECase expX expsF -> do
  --   typsF <- traverse infer expsF
  --   typX <- infer exp
  -- TODO: make new type variables, ensure things match up.
  EProd exps -> TProd <$> traverse infer exps
  EProj nm expX -> do
    typY <- freshTyp
    infer expX >>= ensureSubOf (TProd $ M.fromList [(nm, typY)])
    subst typY

latticeOp conThis conDual = curry $ \ case
  (TPrim, TPrim) -> TPrim
  (TVar tvar, typ) -> conThis tvar typ
  (typ, TVar tvar) -> conThis tvar typ
  (TFun typX1 typY1, TFun typX2 typY2) ->
    TFun (dual typX1 typX2) (this typY1 typY2)
  (TSum typs1, TSum typs2) ->
    TSum $ fmap (onBoth this) (union typs1 typs2)
  (TProd typs1, TProd typs2) ->
    TProd $ fmap (onBoth this) (intersect typs1 typs2)
  (typ1, typ2) -> error $ "can't unify " ++ show typ1 ++ " with " ++ show typ2
  where
    this = latticeOp conThis conDual
    dual = latticeOp conDual conThis

lub = latticeOp TLub TGlb
glb = latticeOp TGlb TLub

ensureSubOf = flip ensureSub

-- TODO: should this return the resulting subtype?
ensureSub :: Typ -> Typ -> State ([TVar], TEnv, EEnv) ()
ensureSub = curry . (. debug True "ensureSub") $ substs >=> \ case
  (TPrim, TPrim) -> pure ()
  (TVar tvar, typ) -> setTVar tvar typ *> pure ()
  (typ, TVar tvar) -> setTVar tvar typ *> pure ()
  (TFun typX1 typY1, TFun typX2 typY2) ->
    ensureSub typX2 typX1 *> ensureSub typY1 typY2
  (TSum typs1, TSum typs2) ->
    -- traverse_ ensureSubSum (union typs1 typs2)
    all id <$> traverse ensureSubSum (union typs1 typs2) >>= \ case
      False -> error $ "need " ++ show (TSum typs1) ++ " < " ++ show (TSum typs2)
      _ -> pure ()
  (TProd typs1, TProd typs2) ->
    -- traverse_ ensureSubProd (union typs1 typs2)
    all id <$> traverse ensureSubProd (union typs1 typs2) >>= \ case
      False -> error $ "need " ++ show (TProd typs1) ++ " < " ++ show (TProd typs2)
      _ -> pure ()
  where
    substs (typ1, typ2) = (,) <$> subst typ1 <*> subst typ2
    ensureSubSum = \ case
      Fst _ -> pure False
      Snd _ -> pure True
      Both typ1 typ2 -> ensureSub typ1 typ2 *> pure True
    ensureSubProd = \ case
      Fst _ -> pure True
      Snd _ -> pure False
      Both typ1 typ2 -> ensureSub typ1 typ2 *> pure True

data OneOrTwo a = Fst a | Snd a | Both a a

onBoth f = \ case
  Fst x -> x
  Snd y -> y
  Both x y -> f x y

union m1 m2 = M.unionWith both (fmap Fst m1) (fmap Snd m2)
  where both (Fst x) (Snd y) = Both x y

intersect = M.intersectionWith Both

traverseTVars f = \ case
  TPrim -> pure TPrim
  TVar tvar -> f tvar
  TFun typX typY -> TFun <$> t typX <*> t typY
  TSum typs -> TSum <$> traverse t typs
  TProd typs -> TProd <$> traverse t typs
  where t = traverseTVars f

subst = traverseTVars $ \ tvar ->
        fromMaybe (TVar tvar) . M.lookup tvar <$> getTEnv

withEVar evar typ action = do
  typqOld <- M.lookup evar <$> getEEnv
  modifyEEnv $ M.insert evar typ
  result <- action
  modifyEEnv (M.delete evar)
  case typqOld of
    Nothing -> pure ()
    Just typOld -> subst typOld >>= modifyEEnv . M.insert evar
  pure result

setTVar tvar typ =
  if tvar `isFreeTVarIn` typ
  then error $ "infinite type " ++ show (TVar tvar) ++ " = " ++ show typ
  else modifyTEnv (M.insert tvar typ) *> substEnvs *> pure typ

substEnvs = do
  eenv <- getEEnv
  eenvSubst <- traverse subst eenv
  modifyEEnv (const eenvSubst)
  tenv <- getTEnv
  tenvSubst <- traverse subst tenv
  modifyTEnv (const tenvSubst)

getEEnv = (\ (_, eenv, _) -> eenv) <$> get

getTEnv = (\ (_, _, tenv) -> tenv) <$> get

modifyEEnv f = modify (\ (tvars, eenv, tenv) -> (tvars, f eenv, tenv))

modifyTEnv f = modify (\ (tvars, eenv, tenv) -> (tvars, eenv, f tenv))

foldMapTVars f = execWriter .: traverseTVars $ \ tvar ->
                 tell (f tvar) *> pure unreachable

isFreeTVarIn tvar = getAny . foldMapTVars (Any . (== tvar))

freshTVar = do
  (tvar : tvars, _, _) <- get
  modify $ \ (_, eenv, tenv) -> (tvars, eenv, tenv)
  pure tvar

freshTyp = TVar <$> freshTVar

names = map (:[]) ['a'..'s'] ++ map (('t':) . show) [0..]

runInfer = flip evalState (names, M.empty, M.empty) . infer
