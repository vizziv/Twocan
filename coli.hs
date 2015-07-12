{-# LANGUAGE NoMonomorphismRestriction, LambdaCase, RecursiveDo #-}

module Coli where

import Prelude hiding (exp, lookup, all)
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
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
  | TSub TVar Typ
  | TSuper TVar Typ
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
    subst typT >>= commonSuper typE
  ESum nm exp -> TSum . M.singleton nm <$> infer exp
  -- ECase expX expsF -> do
  --   TSum typsX <- infer exp
  --   typsF <- traverse infer expsF
  --   M.foldM typsY
  EProd exps -> TProd <$> traverse infer exps
  EProj nm expX -> do
    typY <- freshTyp
    infer expX >>= ensureSubOf (TProd $ M.fromList [(nm, typY)])
    subst typY
  exp -> error $ "can't infer " ++ show exp ++ " yet"

-- TODO: add sub/super cases.
commonSuper = curry $ \ case
  (TPrim, TPrim) -> pure TPrim
  (TVar tvar, typ) -> setTVar tvar typ
  (typ, TVar tvar) -> setTVar tvar typ
  (TFun typX1 typY1, TFun typX2 typY2) ->
    TFun <$> commonSuper typX1 typX2 <*> commonSuper typY1 typY2
  (TSum typs1, TSum typs2) ->
    TSum <$> traverse commonSuper' (union typs1 typs2)
  (TProd typs1, TProd typs2) ->
    TProd <$> traverse commonSuper' (intersect typs1 typs2)
  (typ1, typ2) -> error $ "can't unify " ++ show typ1 ++ " with " ++ show typ2
  where
    commonSuper' = \ case
      Fst typ -> pure typ
      Snd typ -> pure typ
      Both typ1 typ2 -> commonSuper typ1 typ2

ensureSubOf = flip ensureSub

-- TODO: should this return the resulting subtype?
ensureSub :: Typ -> Typ -> State ([TVar], TEnv, EEnv) ()
ensureSub = curry . (. debug True "ensureSub") $ substs >=> \ case
  (TPrim, TPrim) -> pure ()
  -- TODO: these two cases are (probably?) wrong!
  (TSub _ typ1, typ2) -> ensureSub typ1 typ2
  (typ1, TSuper _ typ2) -> ensureSub typ1 typ2
  (TVar tvar, typ) -> setTVar tvar (mkTSub tvar typ) *> pure ()
  (typ, TVar tvar) -> setTVar tvar (mkTSuper tvar typ) *> pure ()
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
  (typ1, TSub _ typ2) -> case typ2 of
    -- TODO: make this first case unnecessary.
    TSub _ _ -> ensureSub typ1 typ2
    TVar _ -> ensureSub typ1 typ2
    _ -> error $ "can't ensure " ++ show typ1 ++ " < " ++ show typ2
  (TSuper _ typ1, typ2) -> case typ1 of
    -- TODO: make this first case unnecessary.
    TSuper _ _ -> ensureSub typ1 typ2
    TVar _ -> ensureSub typ1 typ2
    _ -> error $ "can't ensure " ++ show typ1 ++ " < " ++ show typ2
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

data OneOrTwo a b = Fst a | Snd b | Both a b

union m1 m2 = M.unionWith both (fmap Fst m1) (fmap Snd m2)
  where both (Fst x) (Snd y) = Both x y

intersect = M.intersectionWith Both

mkTSub tvar = \ case
  TPrim -> TPrim
  typ@(TVar tvarSub) -> if tvar == tvarSub then typ else TSub tvar typ
  typ@(TSub _ _) -> typ
  typ -> TSub tvar typ

mkTSuper tvar = \ case
  TPrim -> TPrim
  typ@(TVar tvarOther) -> if tvar == tvarOther then typ else TSuper tvar typ
  typ@(TSuper _ _) -> typ
  typ -> TSuper tvar typ

traverseTVars fTVar fTSub fTSuper = \ case
  TPrim -> pure TPrim
  TVar tvar -> fTVar tvar
  TFun typX typY -> TFun <$> t typX <*> t typY
  TSum typs -> TSum <$> traverse t typs
  TProd typs -> TProd <$> traverse t typs
  TSub tvar typ -> t typ >>= fTSub tvar
  TSuper tvar typ -> t typ >>= fTSuper tvar
  where t = traverseTVars fTVar fTSub fTSuper

subst = traverseTVars fTVar fTSub fTSuper
  where
    fTVar tvar = fromMaybe (TVar tvar) . M.lookup tvar <$> getTEnv
    fTSub tvar typ = do
      typq <- M.lookup tvar <$> getTEnv
      case typq of
        Nothing -> pure $ TSub tvar typ
        Just typSub -> ensureSub typSub typ *> subst typSub
    fTSuper = undefined

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

foldMapTVars f = execWriter . traverseTVars g (const . g) (const . g)
  where g tvar = tell (f tvar) *> pure unreachable

isFreeTVarIn tvar = getAny . foldMapTVars (Any . (== tvar))

freshTVar = do
  (tvar : tvars, _, _) <- get
  modify $ \ (_, eenv, tenv) -> (tvars, eenv, tenv)
  pure tvar

freshTyp = TVar <$> freshTVar

names = map (:[]) ['a'..'s'] ++ map (('t':) . show) [0..]

runInfer = flip evalState (names, M.empty, M.empty) . infer
