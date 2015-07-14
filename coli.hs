{-# LANGUAGE NoMonomorphismRestriction, LambdaCase, RecursiveDo #-}

module Coli where

import Prelude hiding (exp, lookup, all)
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Foldable
import Data.Maybe (fromMaybe)
import Data.Traversable
import Data.Tuple
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

unreachable = error "unreachable"

debug on prefix x = if on then trace (prefix ++ ": " ++ show x) x else x


-- Expression Evaluation

eval :: Exp -> Reader Env Val
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

data Bound = BExact Typ | BBetween Typ Typ deriving (Eq, Ord, Show)

type EEnv = M.Map EVar Typ
type TEnv = M.Map TVar Bound

-- Order explicit throughout because subst and infer don't commute.
infer :: Exp -> State ([TVar], EEnv, TEnv) Typ
infer = (. debug True "infer") $ \ case
  EPrim _ -> pure TPrim
  EVar evar -> lookup evar <$> getEEnv
  EOp op expL expR -> do
    infer expL >>= ensureSubOf TPrim
    infer expR >>= ensureSubOf TPrim
    pure TPrim
  EFun evar exp -> do
    typX <- freshTyp
    withEVar evar $ \ typX -> TFun typX <$> infer exp
  EApp expF expX -> do
    typF <- infer expF
    typX <- infer expX
    typY <- freshTyp
    subst typF >>= ensureSubOf (TFun typX typY)
    subst typY
  ELet evar expX expY ->
    withEVar evar $ \ typX -> infer expX >>= ensureSubOf typX >> infer expY
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

lattice con bound setOp = curry $ \ case
  (typ, _) | typ == this bound -> this bound
  (_, typ) | typ == this bound -> this bound
  (typ1, typ2) | typ1 == dual bound -> typ2
  (typ1, typ2) | typ2 == dual bound -> typ1
  (TPrim, TPrim) -> TPrim
  (TVar tvar, typ) -> this con tvar typ
  (typ, TVar tvar) -> this con tvar typ
  (TFun typX1 typY1, TFun typX2 typY2) ->
    TFun (dual latticeOp typX1 typX2) (this latticeOp typY1 typY2)
  (TSum typs1, TSum typs2) ->
    TSum $ fmap (onBoth $ this latticeOp) (this setOp typs1 typs2)
  (TProd typs1, TProd typs2) ->
    TProd $ fmap (onBoth $ this latticeOp) (dual setOp typs1 typs2)
  (typ1, typ2) -> error $ "can't unify " ++ show typ1 ++ " with " ++ show typ2
  where
    this = fst
    dual = snd
    latticeOp = (lattice con bound setOp,
                 lattice (swap con) (swap bound) (swap setOp))

glb = lattice (TGlb, TLub) (TBot, TTop) (intersect, union)
lub = lattice (TLub, TGlb) (TTop, TBot) (union, intersect)

data Cmp = Eq | Lt | Gt | Nc deriving (Eq, Ord, Show)

cmp typ1 typ2 | typ1 == typ2 = Eq
              | typGlb == typ1 = Lt
              | typGlb == typ2 = Gt
              | otherwise = Nc
  where typGlb = glb typ1 typ2

le = (.: cmp) $ \ case
  Gt -> False
  _ -> True

mergeBound = curry $ \ case
  (BExact typ1, BExact typ2) ->
    if typ1 == typ2
    then BExact typ1
    else error $ "need " ++ show typ1 ++ " = " ++ show typ2
  (BExact typ1, BBetween typL2 typU2) ->
    if typL2 `le` typ1 && typ1 `le` typU2
    then BExact typ1
    else error $ "need " ++ show typL2 ++ " < "
           ++ show typ1 ++ " < " ++ show typU2
  (bound1@(BBetween _ _), bound2@(BExact _)) -> mergeBound bound2 bound1
  (BBetween typL1 typU1, BBetween typL2 typU2) ->
    mkBound (lub typL1 typL2) (glb typU1 typU2)

mkBound typL typU = case typL `cmp` typU of
                      Lt -> if cantSuper typL then BExact typL
                            else if cantSub typU then BExact typU
                            else BBetween typL typU
                      Eq -> BExact typL
                      _ -> error $ "need " ++ show typL ++ " < " ++ show typU

cantSub = \ case
  TPrim -> True
  TFun typX typY -> cantSuper typX && cantSub typY
  TSum typs -> M.null typs
  TBot -> True
  _ -> False

cantSuper = \ case
  TPrim -> True
  TFun typX typY -> cantSub typX && cantSuper typY
  TProd typs -> M.null typs
  TTop -> True
  _ -> False

ensureSubOf = flip ensureSub

-- TODO: should this return the resulting subtype?
ensureSub :: Typ -> Typ -> State ([TVar], EEnv, TEnv) ()
ensureSub = curry . (. debug True "ensureSub") $ substs >=> \ case
  (TPrim, TPrim) -> pure ()
  (TVar tvar, typ) -> boundTVar tvar $ mkBound TBot typ
  (typ, TVar tvar) -> boundTVar tvar $ mkBound typ TTop
  (TFun typX1 typY1, TFun typX2 typY2) ->
    ensureSub typX2 typX1 *> ensureSub typY1 typY2
  (TSum typs1, TSum typs2) ->
    -- traverse_ ensureSubSum (union typs1 typs2)
    all id <$> traverse ensureSubSum (union typs1 typs2) >>= \ case
      False -> error $ "don't have " ++ show (TSum typs1) ++ " < " ++ show (TSum typs2)
      _ -> pure ()
  (TProd typs1, TProd typs2) ->
    -- traverse_ ensureSubProd (union typs1 typs2)
    all id <$> traverse ensureSubProd (union typs1 typs2) >>= \ case
      False -> error $ "don't have " ++ show (TProd typs1) ++ " < " ++ show (TProd typs2)
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
  TTop -> pure TTop
  TBot -> pure TBot
  TGlb tvar typ -> glb <$> f tvar <*> t typ
  TLub tvar typ -> lub <$> f tvar <*> t typ
  where t = traverseTVars f

subst = traverseTVars $ \ tvar -> do
          boundq <- M.lookup tvar <$> getTEnv
          pure $ case boundq of
                   Just (BExact typ) -> typ
                   _ -> TVar tvar

traverseBound f = \ case
  BExact typ -> BExact <$> f typ
  BBetween typL typU -> mkBound <$> f typL <*> f typU

withEVar evar action = do
  typNew <- freshTyp
  typqOld <- M.lookup evar <$> getEEnv
  modifyEEnv $ M.insert evar typNew
  result <- action typNew
  modifyEEnv (M.delete evar)
  case typqOld of
    Nothing -> pure ()
    Just typOld -> subst typOld >>= modifyEEnv . M.insert evar
  pure result

boundTVar tvar bound =
  if tvar `isFreeTVarIn` bound
  then error $ "infinite type " ++ show (TVar tvar) ++ " = " ++ show bound
  else modifyTEnv (M.insertWith mergeBound tvar bound) *> substEnvs

substEnvs = do
  eenv <- getEEnv
  eenvSubst <- traverse subst eenv
  modifyEEnv (const eenvSubst)
  tenv <- getTEnv
  tenvSubst <- traverse (traverseBound subst) tenv
  modifyTEnv (const tenvSubst)

getEEnv = (\ (_, eenv, _) -> eenv) <$> get

getTEnv = (\ (_, _, tenv) -> tenv) <$> get

modifyEEnv f = modify $ \ (tvars, eenv, tenv) ->
               (tvars, debug True "eenv" $ f eenv, tenv)

modifyTEnv f = modify $ \ (tvars, eenv, tenv) ->
               (tvars, eenv, debug True "tenv" $ f tenv)

foldMapTVars f =
  execWriter .: traverseTVars $ \ tvar -> tell (f tvar) *> pure unreachable

isFreeTVarIn tvar = \ case
  BExact typ -> isFreeIn typ
  BBetween typL typU -> isFreeIn typL || isFreeIn typU
  where isFreeIn = getAny . foldMapTVars (Any . (== tvar))

freshTyp = do
  (tvar : tvars, _, _) <- get
  modify $ \ (_, eenv, tenv) -> (tvars, eenv, tenv)
  pure $ TVar tvar

names = map (:[]) ['a'..'s'] ++ map (('t':) . show) [0..]

runInfer = flip evalState (names, M.empty, M.empty) . (subst <=< infer)
