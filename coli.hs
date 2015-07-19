{-# LANGUAGE
  NoMonomorphismRestriction,
  LambdaCase,
  RecursiveDo,
  RankNTypes,
  ExplicitForAll #-}

module Coli where

import Useful
import UnionFind

import Prelude hiding (exp, lookup, all)
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.ST
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

data Constraint a = a :<: a deriving (Eq, Ord, Show)

-- Order explicit throughout because subst and infer don't commute.
infer :: Exp -> forall s. ReaderT (Env (Inf s)) (StateT [Var] (ST s)) (Inf s)
infer = (. debug "infer") $ \ case
  EPrim _ -> return IPrim
  EVar var -> lookup var <$> getEnv
  EOp op expL expR -> do
    infer expL >>= lift2 . ensure . (:<: IPrim)
    infer expR >>= lift2 . ensure . (:<: IPrim)
    return IPrim
  EFun var exp -> do
    typX <- unknown
    withVar var typX $ IFun typX <$> infer exp
  EApp expF expX -> do
    typX <- infer expX
    typY <- unknown
    infer expF >>= lift2 . ensure . (:<: IFun typX typY)
    return typY
  ELet var expX expY -> do
    typX <- unknown
    withVar var typX $ infer expX >>= lift2 . ensure . (:<: typX) >> infer expY
  EBranch expI expT expE -> do
    infer expI >>= lift2 . ensure . (:<: IPrim)
    typT <- infer expT
    typE <- infer expE
    typ <- unknown
    lift2 . ensure $ typT :<: typ
    lift2 . ensure $ typE :<: typ
    return typ
  ESum nm exp -> ISum . M.singleton nm <$> infer exp
  -- ECase expX expsF -> do
  --   typsF <- traverse infer expsF
  --   typX <- infer exp
  -- TODO: make new type variables, ensure things match up.
  EProd exps -> IProd <$> traverse infer exps
  EProj nm exp -> do
    typ <- unknown
    infer exp >>= lift2 . ensure . (:<: IProd (M.fromList [(nm, typ)]))
    return typ

lift2 = lift . lift

unknown = do
  (var : vars) <- lift get
  lift $ put vars
  lift2 $ IMyst <$> newUfr (MVar var)

ensure (typ1 :<: typ2) =
  ((:<:) <$> typOfInf typ1 <*> typOfInf typ2) >>=
  -- TODO: be less evil....
  (\ x -> debug "ensure" x `seq` ensure' (typ1 :<: typ2))

-- TODO: deal with structural subtyping.
ensure' = \ case
  IPrim :<: IPrim -> pure ()
  IFun typX1 typY1 :<: IFun typX2 typY2 ->
    ensure (typX2 :<: typX1) *> ensure (typY1 :<: typY2)
  ISum typs1 :<: ISum typs2 ->
    traverse_ ensureSum $ union typs1 typs2
  IProd typs1 :<: IProd typs2 ->
    traverse_ ensureProd $ union typs1 typs2
  IMyst mystr1 :<: IMyst mystr2 -> ensureMyst mystr1 mystr2
  IMyst mystr1 :<: typ2 -> do
    myst1 <- readUfr mystr1
    case myst1 of
      MVar _ -> writeUfr mystr1 $ MInf typ2
      MInf typ1 -> ensure $ typ1 :<: typ2
  typ1 :<: IMyst mystr2 -> do
    myst2 <- readUfr mystr2
    case myst2 of
      MVar _ -> writeUfr mystr2 $ MInf typ1
      MInf typ2 -> ensure $ typ1 :<: typ2
  where
    ensureSum = \case
      Fst _ -> error "ensureSum"
      Snd _ -> pure ()
      Both typ1 typ2 -> ensure $ typ1 :<: typ2
    ensureProd = \case
      Fst _ -> pure ()
      Snd _ -> error "ensureProd"
      Both typ1 typ2 -> ensure $ typ1 :<: typ2
    -- TODO
    ensureMyst = mergeUfr . curry $ \ case
      (MVar _, myst) -> pure myst
      (myst, MVar _) -> pure myst
      (MInf typ1, MInf typ2) -> ensure (typ1 :<: typ2) *> pure (MInf typ2)

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
