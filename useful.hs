{-# LANGUAGE NoMonomorphismRestriction, LambdaCase #-}

module Useful where

import Data.Map as M
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)

infixr 9 .:
(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) = fmap . fmap

lookup key = fromMaybe (error $ "lookup: didn't find " ++ key) . M.lookup key

data OneOrTwo a = Fst a | Snd a | Both a a

onBoth f = \ case
  Fst x -> x
  Snd y -> y
  Both x y -> f x y

union m1 m2 = M.unionWith both (fmap Fst m1) (fmap Snd m2)
  where both (Fst x) (Snd y) = Both x y

intersect = M.intersectionWith Both

debug prefix x = if prefix /= "" then trace (prefix ++ ": " ++ show x) x else x
