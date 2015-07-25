{-# LANGUAGE
  NoMonomorphismRestriction,
  LambdaCase,
  RankNTypes #-}

module UnionFind
  (Ufr, newUfr, readUfr, writeUfr, modifyUfr, mergeUfr, equalUfr)
  where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Control.Monad.ST.Class
import Data.STRef

import Useful

data Path s a = PEnd Int a | PStep (STRef s (Path s a))

-- Union-Find Reference
newtype Ufr s a = Ufr {fromUfr :: STRef s (Path s a)}

-- The pathr returned always refers to a PEnd.
lastPathr pathr = readSTRef pathr >>= \ case
  PEnd _ x -> return pathr
  PStep pathrNext -> do
    pathrLast <- lastPathr pathrNext
    writeSTRef pathr (PStep pathrLast)
    return pathrLast

readPathr = lastPathr >=> readSTRef >=> \ case
  PEnd _ x -> return x
  _ -> error "readPathr: lastPathr didn't return a PEnd"

modifyPathr pathr f = do
  pathrLast <- lastPathr pathr
  modifySTRef pathrLast $ \ case
    PEnd rank x -> PEnd rank (f x)
    _ -> error "modifyPathr: lastPathr didn't return a PEnd"

newUfr x = liftST $ Ufr <$> newSTRef (PEnd 0 x)
readUfr = liftST . readPathr . fromUfr
modifyUfr = liftST .: modifyPathr . fromUfr
writeUfr ufr = modifyUfr ufr . const

mergeUfr op (Ufr pathrFirst1) (Ufr pathrFirst2) = liftST $ do
  pathr1 <- lastPathr pathrFirst1
  pathr2 <- lastPathr pathrFirst2
  if pathr1 == pathr2
  then return ()
  else do
    PEnd rank1 x1 <- readSTRef pathr1
    PEnd rank2 x2 <- readSTRef pathr2
    let (pathrParent, pathrChild, rank) = case compare rank1 rank2 of
                                            LT -> (pathr2, pathr1, rank2)
                                            EQ -> (pathr1, pathr2, rank1 + 1)
                                            GT -> (pathr1, pathr2, rank1)
    let x = op x1 x2
    writeSTRef pathrChild (PStep pathrParent)
    writeSTRef pathrParent (PEnd rank x)

equalUfr (Ufr pathr1) (Ufr pathr2) =
  liftST $ (==) <$> lastPathr pathr1 <*> lastPathr pathr2

unionFindTest = runST $ do
                  a <- newUfr "a"
                  b <- newUfr "b"
                  c <- newUfr "c"
                  d <- newUfr "d"
                  e <- newUfr "e"
                  f <- newUfr "f"
                  g <- newUfr "g"
                  merge b c
                  merge a g
                  merge e f
                  merge e b
                  (,,,) <$> mapM readUfr [a,b,c,d,e,f,g]
                        <*> equalUfr a b
                        <*> equalUfr c e
                        <*> equalUfr f b
  where merge = mergeUfr (++)
