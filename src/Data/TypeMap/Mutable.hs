{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}

module Data.TypeMap.Mutable
( MTypeMap(..)
, MTypeMapTotal(..)
, TotalArray(getTotalArray) -- don't export constructor to guarantee totality
, runTotalArray
) where

import Data.Proxy (Proxy(Proxy))
import Data.Maybe (catMaybes)
import Numeric.Natural (Natural)
import Data.Foldable (foldl')
import qualified Data.Array as A
import qualified Data.Array.ST as AS
import qualified Data.Array.MArray as AM
import Control.Monad (void, foldM)
import Control.Monad.ST (ST, runST)
import GHC.Arr (unsafeFreezeSTArray)
import Data.TypeSet.Cardinality (Cardinal(CardFin))
import Data.TypeSet.Theory (cardinality, Countable(..), Finite)
import Data.TypeMap ()

class (Eq k, Countable k, Monad mo) => MTypeMap m k mo | m -> k where
  lookup :: k -> m v -> mo (Maybe v)
  assocs :: m v -> mo [(k, v)]
  replace :: k -> v -> m v -> mo ()
  replaceWith :: (v -> v) -> k -> m v -> mo ()
  map :: (a -> b) -> m a -> mo (m b)
  mapWithKey :: (k -> a -> b) -> m a -> mo (m b)
  mapAccum :: (a -> b -> (a, c)) -> a -> m b -> mo (a, m c)
  mapAccumWithKey :: (a -> k -> b -> (a, c)) -> a -> m b -> mo (a, m c)
  mapAccumRWithKey :: (a -> k -> b -> (a, c)) -> a -> m b -> mo (a, m c)
  mapAccumWithKeyBy :: [k] -> (a -> k -> b -> (a, c)) -> a -> m b -> mo (a, m c)

  assocs m = catMaybes <$> mapM go enumerate
    where go k = fmap (k,) <$> Data.TypeMap.Mutable.lookup k m
  replace k = flip replaceWith k . const
  replaceWith f k = void . mapWithKey (\k' v -> if k == k' then f v else v)
  map = mapWithKey . const
  mapWithKey f = fmap snd . mapAccumWithKey (\() k b -> ((), f k b)) ()
  mapAccum = mapAccumWithKey . flip . const
  mapAccumWithKey = mapAccumWithKeyBy enumerate
  mapAccumRWithKey = mapAccumWithKeyBy (reverse enumerate)

  {-# MINIMAL lookup, mapAccumWithKeyBy #-}

class (Finite k, MTypeMap m k mo) => MTypeMapTotal m k mo | m -> k where
  build :: (k -> v) -> mo (m v)
  get :: m v -> k -> mo v

  get m k = (\(Just x) -> x) <$> Data.TypeMap.Mutable.lookup k m

  {-# MINIMAL build #-}

-- =

newtype TotalArray s k v = MkTotalArray { getTotalArray :: AS.STArray s Natural v }

runTotalArray :: (Finite k, AM.Ix k) => (forall s. ST s (TotalArray s k v)) -> A.Array k v
runTotalArray st = AS.runSTArray $ do
  MkTotalArray m <- st
  (a, b) <- AM.getBounds m
  AM.mapIndices (fromNatural' a, fromNatural' b) toNatural m


instance (Eq k, Finite k) => MTypeMap (TotalArray s k) k (ST s) where
  lookup k m = Just <$> get m k
  assocs = fmap (zip enumerate) . AM.getElems . getTotalArray
  replace k v (MkTotalArray m) = AM.writeArray m (toNatural k) v
  replaceWith f k (MkTotalArray m) =
    let i = toNatural k in AM.readArray m i >>= AM.writeArray m i
  map f = fmap MkTotalArray . AM.mapArray f . getTotalArray

  mapWithKey f (MkTotalArray m) =
    do m' <- AM.getBounds m >>= AM.newArray_
       AM.getAssocs m >>= mapM (\(i, v) ->
          AM.writeArray m' i (f (fromNatural' i) v))
       return (MkTotalArray m')
  
  mapAccumWithKey f acc (MkTotalArray m) =
    do m' <- AM.getBounds m >>= AM.newArray_
       acc' <- AM.getAssocs m >>=
          flip foldM acc (\a (i, v) ->
            let (a', v') = f a (fromNatural' i) v
            in AM.writeArray m' i v' >> return a')
       return (acc', MkTotalArray m')
    where CardFin n = cardinality (Proxy :: Proxy k)
  
  mapAccumRWithKey f acc (MkTotalArray m) =
    do m' <- AM.getBounds m >>= AM.newArray_
       acc' <- reverse <$> AM.getAssocs m >>=
          flip foldM acc (\a (i, v) ->
            let (a', v') = f a (fromNatural' i) v
            in AM.writeArray m' i v' >> return a')
       return (acc', MkTotalArray m')
    where CardFin n = cardinality (Proxy :: Proxy k)

  mapAccumWithKeyBy ks f acc (MkTotalArray m) =
    do m' <- AM.getBounds m >>= AM.newArray_
       acc' <- foldM (go m') acc ks
       return (acc', MkTotalArray m')
    where
      CardFin n = cardinality (Proxy :: Proxy k)
      go m' a k = let i = toNatural k in
        f a k <$> AM.readArray m i >>=
          \(a', v') -> AM.writeArray m' i v' >> return a'


instance (Eq k, Finite k) => MTypeMapTotal (TotalArray s k) k (ST s) where
  build f = MkTotalArray <$> AM.newListArray (0, n-1) (Prelude.map f enumerate)
    where CardFin n = cardinality (Proxy :: Proxy k)
  get (MkTotalArray m) = AM.readArray m . toNatural
