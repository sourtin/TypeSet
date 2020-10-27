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
, TotalArrayST(getTotalArrayST)
  -- don't export constructor to guarantee totality
, runTotalArray
, thawTotalArray
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
import Data.TypeMap.Internal

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

newtype TotalArrayST s k v = MkTotalArrayST { getTotalArrayST :: AS.STArray s Natural v }

runTotalArray :: Finite k => (forall s. ST s (TotalArrayST s k v)) -> TotalArray k v
runTotalArray st = MkTotalArray (AS.runSTArray $ fmap getTotalArrayST st)

thawTotalArray :: Finite k => TotalArray k v -> ST s (TotalArrayST s k v)
thawTotalArray = fmap MkTotalArrayST . AM.thaw . getTotalArray

instance (Eq k, Finite k) => MTypeMap (TotalArrayST s k) k (ST s) where
  lookup k m = Just <$> get m k
  assocs = fmap (zip enumerate) . AM.getElems . getTotalArrayST
  replace k v (MkTotalArrayST m) = AM.writeArray m (toNatural k) v
  replaceWith f k (MkTotalArrayST m) =
    let i = toNatural k in AM.readArray m i >>= AM.writeArray m i . f
  map f = fmap MkTotalArrayST . AM.mapArray f . getTotalArrayST

  mapWithKey f (MkTotalArrayST m) =
    do m' <- AM.getBounds m >>= AM.newArray_
       AM.getAssocs m >>= mapM (\(i, v) ->
          AM.writeArray m' i (f (fromNatural' i) v))
       return (MkTotalArrayST m')
  
  mapAccumWithKey f acc (MkTotalArrayST m) =
    do m' <- AM.getBounds m >>= AM.newArray_
       acc' <- AM.getAssocs m >>=
          flip foldM acc (\a (i, v) ->
            let (a', v') = f a (fromNatural' i) v
            in AM.writeArray m' i v' >> return a')
       return (acc', MkTotalArrayST m')
    where CardFin n = cardinality (Proxy :: Proxy k)
  
  mapAccumRWithKey f acc (MkTotalArrayST m) =
    do m' <- AM.getBounds m >>= AM.newArray_
       acc' <- reverse <$> AM.getAssocs m >>=
          flip foldM acc (\a (i, v) ->
            let (a', v') = f a (fromNatural' i) v
            in AM.writeArray m' i v' >> return a')
       return (acc', MkTotalArrayST m')
    where CardFin n = cardinality (Proxy :: Proxy k)

  mapAccumWithKeyBy ks f acc (MkTotalArrayST m) =
    do m' <- AM.getBounds m >>= AM.newArray_
       acc' <- foldM (go m') acc ks
       return (acc', MkTotalArrayST m')
    where
      CardFin n = cardinality (Proxy :: Proxy k)
      go m' a k = let i = toNatural k in
        f a k <$> AM.readArray m i >>=
          \(a', v') -> AM.writeArray m' i v' >> return a'


instance (Eq k, Finite k) => MTypeMapTotal (TotalArrayST s k) k (ST s) where
  build f = MkTotalArrayST <$> AM.newListArray (0, n-1) (Prelude.map f enumerate)
    where CardFin n = cardinality (Proxy :: Proxy k)
  get (MkTotalArrayST m) = AM.readArray m . toNatural
