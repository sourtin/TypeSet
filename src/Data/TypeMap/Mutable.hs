{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Data.TypeMap.Mutable
( MTypeMap(..)
, MTypeMapTotal(..)
, TotalArray(getTotalArray) -- don't export constructor to guarantee totality
) where

import Data.Proxy (Proxy(Proxy))
import Data.Maybe (catMaybes)
import Numeric.Natural (Natural)
import Data.Foldable (foldl')
import qualified Data.Array.ST as AS
import qualified Data.Array.MArray as AM
import Control.Monad.ST (ST)
import Data.TypeSet.Cardinality (Cardinal(CardFin))
import Data.TypeSet.Theory (cardinality, Countable(..), Finite)

class MTypeMap m k mo | m -> k where
  lookup :: k -> m v -> mo (Maybe v)
  assocs :: m v -> mo [(k, v)]
  replace :: k -> v -> m v -> mo (m v)
  replaceWith :: (v -> v) -> k -> m v -> mo (m v)
  map :: (a -> b) -> m a -> mo (m b)
  mapWithKey :: (k -> a -> b) -> m a -> mo (m b)
  mapAccum :: (a -> b -> (a, c)) -> a -> m b -> mo (a, m c)
  mapAccumWithKey :: (a -> k -> b -> (a, c)) -> a -> m b -> mo (a, m c)
  mapAccumRWithKey :: (a -> k -> b -> (a, c)) -> a -> m b -> mo (a, m c)
  mapAccumWithKeyBy :: [k] -> (a -> k -> b -> (a, c)) -> a -> m b -> mo (a, m c)

class MTypeMap m k mo => MTypeMapTotal m k mo | m -> k where
  build :: (k -> v) -> mo (m v)
  get :: m v -> k -> mo v

-- =

newtype TotalArray s k v = MkTotalArray { getTotalArray :: AS.STArray s Natural v }

instance Finite k => MTypeMap (TotalArray s k) k (ST s) where
  lookup k m = Just <$> get m k
  assocs (MkTotalArray m) = zip enumerate <$> AM.getElems m

instance Finite k => MTypeMapTotal (TotalArray s k) k (ST s) where
  build f = MkTotalArray <$> AM.newListArray (0, n-1) (Prelude.map f enumerate)
    where CardFin n = cardinality (Proxy :: Proxy k)
  get (MkTotalArray m) = AM.readArray m . toNatural
