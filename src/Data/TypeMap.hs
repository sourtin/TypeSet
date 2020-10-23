{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.TypeMap where

import Numeric.Natural (Natural)
import Data.TypeSet.Theory (Countable)

infixl 9 !
(!) :: TypeMapTotal m k => k -> m v -> v
(!) = get

infixl 9 !?
(!?) :: TypeMapPartial m k => k -> m v -> Maybe v
(!?) = Data.TypeMap.lookup

class Countable k => TypeMap m k | m -> k where
  assocs :: m v -> [(k, v)]
  replace :: k -> v -> m v -> m v
  replaceWith :: (v -> v) -> k -> m v -> m v
  map :: (a -> b) -> (m a -> m b)
  mapWithKey :: (k -> a -> b) -> (m a -> m b)
  mapAccum :: (a -> b -> (a, c)) -> a -> (m b -> (a, m c))
  mapAccumWithKey :: (a -> k -> b -> (a, c)) -> a -> (m b -> (a, m c))

class TypeMap m k => TypeMapTotal m k | m -> k where
  build :: (k -> v) -> m v
  get :: k -> m v -> v

class TypeMap m k => TypeMapPartial m k | m -> k where
  empty :: m v
  singleton :: k -> v -> m v
  fromAssocs :: [(k, v)] -> m v
  fromAssocsWith :: (v -> v -> v) -> [(k, v)] -> m v
  fromAssocsWithKey :: (k -> v -> v -> v) -> [(k, v)] -> m v
  insert :: k -> v -> m v -> m v
  insertWith :: (v -> v -> v) -> k -> v -> m v -> m v
  insertWithKey :: (k -> v -> v -> v) -> k -> v -> m v -> m v
  insertLookupWithKey :: (k -> v -> v -> v) -> k -> v -> m v -> (Maybe v, m v)
  delete :: k -> m v -> m v
  adjust :: (v -> v) -> k -> m v -> m v
  update :: (v -> Maybe v) -> k -> m v -> m v
  updateLookup :: (v -> Maybe v) -> k -> m v -> (Maybe v, m v)
  alter :: (Maybe v -> Maybe v) -> k -> m v -> m v
  lookup :: k -> m v -> Maybe v
  findWithDefault :: v -> k -> m v -> v
  member :: k -> m v -> Bool
  null :: m v -> Bool
  size :: m v -> Natural
  union :: m v -> m v -> m v
  unionWithKey :: (k -> v -> v -> v) -> (m v -> m v -> m v)
  unions :: [m v] -> m v
  unionsWithKey :: (k -> v -> v -> v) -> ([m v] -> m v)