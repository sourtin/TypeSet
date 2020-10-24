{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module Data.TypeMap where

import Data.Maybe (catMaybes)
import Numeric.Natural (Natural)
import Data.TypeSet.Theory (Countable(..), Finite)
import Data.Foldable (foldl')
import qualified Data.Map.Strict as MS

infixl 9 !
(!) :: TypeMapTotal m k => k -> m v -> v
(!) = get

infixl 9 !?
(!?) :: TypeMapPartial m k => k -> m v -> Maybe v
(!?) = Data.TypeMap.lookup

class (Eq k, Finite k) => TypeMap m k | m -> k where
  lookup :: k -> m v -> Maybe v
  assocs :: m v -> [(k, v)]
  replace :: k -> v -> m v -> m v
  replaceWith :: (v -> v) -> k -> m v -> m v
  map :: (a -> b) -> (m a -> m b)
  mapWithKey :: (k -> a -> b) -> (m a -> m b)
  mapAccum :: (a -> b -> (a, c)) -> a -> (m b -> (a, m c))
  mapAccumWithKey :: (a -> k -> b -> (a, c)) -> a -> (m b -> (a, m c))
  mapAccumRWithKey :: (a -> k -> b -> (a, c)) -> a -> (m b -> (a, m c))
  -- | precondition for TypeMapTotal instances (not checked):
  --   [k] is a permutation of enumerate
  mapAccumWithKeyBy :: [k] -> (a -> k -> b -> (a, c)) -> a -> (m b -> (a, m c))

  assocs = catMaybes . flip Prelude.map enumerate . go
    where go m k = (k,) <$> Data.TypeMap.lookup k m
  replace k = flip replaceWith k . const
  replaceWith f k = Data.TypeMap.mapWithKey (\k' v -> if k == k' then f v else v)
  map = mapWithKey . const
  mapWithKey = (snd .) . flip mapAccumWithKey () . const . ((((),) .) .)
  mapAccum = mapAccumWithKey . flip . const
  mapAccumWithKey = mapAccumWithKeyBy enumerate
  mapAccumRWithKey = mapAccumWithKeyBy (reverse enumerate)

  {-# MINIMAL lookup, mapAccumWithKeyBy #-}

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
  findWithDefault :: v -> k -> m v -> v
  member :: k -> m v -> Bool
  null :: m v -> Bool
  size :: m v -> Natural
  union :: m v -> m v -> m v
  unionWithKey :: (k -> v -> v -> v) -> (m v -> m v -> m v)
  unions :: [m v] -> m v
  unionsWithKey :: (k -> v -> v -> v) -> ([m v] -> m v)

  singleton k v = fromAssocs [(k, v)]
  fromAssocs = fromAssocsWith const
  fromAssocsWith = fromAssocsWithKey . const
  fromAssocsWithKey f = foldl' (\m (k,v) -> insertWithKey f k v m) empty
  insert = insertWith const
  insertWith f k v = alter (pure . maybe v (f v)) k
  insertWithKey f k = insertWith (f k) k
  insertLookupWithKey f k v m = (Data.TypeMap.lookup k m, insertWithKey f k v m)
  delete = update (const Nothing)
  adjust = update . (pure .)
  update = alter . (=<<)
  updateLookup f k m = (Data.TypeMap.lookup k m, update f k m)
  findWithDefault v = (maybe v id .) . Data.TypeMap.lookup
  member = (maybe False (const True) .) . Data.TypeMap.lookup
  null = (==0) . length . assocs
  size = fromIntegral . length . assocs
  union = unionWithKey (const const)
  unionWithKey f m = foldl' (\m (k,v) -> insertWithKey f k v m) m . assocs
  unions = unionsWithKey (const const)
  unionsWithKey = flip foldl' empty . unionWithKey

  {-# MINIMAL empty, alter #-}

class TypeMapMutable where
class TypeMapTotalMutable where


-- =

instance (Eq k, Finite k) => TypeMap ((->) k) k where
  lookup k m = Just (m k)
  assocs m = Prelude.map (\k -> (k, m k)) enumerate
  replace k v m = \k' -> if k == k' then v else m k'
  replaceWith f k m = \k' -> let v = m k' in if k == k' then f v else v
  map = (.)
  mapWithKey f m = \k -> f k (m k)
  mapAccumWithKeyBy ks f = go ks (MS.empty)
    where go [] m' acc m = (acc, (m' MS.!) . toNatural)
          go (k:ks) m' acc m =
            let (acc', v) = f acc k (m k)
            in go ks (MS.insert (toNatural k) v m') acc' m

instance (Eq k, Finite k) => TypeMapTotal ((->) k) k where
  build = id
  get = flip ($)

newtype FnPartial k v = FnPartial { getFn :: k -> Maybe v }

instance (Eq k, Finite k) => TypeMap (FnPartial k) k where
  lookup = flip getFn
  map f m = FnPartial (fmap f . getFn m)
  mapWithKey f m = FnPartial (\k -> f k <$> getFn m k)
  mapAccumWithKeyBy ks f = go ks (MS.empty)
    where go [] m' acc m = (acc, FnPartial ((m' MS.!?) . toNatural))
          go (k:ks) m' acc m =
            case getFn m k of
              Nothing -> go ks m' acc m
              Just v ->
                let (acc', v') = f acc k v
                in go ks (MS.insert (toNatural k) v' m') acc' m

instance (Eq k, Finite k) => TypeMapPartial (FnPartial k) k where
  empty = FnPartial (const Nothing)
  alter f k (FnPartial m) = FnPartial (\k' -> if k == k' then f (m k) else m k)