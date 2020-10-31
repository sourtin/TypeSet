{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module Data.TypeMap
( TypeMap(..)
, TypeMapTotal(..)
, TypeMapPartial(..)
, (!), (!?)
, FnPartial(..)
, MkPartial(..)
, TotalArray(getTotalArray)
) where

import Data.Proxy (Proxy(Proxy))
import Data.Maybe (catMaybes)
import Numeric.Natural (Natural)
import Data.Foldable (foldl')
import Control.Monad (foldM)
import Control.Monad.ST (ST, runST)
import qualified Data.Array as A
import qualified Data.Array.MArray as AM
import qualified Data.Array.ST as AS
import Data.Array.Unsafe (unsafeFreeze)
import qualified Data.Map.Strict as MS
import Data.TypeSet.Cardinality (Cardinal(CardFin))
import Data.TypeSet.Theory (cardinality, Countable(..), Finite)
import Data.TypeMap.Internal

infixl 9 !
(!) :: TypeMapTotal m k => m v -> k -> v
(!) = flip get

infixl 9 !?
(!?) :: TypeMapPartial m k => m v -> k -> Maybe v
(!?) = flip Data.TypeMap.lookup

class (Eq k, Countable k) => TypeMap m k | m -> k where
  lookup :: k -> m v -> Maybe v
  assocs :: m v -> [(k, v)]
  replace :: k -> v -> m v -> m v
  replaceWith :: (v -> v) -> k -> m v -> m v
  map :: (a -> b) -> (m a -> m b)
  mapWithKey :: (k -> a -> b) -> (m a -> m b)
  mapAccum :: (a -> b -> (a, c)) -> a -> (m b -> (a, m c))
  mapAccumWithKey :: (a -> k -> b -> (a, c)) -> a -> (m b -> (a, m c))
  mapAccumRWithKey :: (a -> k -> b -> (a, c)) -> a -> (m b -> (a, m c))
  mapAccumWithKeyBy :: [k] -> (a -> k -> b -> (a, c)) -> a -> (m b -> (a, m c))
  foldr :: (b -> a -> a) -> a -> (m b -> a)
  foldl :: (a -> b -> a) -> a -> (m b -> a)
  foldrWithKey :: (k -> b -> a -> a) -> a -> (m b -> a)
  foldlWithKey :: (a -> k -> b -> a) -> a -> (m b -> a)
  foldWithKeyBy :: [k] -> (k -> b -> a -> a) -> a -> (m b -> a)

  assocs = catMaybes . flip Prelude.map enumerate . go
    where go m k = (k,) <$> Data.TypeMap.lookup k m
  replace k = flip replaceWith k . const
  replaceWith f k = mapWithKey (\k' v -> if k == k' then f v else v)
  map = mapWithKey . const
  mapWithKey f = snd . mapAccumWithKey (\() k b -> ((), f k b)) ()
  mapAccum = mapAccumWithKey . flip . const
  mapAccumWithKey = mapAccumWithKeyBy enumerate
  mapAccumRWithKey = mapAccumWithKeyBy (reverse enumerate)
  foldr = foldrWithKey . const
  foldl = foldlWithKey . (const .)
  foldrWithKey = foldWithKeyBy enumerate
  foldlWithKey f = foldWithKeyBy (reverse enumerate) (\k b a -> f a k b)
  foldWithKeyBy ks f a = fst . mapAccumWithKeyBy ks (\a k b -> (f k b a, b)) a

  {-# MINIMAL lookup, mapAccumWithKeyBy #-}

class (Finite k, TypeMap m k) => TypeMapTotal m k | m -> k where
  build :: (k -> v) -> m v
  get :: k -> m v -> v

  get k = (\(Just x) -> x) . Data.TypeMap.lookup k

  {-# MINIMAL build #-}

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

-- total function

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

-- partial function from total function

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

-- partial generic from total generic

newtype MkPartial m k v = MkPartial { getPartial :: m k (Maybe v) }
pmap :: (m k (Maybe u) -> m k (Maybe v)) -> (MkPartial m k u -> MkPartial m k v)
pmap f = MkPartial . f . getPartial

instance TypeMapTotal (m k) k => TypeMap (MkPartial m k) k where
  lookup k = get k . getPartial
  assocs = catMaybes . Prelude.map (\(k,v) -> fmap (k,) v) . assocs . getPartial
  replace k = pmap . replace k . Just
  replaceWith = (pmap .) . replaceWith . fmap
  map = pmap . Data.TypeMap.map . fmap
  mapWithKey f = pmap $ mapWithKey (fmap . f)
  mapAccumWithKey f acc = fmap MkPartial . mapAccumWithKey f' acc . getPartial
    where f' a k = maybe (a, Nothing) (fmap Just . f a k)
  mapAccumRWithKey f acc = fmap MkPartial . mapAccumRWithKey f' acc . getPartial
    where f' a k = maybe (a, Nothing) (fmap Just . f a k)
  mapAccumWithKeyBy ks f acc = fmap MkPartial . mapAccumWithKeyBy ks f' acc . getPartial
    where f' a k = maybe (a, Nothing) (fmap Just . f a k)

instance TypeMapTotal (m k) k => TypeMapPartial (MkPartial m k) k where
  empty = MkPartial $ build (const Nothing)
  singleton k v = MkPartial $ build (\k' -> if k == k' then Just v else Nothing)
  insert k = pmap . replace k . Just
  insertWith f k v = pmap (replaceWith (Just . maybe v (f v)) k)
  insertLookupWithKey f k v = fmap MkPartial . mapAccumWithKeyBy [k] f' Nothing . getPartial
    where f' _ k Nothing = (Nothing, Just v)
          f' _ k v' = (v', fmap (f k v) v')
  delete k = pmap (replace k Nothing)
  adjust f = pmap . replaceWith (fmap f)
  update f = pmap . replaceWith (>>= f)
  updateLookup f k = fmap MkPartial . mapAccumWithKeyBy [k] f' Nothing . getPartial
    where f' _ _ v = (v, v >>= f)
  alter f = pmap . replaceWith f
  findWithDefault v k = maybe v id . get k . getPartial
  member k = maybe False (const True) . get k . getPartial

-- binary tree map

instance (Ord k, Finite k) => TypeMap (MS.Map k) k where
  lookup = MS.lookup
  assocs = MS.toList
  replace = MS.insert
  replaceWith = MS.update . (Just .)
  map = MS.map
  mapWithKey = MS.mapWithKey
  mapAccum = MS.mapAccum
  mapAccumWithKey = MS.mapAccumWithKey
  mapAccumRWithKey = MS.mapAccumRWithKey
  mapAccumWithKeyBy ks f z m = foldl' f' (z, empty) ks
    where f' (z, m') k = maybe (z, m') (fmap (flip (replace k) m') . f z k) (m !? k)
  foldr = MS.foldr
  foldl = MS.foldl
  foldrWithKey = MS.foldrWithKey
  foldlWithKey = MS.foldlWithKey
  foldWithKeyBy ks f z m = foldl' f' z ks
    where f' z k = maybe z (flip (f k) z) (m !? k)

instance (Ord k, Finite k) => TypeMapPartial (MS.Map k) k where
  empty = MS.empty
  singleton = MS.singleton
  fromAssocs = MS.fromList
  fromAssocsWith = MS.fromListWith
  fromAssocsWithKey = MS.fromListWithKey
  insert = MS.insert
  insertWith = MS.insertWith
  insertWithKey = MS.insertWithKey
  insertLookupWithKey = MS.insertLookupWithKey
  delete = MS.delete
  adjust = MS.adjust
  update = MS.update
  updateLookup = MS.updateLookupWithKey . const
  alter = MS.alter
  findWithDefault = MS.findWithDefault
  member = MS.member
  null = MS.null
  size = fromIntegral . MS.size
  union = MS.union
  unionWithKey = MS.unionWithKey
  unions = MS.unions

-- immutable arrays

amap f = MkTotalArray . f . getTotalArray

instance (Eq k, Finite k) => TypeMap (TotalArray k) k where
  lookup k = Just . get k
  assocs = zip enumerate . A.elems . getTotalArray
  replace k v = amap (A.// [(toNatural k, v)])
  replaceWith f k = amap $ \m -> let i = toNatural k in (m A.// [f <$> (i, m A.! i)])
  map f = amap (A.listArray (0,n-1) . Prelude.map f . A.elems)
    where CardFin n = cardinality (Proxy :: Proxy k)
  mapWithKey f = amap (A.listArray (0,n-1) . zipWith f enumerate . A.elems)
    where CardFin n = cardinality (Proxy :: Proxy k)
  mapAccumWithKey f acc (MkTotalArray m) =
      MkTotalArray . A.listArray (0,n-1) . reverse <$>
        foldl' go (acc,[]) (zip enumerate $ A.elems m)
    where CardFin n = cardinality (Proxy :: Proxy k)
          go (z,xs) (k,v) = let (z',x) = f z k v in (z',x:xs)
  mapAccumRWithKey f acc (MkTotalArray m) =
      MkTotalArray . A.listArray (0,n-1) <$>
        Prelude.foldr go (acc,[]) (zip enumerate $ A.elems m)
    where CardFin n = cardinality (Proxy :: Proxy k)
          go (k,v) (z,xs) = let (z',x) = f z k v in (z',x:xs)

  mapAccumWithKeyBy ks f acc (MkTotalArray m) = runST $ do
      m' <- (AM.newArray_ (0, n-1) :: ST s (AS.STArray s Natural c))
      acc' <- foldM (go m') acc ks
      m'' <- unsafeFreeze m'
      return (acc', MkTotalArray m'')
    where
      CardFin n = cardinality (Proxy :: Proxy k)
      go m' a k =
        let i = toNatural k
            (a', v') = f a k (m A.! i)
        in AM.writeArray m' i v' >> return a'

  foldr f acc = Prelude.foldr f acc . A.elems . getTotalArray
  foldl f acc = Prelude.foldl f acc . A.elems . getTotalArray
  foldrWithKey f acc =
    Prelude.foldr ($) acc . zipWith f enumerate . A.elems . getTotalArray
  foldlWithKey f acc =
    Prelude.foldl (uncurry . f) acc . zip enumerate . A.elems . getTotalArray
  foldWithKeyBy ks f acc (MkTotalArray m) =
    Prelude.foldr (\k -> f k (m A.! toNatural k)) acc ks

instance (Eq k, Finite k) => TypeMapTotal (TotalArray k) k where
  build f = MkTotalArray $ A.listArray (0, n-1) (Prelude.map f enumerate)
    where CardFin n = cardinality (Proxy :: Proxy k)
  get k (MkTotalArray m) = m A.! (toNatural k)
