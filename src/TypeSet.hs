{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NoStarIsType #-}

module TypeSet where
import Data.Proxy (Proxy(Proxy),asProxyTypeOf)
import Numeric.Natural (Natural)
import Data.Void (Void)
import Data.Bits (Bits(bitSizeMaybe), FiniteBits(finiteBitSize))
import qualified Data.Bits as B
import qualified Data.Word as W
import Data.Foldable (foldl')
import Data.List (tails, foldl1', and, or, elem)
import Data.Maybe (catMaybes)
import Data.Tuple (swap)
import Control.Applicative (liftA2)
import Control.Monad (liftM2)
import qualified Data.Map.Strict as MS
import GHC.TypeNats (Nat, type (^), type (+), type (*), type CmpNat)
import GHC.TypeLits (TypeError, ErrorMessage(..))

import TypeSet.Algorithm

bitsToNatural :: Bits b => b -> Natural
bitsToNatural x | bitsIsInfinite x = toNatural $ bitsToInteger' x
                | otherwise        = fromDigitsReverse 2 . map (\case {False->0; True->1}) $ popBits x


bitsFromNatural :: Bits b => Natural -> b
bitsFromNatural x = let ifInf = bitsFromInteger' $ fromNatural' x
                        ifFin = bitsFromInteger' $ fromIntegral x
                    in if bitsIsInfinite ifInf then ifInf else ifFin

bitsToInteger' :: Bits b => b -> Integer
bitsToInteger' x | bitsIsNegative' x = -1 - bitsToInteger' (B.complement x)
                 | otherwise         = fromIntegral $ bitsToNatural x

bitsFromInteger' :: Bits b => Integer -> b
bitsFromInteger' x | x < 0 = B.complement (bitsFromInteger' (-1 - x))
                   | otherwise = foldl' B.setBit B.zeroBits . map fst
                                     . Prelude.filter ((==1) . snd) . zip [0..]
                                     $ digitsReverse 2 x

data Cardinal = CardFin Natural | CardInf { bethIndex :: Natural } deriving Show

class TypeSet a where
  type Cardinality a :: Cardinal'
  cardinality :: Proxy a -> Cardinal

class TypeSet a => Countable a where
  toNatural :: a -> Natural
  fromNatural :: Natural -> Maybe a
  fromNatural' :: Natural -> a
  fromNatural' = maybe (error "invalid domain") id . fromNatural
  enumerate :: [a]
  enumerate = 
    map fromNatural' $
    case cardinality (Proxy :: Proxy a) of
      CardFin 0 -> []
      CardFin p -> [0..p-1]
      CardInf 0 -> [0..]

class Countable a => Finite a where

class (Eq a, Eq s, Countable a) => TypeSubset s a | s -> a where
  empty :: s
  universe :: s
  powerset :: [s]
  complement :: s -> s
  singleton :: a -> s
  fromList :: [a] -> s
  toList :: s -> [a]
  member :: a -> s -> Bool
  subsetCardinality :: s -> Cardinal
  size :: s -> Maybe Natural
  size' :: s -> Natural
  null :: s -> Bool
  isSubsetOf, isProperSubsetOf, disjoint :: s -> s -> Bool
  union, difference, symmetricDifference, intersection :: s -> s -> s
  unions, intersections :: [s] -> s
  filter :: (a -> Bool) -> s -> s
  build :: (a -> Bool) -> s

  universe = fromList enumerate
  empty = fromList []
  powerset = map fromList . subsets $ toList (universe :: s)
    where subsets = ([]:) . concatMap go . tails
          go (x:xs) = map (x:) $ subsets xs
          go _      = []
  complement = difference universe
  singleton = fromList . pure
  fromList = unions . map singleton
  member x = elem x . toList
  subsetCardinality = maybe (CardInf 0) CardFin . size
  size = (\case {CardFin a -> Just a; _ -> Nothing}) . subsetCardinality
  size' = maybe (error "Attempt to count an infinite subset") id . size
  null = (== Just 0) . size
  isSubsetOf a b = b == union a b
  isProperSubsetOf a b = a /= b && isSubsetOf a b
  disjoint a b = TypeSet.null (union a b)
  union a b = fromList (toList a ++ toList b)
  difference a b = a `intersection` complement b
  symmetricDifference a b = (a `difference` b) `union` (b `difference` a)
  intersection a b = complement (complement a `union` complement b)
  unions = foldl' union empty
  intersections = complement . unions . map complement
  filter p = fromList . Prelude.filter p . toList
  build = flip TypeSet.filter universe


instance TypeSet Void where
  type Cardinality Void = CardFin' 0
  cardinality Proxy = CardFin 0
instance Countable Void where
  toNatural = \case
  fromNatural = const Nothing
instance Finite Void

instance TypeSet () where
  type Cardinality () = CardFin' 1
  cardinality Proxy = CardFin 1
instance Countable () where
  toNatural () = 0
  fromNatural 0 = Just ()
  fromNatural _ = Nothing
instance Finite ()

instance TypeSet Bool where
  type Cardinality Bool = CardFin' 2
  cardinality Proxy = CardFin 2
instance Countable Bool where
  toNatural False = 0
  toNatural True = 1
  fromNatural 0 = Just False
  fromNatural 1 = Just True
  fromNatural _ = Nothing
instance Finite Bool

instance TypeSet Natural where
  type Cardinality Natural = CardInf' 0
  cardinality Proxy = CardInf 0
instance Countable Natural where
  toNatural = id
  fromNatural = Just
  fromNatural' = id

instance TypeSet Integer where
  type Cardinality Integer = CardInf' 0
  cardinality Proxy = CardInf 0
instance Countable Integer where
  toNatural x | x >= 0 = 2 * fromInteger x
              | x < 0  = 2 * fromInteger (-x) - 1
  fromNatural' x = case divMod (toInteger x) 2 of
                     (x, 0) -> x
                     (x, 1) -> -1-x
  fromNatural = Just . fromNatural'

-- haskell doesn't like when this isn't newtype'd...
newtype MkBits a = MkBits {getBits :: a}

instance Bits b => TypeSet (MkBits b) where
  cardinality Proxy = maybe (CardInf 0) (CardFin . (2^)) $ bitSizeMaybe (undefined :: b)
instance Bits b => Countable (MkBits b) where
  toNatural = bitsToNatural . getBits
  fromNatural x = case cardinality (Proxy :: Proxy (MkBits b)) of
    CardFin y | x >= y -> Nothing
    _                  -> Just . MkBits $ bitsFromNatural x
instance FiniteBits b => Finite (MkBits b)

instance (TypeSet a, TypeSet b) => TypeSet (Either a b) where
  type Cardinality (Either a b) = CardAdd (Cardinality a) (Cardinality b)
  cardinality Proxy = case (cardinality (Proxy :: Proxy a), cardinality (Proxy :: Proxy b)) of
    (CardFin a, CardFin b) -> CardFin (a + b)
    (CardFin a, CardInf b) -> CardInf b
    (CardInf a, CardFin b) -> CardInf a
    (CardInf a, CardInf b) -> CardInf (max a b)
instance (Countable a, Countable b) => Countable (Either a b) where
  toNatural x = case (cardinality (Proxy :: Proxy a), cardinality (Proxy :: Proxy b), x) of
    (CardFin a, _, Left y) -> toNatural y
    (CardFin a, _, Right y) -> a + toNatural y
    (CardInf 0, CardFin b, Left y) -> b + toNatural y
    (CardInf 0, CardInf 0, Left y) -> 2 * toNatural y
    (CardInf 0, CardInf 0, Right y) -> 1 + 2 * toNatural y
  fromNatural x = case (cardinality (Proxy :: Proxy a), cardinality (Proxy :: Proxy b)) of
    (CardFin a, _) | x < a     -> Left <$> fromNatural x
                   | otherwise -> Right <$> fromNatural (x - a)
    (CardInf 0, CardFin b) | x < b     -> Right <$> fromNatural x
                           | otherwise -> Left <$> fromNatural (x - b)
    (CardInf 0, CardInf 0) -> case divMod x 2 of
                            (x, 0) -> Left <$> fromNatural x
                            (x, 1) -> Right <$> fromNatural x
instance (Finite a, Finite b) => Finite (Either a b)

instance (TypeSet a, TypeSet b) => TypeSet (a, b) where
  type Cardinality (a, b) = CardMul (Cardinality a) (Cardinality b)
  cardinality Proxy = case (cardinality (Proxy :: Proxy a), cardinality (Proxy :: Proxy b)) of
    (CardFin a, CardFin b) -> CardFin (a * b)
    (CardFin a, CardInf b) -> CardInf b
    (CardInf a, CardFin b) -> CardInf a
    (CardInf a, CardInf b) -> CardInf (max a b)
instance (Countable a, Countable b) => Countable (a, b) where
  toNatural (x, y) =
    let m = toNatural x
        n = toNatural y
    in case (cardinality (Proxy :: Proxy a), cardinality (Proxy :: Proxy b)) of
      (CardFin a, _) -> n*a + m
      (CardInf 0, CardFin b) -> m*b + n
      (CardInf 0, CardInf 0) -> cantorPair m n
  fromNatural x = (\(x,y) -> liftA2 (,) (fromNatural x) (fromNatural y)) $
    case (cardinality (Proxy :: Proxy a), cardinality (Proxy :: Proxy b)) of
      (CardFin a, _) -> swap $ divMod x a
      (CardInf 0, CardFin b) -> divMod x b
      (CardInf 0, CardInf 0) -> cantorUnpair x
instance (Finite a, Finite b) => Finite (a, b)

instance (TypeSet a, TypeSet b) => TypeSet (a -> b) where
  type Cardinality (a -> b) = CardExp (Cardinality a) (Cardinality b)
  cardinality Proxy = case (cardinality (Proxy :: Proxy a), cardinality (Proxy :: Proxy b)) of
    (CardFin a, CardFin b) -> CardFin (b ^ a)
    (CardFin a, CardInf b) -> CardInf b
    (CardInf a, CardFin b) -> CardInf (a + 1)
    (CardInf a, CardInf b) -> CardInf (max (a+1) b)
instance (Finite a, Countable b) => Countable (a -> b) where
  toNatural f = case (cardinality (Proxy :: Proxy a), cardinality (Proxy :: Proxy b)) of
                  (CardFin 0, _) -> 0
                  (_, CardFin p) -> sum $ zipWith (\n a -> p^n * toNatural (f a)) [0..] enumerate
                  (_, CardInf 0) -> snd . cantorZip' $ map (toNatural . f) enumerate
  fromNatural x = 
    let CardFin n = cardinality (Proxy :: Proxy a) in
    case cardinality (Proxy :: Proxy b) of
      CardInf 0 | n == 0 -> Just (\case)
                | otherwise -> 
        let m = MS.fromList . zip [0..n-1] . map fromNatural' $ cantorUnzip' (pred n) x
        in Just ((m MS.!) . toNatural)
      CardFin p ->
        let m = MS.fromList . zip [0..n-1] . map fromNatural' $ digitsReverse p x ++ repeat 0
        in if (x < p^n) then Just ((m MS.!) . toNatural) else Nothing
instance (Finite a, Finite b) => Finite (a -> b)

instance TypeSet a => TypeSet [a] where
  type Cardinality [a] = CardList (Cardinality a)
  cardinality Proxy = case cardinality (Proxy :: Proxy a) of
    CardFin _ -> CardInf 0
    x -> x
instance Countable a => Countable [a] where
  toNatural = case cardinality (Proxy :: Proxy a) of
                       CardFin p -> pred . foldl' ((+) . (p*)) 1 . map toNatural
                       CardInf 0 -> cantorZip . map toNatural
  fromNatural = case cardinality (Proxy :: Proxy a) of
                       CardFin p -> (>>= sequence . map fromNatural) . validate . digits p . succ
                       CardInf 0 -> Just . map fromNatural' . cantorUnzip
    where validate (1:xs) = Just xs
          validate _      = Nothing


-- bitset for fixed b
newtype BitSet' univ b = BitSet' {getBitSet' :: b} deriving (Eq)

-- opaque type (right approach ???)
data BitSet u = BS8 (BitSet' u W.Word8)
              | BS16 (BitSet' u W.Word16)
              | BS32 (BitSet' u W.Word32)
              | BS64 (BitSet' u W.Word64)
              | BSBig (BitSet' u Natural)

instance (Eq u, Countable u, Bits b) => TypeSubset (BitSet' u b) u where
  empty = BitSet' B.zeroBits
  toList = map fst . Prelude.filter snd . zip enumerate . popBits . getBitSet'
  member x (BitSet' s) = B.testBit s (fromIntegral $ toNatural x)
  null = (== empty)

instance (Finite u, Eq v) => Eq (u -> v) where
  f == g = and $ zipWith (==) (map f enumerate) (map g enumerate)

instance (Eq u, Finite u) => TypeSubset (u -> Bool) u where
  empty = const False
  universe = const True
  powerset = enumerate
  complement = (not .)
  singleton = (==)
  fromList = flip elem
  toList = flip Prelude.filter enumerate
  member = flip ($)
  size = Just . fromIntegral . length . toList
  union = liftM2 (||)
  intersection = liftM2 (&&)
  difference f g x = f x && not (g x)
  unions fs x = any ($ x) fs
  intersections fs x = all ($ x) fs
  filter = intersection
  build = id

-- type family Injection a b
-- type instance Injection Void Word8
-- type instance Injection Void Word16
-- type instance Injection Void Word32
-- type instance Injection Void Word64
-- type instance Injection a Word8 => Injection a Word16
-- type instance Injection a Word16 => Injection a Word32
-- type instance Injection a Word32 => Injection a Word64

-- class Injection a b
-- instance Injection Void W.Word8
-- instance Injection Void W.Word16

-- foo :: Injection a W.Word8 => Bool
-- foo = True


-- TODO -- use Cardinality of typesets to compare against 8 for word8, etc in order to determine whether using 
data Cardinal' = CardFin' Nat | CardInf' Nat

type family CardAdd a b where
  CardAdd (CardFin' a) (CardFin' b) = CardFin' (a + b)
  CardAdd (CardFin' a) (CardInf' b) = CardInf' b
  CardAdd (CardInf' a) (CardFin' b) = CardInf' a
  CardAdd (CardInf' a) (CardInf' b) = CardInf' (Max a b (CmpNat a b))

type family CardMul a b where
  CardMul (CardFin' a) (CardFin' b) = CardFin' (a * b)
  CardMul (CardFin' a) (CardInf' b) = CardInf' b
  CardMul (CardInf' a) (CardFin' b) = CardInf' a
  CardMul (CardInf' a) (CardInf' b) = CardInf' (Max a b (CmpNat a b))

type family CardExp a b where
  CardExp (CardFin' a) (CardFin' b) = CardFin' (a ^ b)
  CardExp (CardFin' a) (CardInf' b) = CardInf' b
  CardExp (CardInf' a) (CardFin' b) = CardInf' (a + 1)
  CardExp (CardInf' a) (CardInf' b) = CardInf' (Max (a + 1) b (CmpNat (a + 1) b))

type family CardList a where
  CardList (CardFin' 0) = CardFin' 1
  CardList (CardFin' a) = CardInf' 0
  CardList x = x

type family Max (a :: Nat) (b :: Nat) (c :: Ordering) where
  Max a b LT = b
  Max a b EQ = a
  Max a b GT = a

type family CmpCard a b where
  CmpCard (CardFin' a) (CardFin' b) = CmpNat a b
  CmpCard (CardFin' a) (CardInf' b) = LT
  CmpCard (CardInf' a) (CardFin' b) = GT
  CmpCard (CardInf' a) (CardInf' b) = CmpNat a b

type family ShowCardinality a where
  ShowCardinality (CardFin' a) = ShowType a
  ShowCardinality (CardInf' 0) = Text "Countably Infinite"
  ShowCardinality (CardInf' 1) = Text "Continuum"
  ShowCardinality (CardInf' b) = Text "Beth#" :<>: ShowType b

type family CmpLTErr a (b :: Nat) c where
  CmpLTErr _ _ LT = ()
  CmpLTErr a b _  = TypeError (Text "Error: Cannot fit powerset of given type " :<>: ShowType a :<>: Text " (Cardinality: " :<>: ShowCardinality (Cardinality a) :<>: Text ") into bitset of width " :<>: ShowType b :<>: Text "!")

type CanUseBitSet a (b :: Nat) = CmpLTErr a b (CmpCard (Cardinality a) (CardFin' b)) ~ ()

foo :: CanUseBitSet a 8 => a -> Bool
foo _ = True