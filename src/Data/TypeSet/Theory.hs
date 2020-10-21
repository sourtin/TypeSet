{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}

module Data.TypeSet.Theory where
import Data.Proxy (Proxy(Proxy))
import Numeric.Natural (Natural)
import Data.Void (Void)
import Data.Bits (Bits(bitSizeMaybe), FiniteBits)
import qualified Data.Bits as B
import qualified Data.Int as I
import qualified Data.Word as W
import Data.Foldable (foldl')
import Data.Tuple (swap)
import Control.Applicative (liftA2)
import qualified Data.Map.Strict as MS
import GHC.TypeNats (Nat, type (^))
import GHC.TypeLits (ErrorMessage(..))

import Data.TypeSet.Algorithm
import Data.TypeSet.Cardinality

type family BitWidth a :: Cardinal'

type BitSettable a b = Injectable (Cardinality a) (BitWidth b) (Text "Error: Cannot fit powerset of given type " :<>: ShowType a :<>: Text " (Cardinality: " :<>: ShowCardinality (Cardinality a) :<>: Text ") into bitset of type " :<>: ShowType b :<>: Text " and width " :<>: ShowType (BitWidth b) :<>: Text "!")

type InfiniteBitSet = Integer
type FiniteBitSets = '[W.Word8, W.Word16, W.Word32, W.Word64]
type BitSetMin a = BitSetMin' (Cardinality a) FiniteBitSets
type family BitSetMin' (a :: Cardinal') (bs :: [*]) :: * where
  BitSetMin' _ '[] = InfiniteBitSet
  BitSetMin' a (b : bs) = UnlessEqual (CmpCard a (BitWidth b)) GT b (BitSetMin' a bs)

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

---

instance TypeSet Void where
  type Cardinality Void = CardFin' 0
  cardinality Proxy = CardFin 0
instance Countable Void where
  toNatural = \case
  fromNatural = const Nothing
instance Finite Void

type instance BitWidth () = CardFin' 0
instance TypeSet () where
  type Cardinality () = CardFin' 1
  cardinality Proxy = CardFin 1
instance Countable () where
  toNatural () = 0
  fromNatural 0 = Just ()
  fromNatural _ = Nothing
instance Finite ()

type instance BitWidth Bool = CardFin' 1
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

type instance BitWidth Natural = CardInf' 0
instance TypeSet Natural where
  type Cardinality Natural = CardInf' 0
  cardinality Proxy = CardInf 0
instance Countable Natural where
  toNatural = id
  fromNatural = Just
  fromNatural' = id

type instance BitWidth Integer = CardInf' 0
instance TypeSet Integer where
  type Cardinality Integer = CardInf' 0
  cardinality Proxy = CardInf 0
instance Countable Integer where
  toNatural = bijIntNat
  fromNatural' = bijNatInt
  fromNatural = Just . fromNatural'

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
  type Cardinality (a -> b) = CardExp (Cardinality b) (Cardinality a)
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

---

type instance BitWidth W.Word8 = CardFin' 8
instance TypeSet W.Word8 where
  type Cardinality W.Word8 = CardFin' (2^8)
  cardinality Proxy = CardFin (2^8)
instance Countable W.Word8 where
  toNatural = fromIntegral
  fromNatural x | x < 2^8   = Just (fromIntegral x)
                | otherwise = Nothing
instance Finite W.Word8

type instance BitWidth W.Word16 = CardFin' 16
instance TypeSet W.Word16 where
  type Cardinality W.Word16 = CardFin' (2^16)
  cardinality Proxy = CardFin (2^16)
instance Countable W.Word16 where
  toNatural = fromIntegral
  fromNatural x | x < 2^16  = Just (fromIntegral x)
                | otherwise = Nothing
instance Finite W.Word16

type instance BitWidth W.Word32 = CardFin' 32
instance TypeSet W.Word32 where
  type Cardinality W.Word32 = CardFin' (2^32)
  cardinality Proxy = CardFin (2^32)
instance Countable W.Word32 where
  toNatural = fromIntegral
  fromNatural x | x < 2^32  = Just (fromIntegral x)
                | otherwise = Nothing
instance Finite W.Word32

type instance BitWidth W.Word64 = CardFin' 64
instance TypeSet W.Word64 where
  type Cardinality W.Word64 = CardFin' (2^64)
  cardinality Proxy = CardFin (2^64)
instance Countable W.Word64 where
  toNatural = fromIntegral
  fromNatural x | x < 2^64  = Just (fromIntegral x)
                | otherwise = Nothing
instance Finite W.Word64

-- convenience functions for bounded integrals
-- for some reason scopedtypevariables isn't applying here, so we use
-- a little hack to get the typechecker to do what we want
boundedToNat :: (Bounded a, Integral a) => a -> Natural
boundedToNat x = fromIntegral (fromIntegral x - fromIntegral lb :: Integer)
  where lb = minBound
        lb' = lb + (x-x)

natToBounded :: (Bounded a, Integral a) => Natural -> Maybe a
natToBounded x | x <= range = Just y
               | otherwise  = Nothing
  where range' = fromIntegral ub - fromIntegral lb :: Integer
        range = fromIntegral range'
        ub = maxBound
        lb = minBound
        y = fromIntegral (fromIntegral x + fromIntegral lb :: Integer)
        lb' = lb + ub + (y-y)

type instance BitWidth I.Int8 = CardFin' 8
instance TypeSet I.Int8 where
  type Cardinality I.Int8 = CardFin' (2^8)
  cardinality Proxy = CardFin (2^8)
instance Countable I.Int8 where
  toNatural = boundedToNat
  fromNatural = natToBounded
instance Finite I.Int8

type instance BitWidth I.Int16 = CardFin' 16
instance TypeSet I.Int16 where
  type Cardinality I.Int16 = CardFin' (2^16)
  cardinality Proxy = CardFin (2^16)
instance Countable I.Int16 where
  toNatural = boundedToNat
  fromNatural = natToBounded
instance Finite I.Int16

type instance BitWidth I.Int32 = CardFin' 32
instance TypeSet I.Int32 where
  type Cardinality I.Int32 = CardFin' (2^32)
  cardinality Proxy = CardFin (2^32)
instance Countable I.Int32 where
  toNatural = boundedToNat
  fromNatural = natToBounded
instance Finite I.Int32

type instance BitWidth I.Int64 = CardFin' 64
instance TypeSet I.Int64 where
  type Cardinality I.Int64 = CardFin' (2^64)
  cardinality Proxy = CardFin (2^64)
instance Countable I.Int64 where
  toNatural = boundedToNat
  fromNatural = natToBounded
instance Finite I.Int64

type instance BitWidth Char = CardFin' 20
instance TypeSet Char where
  type Cardinality Char = CardFin' 0x110000
  cardinality Proxy = CardFin 0x110000
instance Countable Char where
  toNatural = fromIntegral . fromEnum
  fromNatural x | x < 0x110000 = Just . toEnum $ fromIntegral x
                | otherwise    = Nothing
instance Finite Char

---

instance (TypeSet a, TypeSet b, TypeSet c) => TypeSet (a, b, c) where
  type Cardinality (a, b, c) = Cardinality (a, (b, c))
  cardinality Proxy = cardinality (Proxy :: Proxy (a, (b, c)))
instance (Countable a, Countable b, Countable c) => Countable (a, b, c) where
  toNatural (x, y, z) = toNatural (x, (y, z))
  fromNatural = fmap (\(x, (y, z)) -> (x, y, z)) . fromNatural
instance (Finite a, Finite b, Finite c) => Finite (a, b, c)

instance (TypeSet a, TypeSet b, TypeSet c, TypeSet d) => TypeSet (a, b, c, d) where
  type Cardinality (a, b, c, d) = Cardinality ((a, b), (c, d))
  cardinality Proxy = cardinality (Proxy :: Proxy ((a, b), (c, d)))
instance (Countable a, Countable b, Countable c, Countable d) => Countable (a, b, c, d) where
  toNatural (w, x, y, z) = toNatural ((w, x), (y, z))
  fromNatural = fmap (\((w, x), (y, z)) -> (w, x, y, z)) . fromNatural
instance (Finite a, Finite b, Finite c, Finite d) => Finite (a, b, c, d)

instance (TypeSet a, TypeSet b, TypeSet c, TypeSet d, TypeSet e) => TypeSet (a, b, c, d, e) where
  type Cardinality (a, b, c, d, e) = Cardinality ((a, b), (c, d, e))
  cardinality Proxy = cardinality (Proxy :: Proxy ((a, b), (c, d, e)))
instance (Countable a, Countable b, Countable c, Countable d, Countable e) => Countable (a, b, c, d, e) where
  toNatural (v, w, x, y, z) = toNatural ((v, w), (x, y, z))
  fromNatural = fmap (\((v, w), (x, y, z)) -> (v, w, x, y, z)) . fromNatural
instance (Finite a, Finite b, Finite c, Finite d, Finite e) => Finite (a, b, c, d, e)