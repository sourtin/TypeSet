{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}

module TypeSet.Theory where
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
import GHC.TypeNats (Nat)
import GHC.TypeLits (ErrorMessage(..))

import TypeSet.Algorithm
import TypeSet.Cardinality

type BitSettable a (b :: Nat) = Injectable (Cardinality a) (CardFin' b) (Text "Error: Cannot fit powerset of given type " :<>: ShowType a :<>: Text " (Cardinality: " :<>: ShowCardinality (Cardinality a) :<>: Text ") into bitset of width " :<>: ShowType b :<>: Text "!")

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

---

-- I.Int
-- I.Int8
-- I.Int16
-- I.Int32
-- I.Int64
-- W.Word
-- W.Word8
-- W.Word16
-- W.Word32
-- W.Word64
