{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}

module TypeSet.Cardinality where
import Numeric.Natural (Natural)
import GHC.Exts (Constraint)
import GHC.TypeNats (Nat, type (^), type (+), type (*), type CmpNat)
import GHC.TypeLits (TypeError, ErrorMessage(..))

data Cardinal = CardFin Natural
              | CardInf { bethIndex :: Natural }
              deriving (Show, Eq, Ord)

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

type family EqualOrFail (a :: k) (b :: k) (msg :: ErrorMessage) :: Constraint where
  EqualOrFail a a _ = ()
  EqualOrFail _ _ m = TypeError m

type family NotEqualOrFail (a :: k) (b :: k) (msg :: ErrorMessage) :: Constraint where
  NotEqualOrFail a a m = TypeError m
  NotEqualOrFail _ _ _ = ()

type family UnlessEqual (a :: k) (b :: k) (c :: l) (d :: l) :: l where
  UnlessEqual a a _ d = d
  UnlessEqual _ _ c _ = c

type Injectable a b msg = NotEqualOrFail (CmpCard a b) GT msg