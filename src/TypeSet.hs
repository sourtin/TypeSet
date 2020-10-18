{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}

module TypeSet where
import Data.Proxy (Proxy(Proxy),asProxyTypeOf)
import Numeric.Natural (Natural)
import Data.Void (Void)
import Data.Bits (testBit, setBit, zeroBits, Bits(bitSizeMaybe), FiniteBits(finiteBitSize))
import Data.Foldable (foldl')
import Data.List (tails, foldl1')
import Data.Maybe (catMaybes)
import Data.Tuple (swap)
import Control.Applicative (liftA2)
import qualified Data.Map.Strict as MS

data Cardinal = CardFin Natural | CardInf { bethIndex :: Natural } deriving Show

class TypeSet a where
  cardinality :: Proxy a -> Cardinal

-- =
instance TypeSet Void where
  cardinality Proxy = CardFin 0
instance TypeSet () where
  cardinality Proxy = CardFin 1
instance TypeSet Bool where
  cardinality Proxy = CardFin 2
instance TypeSet Integer where
  cardinality Proxy = CardInf 0

-- instance {-# OVERLAPPABLE #-} FiniteBits b => TypeSet b where
--   cardinality = CardFin . (2^) . finiteBitSize . asProxyTypeOf undefined
instance {-# OVERLAPPABLE #-} Bits b => TypeSet b where
  cardinality = maybe (CardInf 0) (CardFin . (2^)) . bitSizeMaybe . asProxyTypeOf undefined

instance (TypeSet a, TypeSet b) => TypeSet (Either a b) where
  cardinality Proxy = case (cardinality (Proxy :: Proxy a), cardinality (Proxy :: Proxy b)) of
    (CardFin a, CardFin b) -> CardFin (a + b)
    (CardFin a, CardInf b) -> CardInf b
    (CardInf a, CardFin b) -> CardInf a
    (CardInf a, CardInf b) -> CardInf (max a b)

instance (TypeSet a, TypeSet b) => TypeSet (a, b) where
  cardinality Proxy = case (cardinality (Proxy :: Proxy a), cardinality (Proxy :: Proxy b)) of
    (CardFin a, CardFin b) -> CardFin (a * b)
    (CardFin a, CardInf b) -> CardInf b
    (CardInf a, CardFin b) -> CardInf a
    (CardInf a, CardInf b) -> CardInf (max a b)

instance (TypeSet a, TypeSet b) => TypeSet (a -> b) where
  cardinality Proxy = case (cardinality (Proxy :: Proxy a), cardinality (Proxy :: Proxy b)) of
    (CardFin a, CardFin b) -> CardFin (b ^ a)
    (CardFin a, CardInf b) -> CardInf b
    (CardInf a, CardFin b) -> CardInf (a + 1)
    (CardInf a, CardInf b) -> CardInf (max (a+1) b)

class (Eq a, Eq s, TypeSet a) => TypeSubset s a | s -> a where
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

  universe = complement empty
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

class Countable a where
  toNatural :: a -> Natural
  fromNatural :: Natural -> Maybe a
  fromNatural' :: Natural -> a
  fromNatural' = maybe (error "invalid domain") id . fromNatural
  enumerate :: [(Natural, a)]
  enumerate = 
    catMaybes . map (\x -> (x,) <$> fromNatural x) $
    case upperBound (Proxy :: Proxy a) of
      Just 0 -> []
      Just p -> [0..p-1]
      Nothing -> [0..]
  upperBound :: Proxy a -> Maybe Natural
class Countable a => Finite a where
  upperBound' :: Proxy a -> Natural
  upperBound' = maybe undefined id . upperBound

instance Finite Void
instance Countable Void where
  toNatural = \case
  fromNatural = const Nothing
  upperBound Proxy = Just 0
instance Finite ()
instance Countable () where
  toNatural () = 0
  fromNatural 0 = Just ()
  fromNatural _ = Nothing
  upperBound Proxy = Just 1
instance Finite Bool
instance Countable Bool where
  toNatural False = 0
  toNatural True = 1
  fromNatural 0 = Just False
  fromNatural 1 = Just True
  fromNatural _ = Nothing
  upperBound Proxy = Just 2
instance Countable Natural where
  toNatural = id
  fromNatural = Just
  fromNatural' = id
  upperBound Proxy = Nothing
instance Countable Integer where
  toNatural x | x >= 0 = 2 * fromInteger x
              | x < 0  = 2 * fromInteger (-x) - 1
  fromNatural' x = case divMod (toInteger x) 2 of
                     (x, 0) -> x
                     (x, 1) -> -1-x
  fromNatural = Just . fromNatural'
  upperBound Proxy = Nothing
newtype FB a = FB {getFB :: a}
instance {-# OVERLAPPABLE #-} FiniteBits b => Finite (FB b) where
  upperBound' Proxy = (2^) . fromIntegral $ finiteBitSize (undefined :: b)
instance {-# OVERLAPPABLE #-} FiniteBits b => Countable (FB b) where
  toNatural (FB x) = fromDigitsReverse 2 $ map (toNatural . testBit x) [0..(finiteBitSize x)-1]
  fromNatural x | x >= upperBound' (Proxy :: Proxy (FB b)) = Nothing
                | otherwise = Just . FB . foldl' setBit zeroBits . map fst . Prelude.filter ((==1) . snd) .
                                  zip [0..(finiteBitSize (undefined :: b))-1] $ digitsReverse 2 x ++ repeat 0
  upperBound = Just . upperBound'
-- haskell doesn't like this???
---- instance {-# OVERLAPPABLE #-} FiniteBits b => Finite b where
----   upperBound' Proxy = (2^) . fromIntegral $ finiteBitSize (undefined :: b)
---- instance {-# OVERLAPPABLE #-} FiniteBits b => Countable b where
----   toNatural x = fromDigitsReverse 2 $ map (toNatural . testBit x) [0..(finiteBitSize x)-1]
----   fromNatural x | x >= upperBound' (Proxy :: Proxy b) = Nothing
----                 | otherwise = Just . foldl' setBit zeroBits . map fst . Prelude.filter ((==1) . snd) .
----                                   zip [0..(finiteBitSize (undefined :: b))-1] $ digitsReverse 2 x ++ repeat 0
----   upperBound = Just . upperBound'
instance (Finite a, Finite b) => Finite (Either a b)
instance (Countable a, Countable b) => Countable (Either a b) where
  toNatural x = case (upperBound (Proxy :: Proxy a), upperBound (Proxy :: Proxy b), x) of
    (Just a, _, Left y) -> toNatural y
    (Just a, _, Right y) -> a + toNatural y
    (Nothing, Just b, Left y) -> b + toNatural y
    (Nothing, Nothing, Left y) -> 2 * toNatural y
    (Nothing, Nothing, Right y) -> 1 + 2 * toNatural y
  fromNatural x = case (upperBound (Proxy :: Proxy a), upperBound (Proxy :: Proxy b)) of
    (Just a, _) -> if x < a then Left <$> fromNatural x else Right <$> fromNatural (x - a)
    (Nothing, Just b) -> if x < b then Right <$> fromNatural x else Left <$> fromNatural (x - b)
    (Nothing, Nothing) -> case divMod x 2 of
                            (x, 0) -> Left <$> fromNatural x
                            (x, 1) -> Right <$> fromNatural x
  upperBound Proxy = liftA2 (+) (upperBound (Proxy :: Proxy a))
                                (upperBound (Proxy :: Proxy b))
instance (Finite a, Finite b) => Finite (a, b)
instance (Countable a, Countable b) => Countable (a, b) where
  toNatural (x, y) =
    let m = toNatural x
        n = toNatural y
    in case (upperBound (Proxy :: Proxy a), upperBound (Proxy :: Proxy b)) of
      (Just a, _) -> n*a + m
      (Nothing, Just b) -> m*b + n
      (Nothing, Nothing) -> cantorPair m n
  fromNatural x = (\(x,y) -> liftA2 (,) (fromNatural x) (fromNatural y)) $
    case (upperBound (Proxy :: Proxy a), upperBound (Proxy :: Proxy b)) of
      (Just a, _) -> swap $ divMod x a
      (Nothing, Just b) -> divMod x b
      (Nothing, Nothing) -> cantorUnpair x
  upperBound Proxy = liftA2 (*) (upperBound (Proxy :: Proxy a))
                                (upperBound (Proxy :: Proxy b))
instance (Finite a, Finite b) => Finite (a -> b)
instance (Finite a, Countable b) => Countable (a -> b) where
  toNatural f = case (upperBound (Proxy :: Proxy a), upperBound (Proxy :: Proxy b)) of
                  (Just 0, _) -> 0
                  (_, Just p) -> sum [p^n * toNatural (f a) | (n,a) <- enumerate]
                  (_, Nothing) -> snd . cantorZip' $ map (toNatural . f . snd) enumerate
  fromNatural x = 
    let Just n = upperBound (Proxy :: Proxy a) in
    case upperBound (Proxy :: Proxy b) of
      Nothing | n == 0 -> Just (\case)
              | otherwise -> 
        let m = MS.fromList . zip [0..n-1] . map fromNatural' $ cantorUnzip' (pred n) x
        in Just ((m MS.!) . toNatural)
      Just p ->
        let m = MS.fromList . zip [0..n-1] . map fromNatural' $ digitsReverse p x ++ repeat 0
        in if (x < p^n) then Just ((m MS.!) . toNatural) else Nothing
  upperBound Proxy = liftA2 (^) (upperBound (Proxy :: Proxy b))
                                (upperBound (Proxy :: Proxy a))
instance Countable a => Countable [a] where
  toNatural = case upperBound (Proxy :: Proxy a) of
                       Just p -> pred . foldl' ((+) . (p*)) 1 . map toNatural
                       Nothing -> cantorZip . map toNatural
  fromNatural = case upperBound (Proxy :: Proxy a) of
                       Just p -> (>>= sequence . map fromNatural) . validate . digits p . succ
                       Nothing -> Just . map fromNatural' . cantorUnzip
    where validate (1:xs) = Just xs
          validate _      = Nothing
  upperBound Proxy = Nothing

digitsReverse :: Integral a => a -> a -> [a]
digitsReverse p = go
  where go 0 = []
        go n = let (n',d) = divMod n p in d : go n'

digits :: Integral a => a -> a -> [a]
digits p = flip go []
  where go 0 = id
        go n = let (n',d) = divMod n p in go n' . (d :)

fromDigitsReverse :: Integral a => a -> [a] -> a
fromDigitsReverse p [] = 0
fromDigitsReverse p (x:xs) = x + p*fromDigitsReverse p xs


{- snippet: haskell wiki -}
(^!) :: Num a => a -> Int -> a
(^!) x n = x^n

squareRoot :: Integer -> Integer
squareRoot 0 = 0
squareRoot 1 = 1
squareRoot n =
   let twopows = iterate (^!2) 2
       (lowerRoot, lowerN) =
          last $ takeWhile ((n>=) . snd) $ zip (1:twopows) twopows
       newtonStep x = div (x + div n x) 2
       iters = iterate newtonStep (squareRoot (div n lowerN) * lowerRoot)
       isRoot r  =  r^!2 <= n && n < (r+1)^!2
  in  head $ dropWhile (not . isRoot) iters
{- end snippet; -}

cantorPair :: Natural -> Natural -> Natural
cantorPair x y = ((x + y) * (x + y + 1)) `div` 2 + y

cantorZip' :: [Natural] -> (Natural, Natural)
cantorZip' [x] = (0, x)
cantorZip' (x:xs) = let (n, z) = cantorZip' xs in (n+1, cantorPair x z)

cantorZip :: [Natural] -> Natural
cantorZip [] = 0
cantorZip xs = succ . uncurry cantorPair $ cantorZip' xs

cantorUnpair :: Natural -> (Natural, Natural)
cantorUnpair z = let xy1 = fromInteger . squareRoot . toInteger $ 2*z
                     t1 = xy1 * (xy1+1) `div` 2
                     t2 = xy1 * (xy1-1) `div` 2
                     y1 = z - t1
                     y2 = z - t2
                 in if z >= t1 then (xy1-y1,y1) else (xy1-1-y2,y2)

cantorUnzip' :: Natural -> Natural -> [Natural]
cantorUnzip' 0 x = [x]
cantorUnzip' n z = let (x, z') = cantorUnpair z in x : cantorUnzip' (n-1) z'

cantorUnzip :: Natural -> [Natural]
cantorUnzip 0 = []
cantorUnzip n = uncurry cantorUnzip' . cantorUnpair $ pred n