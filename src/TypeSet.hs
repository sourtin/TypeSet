{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}

module TypeSet where
import Data.Proxy (Proxy(Proxy),asProxyTypeOf)
import Numeric.Natural (Natural)
import Data.Void (Void)
import Data.Bits (Bits(bitSizeMaybe))
import Data.Foldable (foldl')
import Data.List (tails)
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

-- import Data.Bits (FiniteBits(finiteBitSize))
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
  upperBound :: Proxy a -> Maybe Natural
  dense :: Proxy a -> Bool
  dense Proxy = False

instance Countable Void where
  toNatural = \case {}
  fromNatural = const Nothing
  enumerate = []
  upperBound Proxy = Just 0
  dense Proxy = True
instance Countable () where
  toNatural () = 0
  fromNatural 0 = Just ()
  fromNatural _ = Nothing
  enumerate = [(0, ())]
  upperBound Proxy = Just 1
  dense Proxy = True
instance Countable Bool where
  toNatural False = 0
  toNatural True = 1
  fromNatural 0 = Just False
  fromNatural 1 = Just True
  fromNatural _ = Nothing
  enumerate = [(0, False), (1, True)]
  upperBound Proxy = Just 2
  dense Proxy = True
instance Countable Natural where
  toNatural = id
  fromNatural = Just
  fromNatural' = id
  enumerate = [(x,x) | x <- [0..]]
  upperBound Proxy = Nothing
  dense Proxy = True
instance Countable Integer where
  toNatural x | x >= 0 = 2 * fromInteger x
              | x < 0  = 2 * fromInteger (-x) - 1
  fromNatural' x = case divMod (toInteger x) 2 of
                     (x, 0) -> x
                     (x, 1) -> -1-x
  fromNatural = Just . fromNatural'
  enumerate = [(x,fromNatural' x) | x <- [0..]]
  upperBound Proxy = Nothing
  dense Proxy = True
-- instance {-# OVERLAPPABLE #-} Bits b => Countable b where
instance (Countable a, Countable b) => Countable (Either a b) where
  toNatural (Left a) = 2 * toNatural a
  toNatural (Right b) = 1 + 2 * toNatural b
  fromNatural x = case divMod x 2 of
                    (x, 0) -> Left <$> fromNatural x
                    (x, 1) -> Right <$> fromNatural x
  enumerate = go enumerate enumerate
    where go ((x,u):xs) ((y,v):ys) = (2*x,Left u) : (2*y+1,Right v) : go xs ys
          go ((x,u):xs) [] = (2*x,Left u) : go xs []
          go [] ((y,v):ys) = (2*y+1,Right v) : go [] ys
          go [] [] = []
  upperBound Proxy = do l <- upperBound (Proxy :: Proxy a)
                        r <- upperBound (Proxy :: Proxy b)
                        return $ max (2 * l + 1) (2 * r)
  dense Proxy =
    dense (Proxy :: Proxy a) && dense (Proxy :: Proxy b) &&
    (upperBound (Proxy :: Proxy a) == upperBound (Proxy :: Proxy b) ||
     upperBound (Proxy :: Proxy a) == (succ <$> upperBound (Proxy :: Proxy b)))
instance (Countable a, Countable b) => Countable (a, b) where
  toNatural (a, b) = let x = toNatural a
                         y = toNatural b
                     in ((x + y) * (x + y + 1)) `div` 2 + y
  fromNatural x = do let (y,z) = cantorUnpair x
                     a <- fromNatural y
                     b <- fromNatural z
                     return (a,b)
  enumerate = map (\x -> (toNatural x, x)) $ liftA2 (,) (map snd enumerate) (map snd enumerate)
  upperBound Proxy = toNatural <$> liftA2 (,)
                        (upperBound (Proxy :: Proxy a))
                        (upperBound (Proxy :: Proxy b))
  dense Proxy =
    dense (Proxy :: Proxy a) && dense (Proxy :: Proxy b) && 
    upperBound (Proxy :: Proxy a) == Nothing &&
    upperBound (Proxy :: Proxy b) == Nothing
    -- it is possible to make this dense for finite a,b by using a pairing function
    -- based on square numbers rather than triangle numbers
instance (Countable a, Countable b) => Countable (a -> b) where
  toNatural f = case upperBound (Proxy :: Proxy b) of
                  Just p -> sum [p^n * toNatural (f a) | (n,a) <- enumerate]
  fromNatural x = do p <- upperBound (Proxy :: Proxy b)
                     let as = enumerate :: [(Natural, a)]
                     l <- go p (map fst as) 0 (divMod x p)
                     let m = MS.fromList l
                     return ((m MS.!) . toNatural)
    where go :: Natural -> [Natural] -> Natural -> (Natural,Natural) -> Maybe [(Natural, b)]
          go p (n:ns) n' (x,d)
            | n' < n && d == 0 = go p (n:ns) (n'+1) (divMod x p)
            | n' == n = do b <- fromNatural d
                           rem <- go p ns (n'+1) (divMod x p)
                           return ((n,b) : rem)
            | otherwise = Nothing
          go _ [] _ (0,0) = Just []
          go _ _ _ _ = Nothing
  enumerate = case upperBound (Proxy :: Proxy b) of
                Just p ->
                  let as = map ((p^) . fst) (enumerate :: [(Natural, a)])
                      bs = map fst (enumerate :: [(Natural, b)])
                      n = length as
                  in map ((\n -> (n, fromNatural' n)) . sum . zipWith (*) as) (cartPow bs n)
    where cartPow xs 0 = [[]]
          cartPow xs n = liftA2 (:) xs (cartPow xs (n-1))
  upperBound Proxy = liftA2 (^) (upperBound (Proxy :: Proxy b))
                                (upperBound (Proxy :: Proxy a))
  dense Proxy = dense (Proxy :: Proxy a) && dense (Proxy :: Proxy b)
instance Countable a => Countable [a] where
  toNatural xs = case upperBound (Proxy :: Proxy a) of
                       Just p -> foldl' ((+) . ((p+1)*)) 0 (map (succ . toNatural) xs)
  fromNatural x = case upperBound (Proxy :: Proxy a) of
                       Just p -> sequence . map go $ digits (p+1) x []
    where digits p 0 ds = ds
          digits p n ds = case divMod n p of (n',d) -> digits p n' (d : ds)
          go 0 = Nothing
          go a = fromNatural (a - 1)
  enumerate = map (\x -> (toNatural x, x)) $ concat enumerate'
    where xs = map snd enumerate
          enumerate' = [[]] : [[(y:ys) | y <- xs, ys <- yss] | yss <- enumerate']
  upperBound Proxy = Nothing
  dense Proxy = False

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

cantorPair :: Integral a => (a,a) -> a
cantorPair (x, y) = ((x + y) * (x + y + 1)) `div` 2 + y

cantorUnpair :: Integral a => a -> (a,a)
cantorUnpair z = let xy1 = fromInteger . squareRoot . toInteger $ 2*z
                     t1 = xy1 * (xy1+1) `div` 2
                     t2 = xy1 * (xy1-1) `div` 2
                     y1 = z - t1
                     y2 = z - t2
                 in if z >= t1 then (xy1-y1,y1) else (xy1-1-y2,y2)