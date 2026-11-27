{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}

-- | Certified total operations on pairs and isomorphism witnesses.
module Data.Tuple.Dependent.Internal (
    fst,
    snd,
    swap,
    curry,
    uncurry,
    bimapPair,
    firstPair,
    secondPair,
    assocPairTo,
    assocPairFrom,
    unitPairLTo,
    unitPairLFrom,
    unitPairRTo,
    unitPairRFrom,
    distribPairEitherTo,
    distribPairEitherFrom,
    distribEitherPairTo,
    distribEitherPairFrom,
    Iso (..),
) where

import Data.Tuple (curry, fst, snd, swap, uncurry)
import Data.Type.Equality.Dependent ((:~:))
import Prelude (Either (..))

-- | Apply two functions independently to the components of a pair.
bimapPair :: forall a b c d. (a -> c) -> (b -> d) -> (a, b) -> (c, d)
bimapPair f g (x, y) = (f x, g y)

-- | Transform the first component of a pair and preserve the second.
firstPair :: forall a b c. (a -> c) -> (a, b) -> (c, b)
firstPair f (x, y) = (f x, y)

-- | Transform the second component of a pair and preserve the first.
secondPair :: forall a b d. (b -> d) -> (a, b) -> (a, d)
secondPair g (x, y) = (x, g y)

-- | Reassociate a left-nested pair to the right.
assocPairTo :: forall a b c. ((a, b), c) -> (a, (b, c))
assocPairTo ((x, y), z) = (x, (y, z))

-- | Reassociate a right-nested pair to the left.
assocPairFrom :: forall a b c. (a, (b, c)) -> ((a, b), c)
assocPairFrom (x, (y, z)) = ((x, y), z)

-- | Drop a leading unit component from a pair.
unitPairLTo :: forall a. ((), a) -> a
unitPairLTo ((), x) = x

-- | Pair a value with a leading unit component.
unitPairLFrom :: forall a. a -> ((), a)
unitPairLFrom x = ((), x)

-- | Drop a trailing unit component from a pair.
unitPairRTo :: forall a. (a, ()) -> a
unitPairRTo (x, ()) = x

-- | Pair a value with a trailing unit component.
unitPairRFrom :: forall a. a -> (a, ())
unitPairRFrom x = (x, ())

-- | Distribute a left factor over an 'Either' sum.
distribPairEitherTo :: forall a b c. (a, Either b c) -> Either (a, b) (a, c)
distribPairEitherTo (x, Left y) = Left (x, y)
distribPairEitherTo (x, Right z) = Right (x, z)

-- | Factor a shared left component out of an 'Either' sum of pairs.
distribPairEitherFrom :: forall a b c. Either (a, b) (a, c) -> (a, Either b c)
distribPairEitherFrom (Left (x, y)) = (x, Left y)
distribPairEitherFrom (Right (x, z)) = (x, Right z)

-- | Distribute a right factor over an 'Either' sum.
distribEitherPairTo :: forall a b c. (Either a b, c) -> Either (a, c) (b, c)
distribEitherPairTo (Left x, z) = Left (x, z)
distribEitherPairTo (Right y, z) = Right (y, z)

-- | Factor a shared right component out of an 'Either' sum of pairs.
distribEitherPairFrom :: forall a b c. Either (a, c) (b, c) -> (Either a b, c)
distribEitherPairFrom (Left (x, z)) = (Left x, z)
distribEitherPairFrom (Right (y, z)) = (Right y, z)

{- | A certified bijection between types @a@ and @b@ with round-trip proofs on
both sides.
-}
data Iso a b where
    MkIso ::
        foreach (to :: a -> b) ->
        foreach (from :: b -> a) ->
        (foreach (x :: a) -> from (to x) :~: x) ->
        (foreach (y :: b) -> to (from y) :~: y) ->
        Iso a b
