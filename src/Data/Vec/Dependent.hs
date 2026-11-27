{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE ListTuplePuns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}

-- | Length-indexed vectors ('Vec'), safe indexing by 'Fin', and list adapters.
module Data.Vec.Dependent (
    Vec (..),
    SomeVec,
    headVec,
    tailVec,
    snocVec,
    initVec,
    lastVec,
    appendVec,
    mapVec,
    zipVec,
    zipWithVec,
    replicateVec,
    lookupVec,
    mkFinVec,
    tabulateVec,
    updateAtVec,
    reverseVec,
    foldrVec,
    toListVec,
    fromListVec,
    fromListExact,
    packListVec,
) where

import Data.Fin.Dependent (Fin (..))
import Data.List.Dependent (size)
import Data.Nat.Dependent (Nat (..), plus)
import GHC.Sigma (Sigma (Pair))
import Prelude (Eq (..), Int, Maybe (..), Ord (..), Show, otherwise, (-))

-- | A list whose length is tracked by a Peano natural index.
data Vec a (n :: Nat) where
    VNil :: Vec a Zero
    VCons :: a -> Vec a n -> Vec a (Succ n)

deriving instance (Eq a) => Eq (Vec a n)
deriving instance (Show a) => Show (Vec a n)

-- | A runtime length paired with a vector of that length.
type SomeVec a = some (n :: Nat) | Vec a n

-- | Extract the first element of a non-empty vector.
headVec :: Vec a (Succ n) -> a
headVec (VCons x _) = x

-- | Drop the first element of a non-empty vector.
tailVec :: Vec a (Succ n) -> Vec a n
tailVec (VCons _ xs) = xs

-- | Append one element at the right end of a vector.
snocVec :: Vec a n -> a -> Vec a (Succ n)
snocVec VNil y = VCons y VNil
snocVec (VCons x xs) y = VCons x (snocVec xs y)

-- | Drop the last element of a non-empty vector.
initVec :: Vec a (Succ n) -> Vec a n
initVec (VCons _ VNil) = VNil
initVec (VCons x xs@(VCons _ _)) = VCons x (initVec xs)

-- | Extract the last element of a non-empty vector.
lastVec :: Vec a (Succ n) -> a
lastVec (VCons x VNil) = x
lastVec (VCons _ xs@(VCons _ _)) = lastVec xs

-- | Append two vectors and add their length indices.
appendVec :: Vec a n -> Vec a m -> Vec a (plus n m)
appendVec VNil ys = ys
appendVec (VCons x xs) ys = VCons x (appendVec xs ys)

-- | Apply a function to each element while preserving the length index.
mapVec :: (a -> b) -> Vec a n -> Vec b n
mapVec _ VNil = VNil
mapVec f (VCons x xs) = VCons (f x) (mapVec f xs)

-- | Pair corresponding elements of two equal-length vectors.
zipVec :: Vec a n -> Vec b n -> Vec (a, b) n
zipVec VNil VNil = VNil
zipVec (VCons x xs) (VCons y ys) = VCons (x, y) (zipVec xs ys)

-- | Combine corresponding elements of two equal-length vectors with a function.
zipWithVec :: (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
zipWithVec _ VNil VNil = VNil
zipWithVec f (VCons x xs) (VCons y ys) = VCons (f x y) (zipWithVec f xs ys)

-- | Build a vector of the requested runtime length by repeating one value.
replicateVec :: forall a. foreach (n :: Nat) -> a -> Vec a n
replicateVec Zero _ = VNil
replicateVec (Succ n) x = VCons x (replicateVec @a n x)

-- | Read the element at a checked 'Fin' position without a fallback branch.
lookupVec :: Fin n -> Vec a n -> a
lookupVec FZ (VCons x _) = x
lookupVec (FS i) (VCons _ xs) = lookupVec i xs

-- | Convert a non-negative 'Int' into a position within a vector's spine.
mkFinVec :: Vec a n -> Int -> Maybe (Fin n)
mkFinVec xs position
    | position < 0 = Nothing
    | otherwise = case xs of
        VNil -> Nothing
        VCons _ rest
            | position == 0 -> Just FZ
            | otherwise -> case mkFinVec rest (position - 1) of
                Nothing -> Nothing
                Just smaller -> Just (FS smaller)

-- | Construct a vector of length @n@ by sampling a function on @Fin n@.
tabulateVec :: foreach (n :: Nat) -> (Fin n -> a) -> Vec a n
tabulateVec Zero _ = VNil
tabulateVec (Succ n) f = VCons (f FZ) (tabulateVec n (\i -> f (FS i)))

-- | Update the element at a checked 'Fin' position in a vector.
updateAtVec :: Fin n -> (a -> a) -> Vec a n -> Vec a n
updateAtVec FZ f (VCons x xs) = VCons (f x) xs
updateAtVec (FS i) f (VCons x xs) = VCons x (updateAtVec i f xs)

-- | Reverse a vector while preserving its length index.
reverseVec :: Vec a n -> Vec a n
reverseVec VNil = VNil
reverseVec (VCons x xs) = snocVec (reverseVec xs) x

-- | Right-associative fold over a vector.
foldrVec :: (a -> b -> b) -> b -> Vec a n -> b
foldrVec _ z VNil = z
foldrVec f z (VCons x xs) = f x (foldrVec f z xs)

-- | Convert a vector to an ordinary list by dropping its length index.
toListVec :: Vec a n -> [a]
toListVec VNil = []
toListVec (VCons x xs) = x : toListVec xs

-- | Convert an ordinary list to a vector indexed by 'size'.
fromListVec :: forall a. foreach (xs :: [a]) -> Vec a (size xs)
fromListVec [] = VNil
fromListVec (x : xs) = VCons x (fromListVec @a xs)

{- | Check that an ordinary list has the requested runtime length.
See Note [Exact-length list adapter].
-}
fromListExact :: foreach (n :: Nat) -> [a] -> Maybe (Vec a n)
fromListExact Zero [] = Just VNil
fromListExact Zero (_ : _) = Nothing
fromListExact (Succ _) [] = Nothing
fromListExact (Succ n) (x : xs) = case fromListExact n xs of
    Nothing -> Nothing
    Just rest -> Just (VCons x rest)

-- | Pair an ordinary list's runtime length with its indexed vector.
packListVec :: [a] -> SomeVec a
packListVec xs = Pair (size xs) (fromListVec xs)

{- Note [Exact-length list adapter]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Function 'fromListExact' checks a list spine against a runtime 'Nat' bound.
When the bound is 'Zero' and the list is non-empty, 'fromListExact' returns
'Nothing' without evaluating the head or tail. When the lengths match,
'fromListExact' returns 'Just' without evaluating the list elements.

Function 'packListVec' accepts a list of any length. Both 'Pair' fields stay
lazy until the caller inspects the length or the vector spine.
-}
