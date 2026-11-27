{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}

-- | Length, concatenation, functor, and reversal laws for ordinary lists.
module Data.List.Dependent.Properties (
    consCong,
    appendNilR,
    appendAssoc,
    mapId,
    mapCompose,
    mapAppend,
    lengthAppend,
    lengthAppendList,
    lengthMap,
    lengthZip,
    lengthZipWith,
    lengthZipMap,
    lengthMapZip,
    lengthReverse,
    lengthShunt,
    lengthReverseShunt,
    shuntAppend,
    reverseShuntInvolutive,
    lengthTakeSize,
) where

import Data.Function.Dependent ((.))
import Data.List.Dependent (
    append,
    map,
    reverse,
    reverseShunt,
    shunt,
    size,
    takeSize,
    zip,
    zipWith,
    (++),
 )
import Data.Nat.Dependent (Nat (..), minSize, plus)
import Data.Nat.Dependent.Properties (congSucc, plusSucc, plusZero)
import Data.Type.Equality.Dependent (cong, sym, trans, (:~:) (Refl))
import GHC.Internal.List qualified as List
import Prelude (id)

-- | Congruence in the tail of '(:)' at a fixed head element.
consCong ::
    forall {a}.
    foreach (x :: a) ->
    forall {xs :: [a]} {ys :: [a]}.
    xs :~: ys -> (x : xs) :~: (x : ys)
consCong x eq = cong (x :) eq

-- | Right identity of '(++)'.
appendNilR :: forall a. foreach (xs :: [a]) -> (xs ++ '[]) :~: xs
appendNilR [] = Refl
appendNilR (x : xs) = consCong x (appendNilR xs)

-- | Associativity of '(++)'.
appendAssoc ::
    forall a.
    foreach (xs :: [a]) ->
    foreach (ys :: [a]) ->
    foreach (zs :: [a]) ->
    ((xs ++ ys) ++ zs) :~: (xs ++ (ys ++ zs))
appendAssoc [] _ _ = Refl
appendAssoc (x : xs) ys zs = consCong x (appendAssoc xs ys zs)

-- | Mapping 'id' over a list returns the input list.
mapId :: forall a. foreach (xs :: [a]) -> map id xs :~: xs
mapId [] = Refl
mapId (x : xs) = consCong x (mapId xs)

-- | Mapping a composed function over a list agrees with sequential 'map'.
mapCompose ::
    forall a b c.
    foreach (g :: b -> c) ->
    foreach (f :: a -> b) ->
    foreach (xs :: [a]) ->
    map (g . f) xs :~: map g (map f xs)
mapCompose _ _ [] = Refl
mapCompose g f (_ : xs) = case mapCompose g f xs of
    Refl -> Refl

-- | 'map' distributes over '(++)'.
mapAppend ::
    forall a b.
    foreach (f :: a -> b) ->
    foreach (xs :: [a]) ->
    foreach (ys :: [a]) ->
    map f (xs ++ ys) :~: (map f xs ++ map f ys)
mapAppend _ [] _ = Refl
mapAppend f (x : xs) ys = consCong (f x) (mapAppend f xs ys)

-- | The length of '(++)' is the sum of the input lengths.
lengthAppend ::
    forall a.
    foreach (xs :: [a]) ->
    foreach (ys :: [a]) ->
    size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppend [] _ = Refl
lengthAppend (_ : xs) ys = congSucc (lengthAppend xs ys)

-- | The length of 'append' is the sum of the input lengths.
lengthAppendList ::
    forall a.
    foreach (xs :: [a]) ->
    foreach (ys :: [a]) ->
    size (append xs ys) :~: plus (size xs) (size ys)
lengthAppendList [] _ = Refl
lengthAppendList (_ : xs) ys = congSucc (lengthAppendList xs ys)

-- | 'map' preserves the number of list cells.
lengthMap ::
    forall a b.
    foreach (f :: a -> b) ->
    foreach (xs :: [a]) ->
    size (map f xs) :~: size xs
lengthMap f = \case
    [] -> Refl
    _ : xs -> congSucc (lengthMap f xs)

-- | 'zip' produces a list whose length is the minimum of the input lengths.
lengthZip ::
    forall a b.
    foreach (xs :: [a]) ->
    foreach (ys :: [b]) ->
    size (zip xs ys) :~: minSize (size xs) (size ys)
lengthZip [] _ = Refl
lengthZip (_ : _) [] = Refl
lengthZip (_ : xs) (_ : ys) = case lengthZip xs ys of
    Refl -> Refl

-- | 'zipWith' produces a list whose length is the minimum of the input lengths.
lengthZipWith ::
    forall a b c.
    foreach (f :: a -> b -> c) ->
    foreach (xs :: [a]) ->
    foreach (ys :: [b]) ->
    size (zipWith f xs ys) :~: minSize (size xs) (size ys)
lengthZipWith _ [] _ = Refl
lengthZipWith _ (_ : _) [] = Refl
lengthZipWith f (_ : xs) (_ : ys) = case lengthZipWith f xs ys of
    Refl -> Refl

-- | Mapping the left list before 'zipWith' preserves the shorter input length.
lengthZipMap ::
    forall a b c d.
    foreach (pre :: a -> b) ->
    foreach (combine :: b -> c -> d) ->
    foreach (xs :: [a]) ->
    foreach (ys :: [c]) ->
    size (zipWith combine (map pre xs) ys) :~: minSize (size xs) (size ys)
lengthZipMap _ _ [] _ = Refl
lengthZipMap _ _ (_ : _) [] = Refl
lengthZipMap pre combine (_ : xs) (_ : ys) = case lengthZipMap pre combine xs ys of
    Refl -> Refl

-- | Mapping over 'zip' preserves the shorter input length.
{-# NOINLINE lengthMapZip #-}
lengthMapZip ::
    forall a b c.
    foreach (f :: (a, b) -> c) ->
    foreach (xs :: [a]) ->
    foreach (ys :: [b]) ->
    size (map f (zip xs ys)) :~: minSize (size xs) (size ys)
lengthMapZip f xs ys = case lengthMap f (zip xs ys) of
    Refl -> lengthZip xs ys

-- | Length of the internal 'List.reverseOnto' worker.
lengthReverseOnto ::
    forall a.
    foreach (xs :: [a]) ->
    foreach (acc :: [a]) ->
    size (List.reverseOnto xs acc) :~: plus (size xs) (size acc)
lengthReverseOnto [] _ = Refl
lengthReverseOnto (x : xs) acc =
    trans (lengthReverseOnto xs (x : acc)) (plusSucc (size xs) (size acc))

-- | Reversing a list with 'reverse' preserves its length.
lengthReverse :: forall a. foreach (xs :: [a]) -> size (reverse xs) :~: size xs
lengthReverse xs = trans (lengthReverseOnto xs []) (plusZero (size xs))

-- | 'shunt' adds the length of the input list to the accumulator length.
lengthShunt ::
    forall a.
    foreach (xs :: [a]) ->
    foreach (acc :: [a]) ->
    size (shunt xs acc) :~: plus (size xs) (size acc)
lengthShunt [] _ = Refl
lengthShunt (x : xs) acc =
    trans (lengthShunt xs (x : acc)) (plusSucc (size xs) (size acc))

-- | 'reverseShunt' preserves the length of a list.
lengthReverseShunt :: forall a. foreach (xs :: [a]) -> size (reverseShunt xs) :~: size xs
lengthReverseShunt xs = trans (lengthShunt xs []) (plusZero (size xs))

-- | Shunting @xs@ onto @ys@ reverses @xs@ and appends @ys@.
shuntAppend ::
    forall a.
    foreach (xs :: [a]) ->
    foreach (ys :: [a]) ->
    shunt xs ys :~: (reverseShunt xs ++ ys)
shuntAppend [] _ = Refl
shuntAppend (x : xs) ys = case shuntAppend xs [x] of
    Refl ->
        trans
            (shuntAppend xs (x : ys))
            (sym (appendAssoc (reverseShunt xs) [x] ys))

shuntInvAux ::
    forall a.
    foreach (xs :: [a]) ->
    foreach (ys :: [a]) ->
    shunt (shunt xs ys) '[] :~: (shunt ys '[] ++ xs)
shuntInvAux [] ys = sym (appendNilR (shunt ys []))
shuntInvAux (x : xs) ys = case shuntAppend ys [x] of
    Refl -> case shuntInvAux xs (x : ys) of
        Refl -> case appendAssoc (shunt ys []) [x] xs of
            Refl -> Refl

-- | Reversing a list twice with 'reverseShunt' returns the original list.
reverseShuntInvolutive :: forall a. foreach (xs :: [a]) -> reverseShunt (reverseShunt xs) :~: xs
reverseShuntInvolutive xs = shuntInvAux xs []

-- | Prefix length under 'takeSize' is the smaller of the bound and input length.
lengthTakeSize ::
    forall a.
    foreach (n :: Nat) ->
    foreach (xs :: [a]) ->
    size (takeSize n xs) :~: minSize n (size xs)
lengthTakeSize Zero _ = Refl
lengthTakeSize (Succ _) [] = Refl
lengthTakeSize (Succ n) (_ : xs) = congSucc (lengthTakeSize n xs)
