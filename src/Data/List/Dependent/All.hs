{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}

{- | Indexed universal ('All') and existential ('Any') list predicates and
typed context membership ('Elem').
-}
module Data.List.Dependent.All (
    All (..),
    Any (..),
    Elem,
    lookupAll,
    tabulateAll,
    mapAll,
    mapAny,
    allAppend,
    splitAllAppend,
    decAll,
    decAny,
    decElem,
) where

import Data.Decision (Dec (No, Yes), DecEq (decEq))
import Data.Kind (Type)
import Data.Type.Equality.Dependent ((:~:) (Refl))
import GHC.Matchability (Matchability)
import Prelude ((++))

-- | Evidence that predicate @p@ holds for every element of a list.
type All :: forall {a} {m :: Matchability}. (a %m -> Type) -> [a] -> Type
data All p xs where
    AllNil :: forall {a} {m :: Matchability} {p :: a %m -> Type}. All p '[]
    AllCons ::
        forall {a} {m :: Matchability} {p :: a %m -> Type} {x :: a} {xs :: [a]}.
        p x -> All p xs -> All p (x : xs)

-- | Evidence that predicate @p@ holds for at least one element of a list.
type Any :: forall {a} {m :: Matchability}. (a %m -> Type) -> [a] -> Type
data Any p xs where
    Here ::
        forall {a} {m :: Matchability} {p :: a %m -> Type} {x :: a} {xs :: [a]}.
        p x -> Any p (x : xs)
    There ::
        forall {a} {m :: Matchability} {p :: a %m -> Type} {x :: a} {xs :: [a]}.
        Any p xs -> Any p (x : xs)

-- | Typed list membership: @Elem x xs@ witnesses an occurrence of @x@ in @xs@.
type Elem :: forall {a}. a -> [a] -> Type
type Elem x xs = Any ((:~:) x) xs

-- | Extract the predicate evidence at a membership position 'Elem'.
lookupAll ::
    forall {a} {m :: Matchability} {p :: a %m -> Type} {x :: a} {xs :: [a]}.
    All p xs -> Elem x xs -> p x
lookupAll AllNil ix = case ix of {}
lookupAll (AllCons px _) (Here Refl) = px
lookupAll (AllCons _ pxs) (There i) = lookupAll pxs i

-- | Build @All p xs@ when @p@ holds at every membership position of @xs@.
tabulateAll ::
    forall {a} {m :: Matchability} {p :: a %m -> Type}.
    foreach (xs :: [a]) ->
    (forall (x :: a). Elem x xs -> p x) ->
    All p xs
tabulateAll [] _ = AllNil
tabulateAll (x : xs) f = AllCons (f @x (Here Refl)) (tabulateAll xs (\i -> f (There i)))

-- | Transform universal list evidence pointwise across the list.
mapAll ::
    forall
        {a}
        {m1 :: Matchability}
        {m2 :: Matchability}
        {p :: a %m1 -> Type}
        {q :: a %m2 -> Type}
        {xs :: [a]}.
    (forall {x :: a}. p x -> q x) ->
    All p xs ->
    All q xs
mapAll _ AllNil = AllNil
mapAll f (AllCons px pxs) = AllCons (f px) (mapAll f pxs)

-- | Transform existential list evidence at the selected element.
mapAny ::
    forall
        {a}
        {m1 :: Matchability}
        {m2 :: Matchability}
        {p :: a %m1 -> Type}
        {q :: a %m2 -> Type}
        {xs :: [a]}.
    (forall {x :: a}. p x -> q x) ->
    Any p xs ->
    Any q xs
mapAny f (Here px) = Here (f px)
mapAny f (There ix) = There (mapAny f ix)

-- | Combine universal evidence across two concatenated lists.
allAppend ::
    forall {a} {m :: Matchability} {p :: a %m -> Type} {xs :: [a]} {ys :: [a]}.
    All p xs -> All p ys -> All p (xs ++ ys)
allAppend AllNil pys = pys
allAppend (AllCons px pxs) pys = AllCons px (allAppend pxs pys)

-- | Split universal evidence for @xs ++ ys@ into evidence for @xs@ and @ys@.
splitAllAppend ::
    forall {a} {m :: Matchability} {p :: a %m -> Type} (ys :: [a]).
    foreach (xs :: [a]) ->
    All p (xs ++ ys) -> (All p xs, All p ys)
splitAllAppend [] pys = (AllNil, pys)
splitAllAppend (_ : xs) (AllCons px rest) =
    case splitAllAppend @ys xs rest of
        (pxs, pys) -> (AllCons px pxs, pys)

-- | Decide whether @All p xs@ holds given a decision procedure for @p@.
decAll ::
    forall {a} {m :: Matchability} {p :: a %m -> Type}.
    (foreach (x :: a) -> Dec (p x)) ->
    foreach (xs :: [a]) ->
    Dec (All p xs)
decAll _ [] = Yes AllNil
decAll decP (x : xs) = case decP x of
    No notPx -> No (\case AllCons px _ -> notPx px)
    Yes px -> case decAll decP xs of
        Yes pxs -> Yes (AllCons px pxs)
        No notPxs -> No (\case AllCons _ pxs -> notPxs pxs)

-- | Decide whether @Any p xs@ holds given a decision procedure for @p@.
decAny ::
    forall {a} {m :: Matchability} {p :: a %m -> Type}.
    (foreach (x :: a) -> Dec (p x)) ->
    foreach (xs :: [a]) ->
    Dec (Any p xs)
decAny _ [] = No (\case {})
decAny decP (x : xs) = case decP x of
    Yes px -> Yes (Here px)
    No notPx -> case decAny decP xs of
        Yes ix -> Yes (There ix)
        No notAny ->
            No
                ( \case
                    Here px -> notPx px
                    There ix -> notAny ix
                )

-- | Decide whether @x@ occurs in @xs@ when @a@ has decidable equality.
decElem ::
    forall {a}.
    (DecEq a) =>
    foreach (x :: a) ->
    foreach (xs :: [a]) ->
    Dec (Elem x xs)
decElem _ [] = No (\case {})
decElem x (y : ys) = case decEq x y of
    Yes eq -> Yes (Here eq)
    No notEq -> case decElem x ys of
        Yes ix -> Yes (There ix)
        No notAny ->
            No
                ( \case
                    Here eq -> notEq eq
                    There ix -> notAny ix
                )
