{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}

-- | Certified total operations on 'Maybe' values.
module Data.Maybe.Dependent.Internal (
    Maybe (..),
    maybe,
    fromMaybe,
    isJust,
    isNothing,
    fmapMaybe,
    maybeToList,
    listToMaybe,
    mapMaybe,
    catMaybes,
) where

import Prelude (Bool (..), Maybe (..))

-- | Eliminate a 'Maybe' value with a default and a handler for 'Just'.
maybe :: forall a b. b -> (a -> b) -> Maybe a -> b
maybe def _ Nothing = def
maybe _ f (Just x) = f x

-- | Extract the payload of 'Just' or return the supplied default value.
fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def Nothing = def
fromMaybe _ (Just x) = x

-- | Test whether a 'Maybe' value uses 'Just'.
isJust :: forall a. Maybe a -> Bool
isJust Nothing = False
isJust (Just _) = True

-- | Test whether a 'Maybe' value is 'Nothing'.
isNothing :: forall a. Maybe a -> Bool
isNothing Nothing = True
isNothing (Just _) = False

-- | Apply a function to the payload of 'Just' and preserve 'Nothing'.
fmapMaybe :: forall a b. (a -> b) -> Maybe a -> Maybe b
fmapMaybe _ Nothing = Nothing
fmapMaybe f (Just x) = Just (f x)

-- | Convert 'Nothing' to the empty list and 'Just' to a singleton list.
maybeToList :: forall a. Maybe a -> [a]
maybeToList Nothing = []
maybeToList (Just x) = [x]

-- | Return 'Nothing' on the empty list and 'Just' of the head otherwise.
listToMaybe :: forall a. [a] -> Maybe a
listToMaybe [] = Nothing
listToMaybe (x : _) = Just x

-- | Apply a partial function across a list and keep the 'Just' results.
mapMaybe :: forall a b. (a -> Maybe b) -> [a] -> [b]
mapMaybe _ [] = []
mapMaybe f (x : xs) = case f x of
    Nothing -> mapMaybe f xs
    Just y -> y : mapMaybe f xs

-- | Collect all 'Just' payloads from a list of 'Maybe' values.
catMaybes :: forall a. [Maybe a] -> [a]
catMaybes [] = []
catMaybes (Nothing : xs) = catMaybes xs
catMaybes (Just x : xs) = x : catMaybes xs
