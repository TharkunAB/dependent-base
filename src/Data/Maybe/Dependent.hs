{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}

-- | Certified 'Maybe' operations and their functor and round-trip laws.
module Data.Maybe.Dependent
  ( Maybe (..)
  , maybe
  , fromMaybe
  , isJust
  , isNothing
  , fmapMaybe
  , maybeToList
  , listToMaybe
  , mapMaybe
  , catMaybes
  , fmapMaybeId
  , fmapMaybeCompose
  , isJustJust
  , listToMaybeSingleton
  , listToMaybeMaybeToList
  ) where

import Data.Function.Dependent ((.))
import Data.Maybe.Dependent.Internal
  ( Maybe (..)
  , catMaybes
  , fmapMaybe
  , fromMaybe
  , isJust
  , isNothing
  , listToMaybe
  , mapMaybe
  , maybe
  , maybeToList
  )
import Data.Type.Equality.Dependent ((:~:) (Refl))
import Prelude (Bool (True), id)

-- | Mapping 'id' over a 'Maybe' value returns the input unchanged.
fmapMaybeId :: forall a. foreach (mx :: Maybe a) -> fmapMaybe id mx :~: mx
fmapMaybeId Nothing  = Refl
fmapMaybeId (Just _) = Refl

-- | Mapping a composed function over 'Maybe' agrees with mapping sequentially.
fmapMaybeCompose
  :: forall a b c.
     foreach (g :: b -> c)
  -> foreach (f :: a -> b)
  -> foreach (mx :: Maybe a)
  -> fmapMaybe (g . f) mx :~: fmapMaybe g (fmapMaybe f mx)
fmapMaybeCompose _ _ Nothing  = Refl
fmapMaybeCompose _ _ (Just _) = Refl

-- | Every 'Just' value satisfies 'isJust'.
isJustJust :: forall a. foreach (x :: a) -> isJust (Just x) :~: True
isJustJust _ = Refl

-- | Converting a singleton list with 'listToMaybe' recovers its element.
listToMaybeSingleton :: forall a. foreach (x :: a) -> listToMaybe '[x] :~: Just x
listToMaybeSingleton _ = Refl

-- | Round-tripping a 'Maybe' value through 'maybeToList' and 'listToMaybe' is the identity.
listToMaybeMaybeToList
  :: forall a.
     foreach (mx :: Maybe a)
  -> listToMaybe (maybeToList mx) :~: mx
listToMaybeMaybeToList Nothing  = Refl
listToMaybeMaybeToList (Just _) = Refl
