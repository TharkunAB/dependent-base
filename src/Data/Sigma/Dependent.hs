{-# LANGUAGE DependentTypes #-}

-- | Retained dependent pairs ('Sigma') and projection/mapping combinators.
module Data.Sigma.Dependent
  ( Sigma (..)
  , first
  , second
  , withSigma
  , mapSigma
  , mapSigmaSecond
  , currySigma
  , uncurrySigma
  ) where

import Data.Kind (Type)
import GHC.Matchability (U)
import GHC.Sigma (Sigma (..), first, second, withSigma)
import Prelude ()

-- | Map an ordinary function over the first component and a dependent function
-- over the second component of a 'Sigma' pair.
mapSigma
  :: forall {a} {b} (p :: a %U -> Type) (q :: b %U -> Type).
     foreach (f :: a -> b)
  -> (foreach (x :: a) -> p x -> q (f x))
  -> Sigma a p
  -> Sigma b q
mapSigma f g (Pair x px) = Pair (f x) (g x px)

-- | Transform the payload of a 'Sigma' pair while keeping the same witness.
mapSigmaSecond
  :: forall {a} (p :: a %U -> Type) (q :: a %U -> Type).
     (foreach (x :: a) -> p x -> q x)
  -> Sigma a p
  -> Sigma a q
mapSigmaSecond g (Pair x px) = Pair x (g x px)

-- | Convert a function on a 'Sigma' pair into a curried dependent function.
currySigma
  :: forall {a} (p :: a %U -> Type) {r}.
     (Sigma a p -> r)
  -> foreach (x :: a)
  -> p x
  -> r
currySigma k x px = k (Pair x px)

-- | Convert a curried dependent function into a function on a 'Sigma' pair.
uncurrySigma
  :: forall {a} (p :: a %U -> Type) {r}.
     (foreach (x :: a) -> p x -> r)
  -> Sigma a p
  -> r
uncurrySigma k (Pair x px) = k x px
