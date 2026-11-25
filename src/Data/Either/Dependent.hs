{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}

-- | Certified 'Either' operations, involution proofs, and sum associativity.
module Data.Either.Dependent
  ( Either (..)
  , either
  , isLeft
  , isRight
  , bimapEither
  , mapLeft
  , mapRight
  , swapEither
  , assocEitherTo
  , assocEitherFrom
  , swapEitherInvolutive
  , isLeftLeft
  , isRightRight
  , mapLeftId
  , mapRightId
  , sumCommIso
  , sumAssocIso
  ) where

import Data.Either.Dependent.Internal
  ( Either (..)
  , assocEitherFrom
  , assocEitherTo
  , bimapEither
  , either
  , isLeft
  , isRight
  , mapLeft
  , mapRight
  , swapEither
  )
import Data.Tuple.Dependent.Internal (Iso (MkIso))
import Data.Type.Equality.Dependent ((:~:) (Refl))
import Prelude (Bool (True), id)

-- | Swapping an 'Either' sum twice returns the original value.
swapEitherInvolutive
  :: forall a b.
     foreach (e :: Either a b)
  -> swapEither (swapEither e) :~: e
swapEitherInvolutive (Left _)  = Refl
swapEitherInvolutive (Right _) = Refl

-- | Every 'Left' value satisfies 'isLeft'.
isLeftLeft :: forall a b. foreach (x :: a) -> isLeft (Left @a @b x) :~: True
isLeftLeft _ = Refl

-- | Every 'Right' value satisfies 'isRight'.
isRightRight :: forall a b. foreach (y :: b) -> isRight (Right @a @b y) :~: True
isRightRight _ = Refl

-- | Mapping 'id' over the 'Left' branch of 'Either' preserves the input.
mapLeftId
  :: forall a b.
     foreach (e :: Either a b)
  -> mapLeft id e :~: e
mapLeftId (Left _)  = Refl
mapLeftId (Right _) = Refl

-- | Mapping 'id' over the 'Right' branch of 'Either' preserves the input.
mapRightId
  :: forall a b.
     foreach (e :: Either a b)
  -> mapRight id e :~: e
mapRightId (Left _)  = Refl
mapRightId (Right _) = Refl

-- | Certified commutativity isomorphism for 'Either'.
sumCommIso :: forall a b. Iso (Either a b) (Either b a)
sumCommIso = MkIso swapEither swapEither swapEitherInvolutive swapEitherInvolutive

-- | Left-to-right-to-left round-trip law for 'Either' associativity.
assocEitherFromTo
  :: forall a b c.
     foreach (e :: Either (Either a b) c)
  -> assocEitherFrom (assocEitherTo e) :~: e
assocEitherFromTo (Left (Left _))  = Refl
assocEitherFromTo (Left (Right _)) = Refl
assocEitherFromTo (Right _)        = Refl

-- | Right-to-left-to-right round-trip law for 'Either' associativity.
assocEitherToFrom
  :: forall a b c.
     foreach (e :: Either a (Either b c))
  -> assocEitherTo (assocEitherFrom e) :~: e
assocEitherToFrom (Left _)          = Refl
assocEitherToFrom (Right (Left _))  = Refl
assocEitherToFrom (Right (Right _)) = Refl

-- | Certified associativity isomorphism for 'Either'.
sumAssocIso :: forall a b c. Iso (Either (Either a b) c) (Either a (Either b c))
sumAssocIso = MkIso assocEitherTo assocEitherFrom assocEitherFromTo assocEitherToFrom
