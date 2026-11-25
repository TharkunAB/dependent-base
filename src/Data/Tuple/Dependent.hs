{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}

-- | Certified pair projections, 'Iso' combinators, and semiring product bijections.
module Data.Tuple.Dependent
  ( fst
  , snd
  , swap
  , curry
  , uncurry
  , bimapPair
  , firstPair
  , secondPair
  , swapInvolutive
  , pairEta
  , Iso (..)
  , isoRefl
  , isoSym
  , isoTrans
  , composeLeft
  , prodCommIso
  , prodAssocIso
  , prodUnitLIso
  , prodUnitRIso
  , elimProdZeroL
  , elimProdZeroR
  , prodDistribEitherIso
  , prodDistribEitherLIso
  ) where

import Data.Function.Dependent ((.))
import Data.Tuple.Dependent.Internal
  ( Iso (..)
  , assocPairFrom
  , assocPairTo
  , bimapPair
  , curry
  , distribEitherPairFrom
  , distribEitherPairTo
  , distribPairEitherFrom
  , distribPairEitherTo
  , firstPair
  , fst
  , secondPair
  , snd
  , swap
  , uncurry
  , unitPairLFrom
  , unitPairLTo
  , unitPairRFrom
  , unitPairRTo
  )
import Data.Type.Equality.Dependent ((:~:) (Refl), cong, trans)
import Data.Void (Void, absurd)
import Prelude (Either (..), id)

-- | Swapping a pair twice returns the original pair.
swapInvolutive :: forall a b. foreach (p :: (a, b)) -> swap (swap p) :~: p
swapInvolutive (_, _) = Refl

-- | Rebuilding a pair from its 'fst' and 'snd' projections returns the pair.
pairEta :: forall a b. foreach (p :: (a, b)) -> '(fst p, snd p) :~: p
pairEta (_, _) = Refl

-- | Reflexivity of type isomorphism.
isoRefl :: forall a. Iso a a
isoRefl = MkIso id id (\_ -> Refl) (\_ -> Refl)

-- | Symmetry of type isomorphism.
isoSym :: forall a b. Iso a b -> Iso b a
isoSym (MkIso to from fromTo toFrom) = MkIso from to toFrom fromTo

-- | Compose two round-trip laws using dependent function composition '(.)'.
composeLeft
  :: forall {a} {b} {c}.
     foreach (f :: a -> b)
  -> foreach (g :: b -> a)
  -> foreach (h :: b -> c)
  -> foreach (k :: c -> b)
  -> (foreach (x :: a) -> g (f x) :~: x)
  -> (foreach (y :: b) -> k (h y) :~: y)
  -> foreach (x :: a)
  -> g (k (h (f x))) :~: x
composeLeft f g _ _ gf kh x = trans (cong g ((kh . f) x)) (gf x)

-- | Transitivity of type isomorphism via dependent '(.)'.
isoTrans :: forall a b c. Iso a b -> Iso b c -> Iso a c
isoTrans (MkIso f g gf fg) (MkIso h k kh hk) =
  MkIso @a @c (h . f) (g . k)
    (composeLeft f g h k gf kh)
    (composeLeft k h g f hk fg)

-- | Commutativity of product types: @(a, b)@ is isomorphic to @(b, a)@.
prodCommIso :: forall a b. Iso (a, b) (b, a)
prodCommIso = MkIso swap swap swapInvolutive swapInvolutive

assocPairFromTo
  :: forall a b c.
     foreach (p :: ((a, b), c))
  -> assocPairFrom (assocPairTo p) :~: p
assocPairFromTo ((_, _), _) = Refl

assocPairToFrom
  :: forall a b c.
     foreach (p :: (a, (b, c)))
  -> assocPairTo (assocPairFrom p) :~: p
assocPairToFrom (_, (_, _)) = Refl

-- | Associativity of product types: @((a, b), c)@ is isomorphic to @(a, (b, c))@.
prodAssocIso :: forall a b c. Iso ((a, b), c) (a, (b, c))
prodAssocIso = MkIso assocPairTo assocPairFrom assocPairFromTo assocPairToFrom

unitPairLFromTo :: forall a. foreach (p :: ((), a)) -> unitPairLFrom (unitPairLTo p) :~: p
unitPairLFromTo ((), _) = Refl

unitPairLToFrom :: forall a. foreach (x :: a) -> unitPairLTo (unitPairLFrom x) :~: x
unitPairLToFrom _ = Refl

-- | Left unit of product types: @((), a)@ is isomorphic to @a@.
prodUnitLIso :: forall a. Iso ((), a) a
prodUnitLIso = MkIso unitPairLTo unitPairLFrom unitPairLFromTo unitPairLToFrom

unitPairRFromTo :: forall a. foreach (p :: (a, ())) -> unitPairRFrom (unitPairRTo p) :~: p
unitPairRFromTo (_, ()) = Refl

unitPairRToFrom :: forall a. foreach (x :: a) -> unitPairRTo (unitPairRFrom x) :~: x
unitPairRToFrom _ = Refl

-- | Right unit of product types: @(a, ())@ is isomorphic to @a@.
prodUnitRIso :: forall a. Iso (a, ()) a
prodUnitRIso = MkIso unitPairRTo unitPairRFrom unitPairRFromTo unitPairRToFrom

-- | Left annihilation of product types by 'Void'.
elimProdZeroL :: forall a b. (Void, a) -> b
elimProdZeroL (v, _) = absurd v

-- | Right annihilation of product types by 'Void'.
elimProdZeroR :: forall a b. (a, Void) -> b
elimProdZeroR (_, v) = absurd v

distribPairEitherFromTo
  :: forall a b c.
     foreach (p :: (a, Either b c))
  -> distribPairEitherFrom (distribPairEitherTo p) :~: p
distribPairEitherFromTo (_, Left _)  = Refl
distribPairEitherFromTo (_, Right _) = Refl

distribPairEitherToFrom
  :: forall a b c.
     foreach (s :: Either (a, b) (a, c))
  -> distribPairEitherTo (distribPairEitherFrom s) :~: s
distribPairEitherToFrom (Left (_, _))  = Refl
distribPairEitherToFrom (Right (_, _)) = Refl

-- | Left distributivity of products over 'Either' sums.
prodDistribEitherIso :: forall a b c. Iso (a, Either b c) (Either (a, b) (a, c))
prodDistribEitherIso =
  MkIso
    distribPairEitherTo
    distribPairEitherFrom
    distribPairEitherFromTo
    distribPairEitherToFrom

distribEitherPairFromTo
  :: forall a b c.
     foreach (p :: (Either a b, c))
  -> distribEitherPairFrom (distribEitherPairTo p) :~: p
distribEitherPairFromTo (Left _, _)  = Refl
distribEitherPairFromTo (Right _, _) = Refl

distribEitherPairToFrom
  :: forall a b c.
     foreach (s :: Either (a, c) (b, c))
  -> distribEitherPairTo (distribEitherPairFrom s) :~: s
distribEitherPairToFrom (Left (_, _))  = Refl
distribEitherPairToFrom (Right (_, _)) = Refl

-- | Right distributivity of products over 'Either' sums.
prodDistribEitherLIso :: forall a b c. Iso (Either a b, c) (Either (a, c) (b, c))
prodDistribEitherLIso =
  MkIso
    distribEitherPairTo
    distribEitherPairFrom
    distribEitherPairFromTo
    distribEitherPairToFrom
