{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}

-- | Congruence, indexing, splitting, and concatenation laws for length-indexed
-- vectors.
module Data.Vec.Dependent.Properties
  ( SplitVec
  , vconsCong
  , appendVecNilL
  , appendVecCons
  , appendVecNilR
  , appendVecAssoc
  , splitAtAppendVec
  ) where

import Data.Nat.Dependent (Nat (..), plus, type (+))
import Data.Type.Equality.Dependent ((:~:) (Refl), (:~~:) (HRefl), cong)
import Data.Vec.Dependent
  ( Vec (..)
  , appendVec
  )
import GHC.Sigma (Sigma (Pair))
import Prelude ()

-- | Dependent pair of a prefix of length @n@, a suffix of length @m@, and a
-- proof that 'appendVec' reconstructs @xs@.
type SplitVec a (n :: Nat) (m :: Nat) (xs :: Vec a (n + m)) =
  some (left :: Vec a n) | (some (right :: Vec a m) | appendVec left right :~: xs)

-- | Congruence in the tail of 'VCons' at a fixed head element.
vconsCong
  :: forall {a} {n :: Nat}.
     foreach (x :: a)
  -> forall {xs :: Vec a n} {ys :: Vec a n}.
     xs :~: ys -> VCons x xs :~: VCons x ys
vconsCong x eq = cong (VCons x) eq

-- | Left identity of 'appendVec'.
appendVecNilL
  :: forall {a} {n :: Nat}.
     foreach (xs :: Vec a n)
  -> appendVec VNil xs :~: xs
appendVecNilL _ = Refl

-- | Prepending a non-empty vector commutes with 'VCons'.
appendVecCons
  :: forall {a} {m :: Nat} {n :: Nat}.
     foreach (x :: a)
  -> foreach (xs :: Vec a m)
  -> foreach (ys :: Vec a n)
  -> appendVec (VCons x xs) ys :~: VCons x (appendVec xs ys)
appendVecCons _ _ _ = Refl

-- | Right identity of 'appendVec' (heterogeneous equality).
appendVecNilR
  :: forall a {n :: Nat}.
     foreach (xs :: Vec a n)
  -> appendVec xs (VNil :: Vec a Zero) :~~: xs
appendVecNilR VNil          = HRefl
appendVecNilR (VCons _x xs) =
  case appendVecNilR @a xs of
    HRefl -> HRefl

-- | Associativity of 'appendVec' (heterogeneous equality).
appendVecAssoc
  :: forall a {m :: Nat} {n :: Nat} {p :: Nat}.
     foreach (xs :: Vec a m)
  -> foreach (ys :: Vec a n)
  -> foreach (zs :: Vec a p)
  -> appendVec (appendVec xs ys) zs :~~: appendVec xs (appendVec ys zs)
appendVecAssoc VNil          _  _  = HRefl
appendVecAssoc (VCons _x xs) ys zs =
  case appendVecAssoc @a xs ys zs of
    HRefl -> HRefl

-- | Split a vector of length @plus n m@ into a prefix and suffix paired with a
-- reconstruction proof.
splitAtAppendVec
  :: forall a m.
     foreach (n :: Nat)
  -> foreach (xs :: Vec a (plus n m))
  -> SplitVec a n m xs
splitAtAppendVec Zero     xs           = Pair VNil (Pair xs Refl)
splitAtAppendVec (Succ n) (VCons x xs) =
  case splitAtAppendVec @a @m n xs of
    Pair left (Pair right eq) ->
      Pair (VCons x left) (Pair right (case eq of Refl -> Refl))
