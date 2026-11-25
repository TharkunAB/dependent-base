{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fwrite-source-equations -fno-cse #-}

-- | Canonical Peano natural numbers ('Nat'), numeral conversion instances, and
-- certified total arithmetic operations.
module Data.Nat.Dependent.Internal
  ( Nat (..)
  , Size
  , plus
  , mul
  , minus
  , minSize
  , minNat
  , maxNat
  , eqSize
  , eqNat
  , compareNat
  ) where

import Control.Exception (ArithException (Underflow), throw)
import GHC.TypeNats.Experimental (FromNatural)
import qualified GHC.TypeNats as TN
import Prelude (Bool (..), Eq (..), Num (..), Ord (..), Ordering (..), Show, otherwise)

-- | A Peano natural number.
data Nat
  = Zero
  | Succ Nat
  deriving (Eq, Ord, Show)

-- | Alias for a Peano count.
type Size = Nat

-- | Add two Peano naturals by structural recursion on the first operand.
plus :: Nat -> Nat -> Nat
plus Zero     n = n
plus (Succ m) n = Succ (plus m n)

-- | Convert a type-level 'TN.Nat' literal into a Peano 'Nat'.
-- See Note [Peano numeral literals].
type family ToPeano (n :: TN.Nat) :: Nat where
  ToPeano 0 = Zero
  ToPeano n = Succ (ToPeano (n TN.- 1))

type instance FromNatural Nat n = ToPeano n

{- Note [Peano numeral literals]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The 'FromNatural' instance converts type-level natural literals whose expected
kind is 'Nat'. The 'Num' instance converts runtime numeral literals. Method
'fromInteger' uses the three-guard recursive definition certified by
'checkedSourceLiteral' in "GHC.Tc.TyCl.Instance", so retained calls such as
@zeros . plus 1@ and @plusZero 3@ lower numeral literals identically in the
runtime term and in the type index.
-}

instance Num Nat where
  (+) = plus
  m * n = times m
    where
      times Zero     = Zero
      times (Succ k) = plus n (times k)
  n - Zero        = n
  Zero - Succ _   = throw Underflow
  Succ n - Succ m = n - m
  abs n           = n
  signum Zero     = Zero
  signum (Succ _) = Succ Zero
  fromInteger n
    | n < 0     = throw Underflow
    | n == 0    = Zero
    | otherwise = Succ (fromInteger (n - 1))

-- | Multiply two Peano naturals by structural recursion on the first operand.
mul :: Nat -> Nat -> Nat
mul Zero     _ = Zero
mul (Succ m) n = plus n (mul m n)

-- | Truncated subtraction (monus) on Peano naturals.
minus :: Nat -> Nat -> Nat
minus Zero     _        = Zero
minus (Succ m) Zero     = Succ m
minus (Succ m) (Succ n) = minus m n

-- | Return the smaller of two Peano naturals.
minSize :: Nat -> Nat -> Nat
minSize Zero     _        = Zero
minSize (Succ _) Zero     = Zero
minSize (Succ m) (Succ n) = Succ (minSize m n)

-- | Return the smaller of two Peano naturals.
minNat :: Nat -> Nat -> Nat
minNat Zero     _        = Zero
minNat (Succ _) Zero     = Zero
minNat (Succ m) (Succ n) = Succ (minNat m n)

-- | Return the larger of two Peano naturals.
maxNat :: Nat -> Nat -> Nat
maxNat Zero     n        = n
maxNat (Succ m) Zero     = Succ m
maxNat (Succ m) (Succ n) = Succ (maxNat m n)

-- | Compare two Peano naturals for equality by structural recursion.
eqSize :: Nat -> Nat -> Bool
eqSize Zero     Zero     = True
eqSize Zero     (Succ _) = False
eqSize (Succ _) Zero     = False
eqSize (Succ m) (Succ n) = eqSize m n

-- | Test whether two Peano naturals are equal by structural recursion.
eqNat :: Nat -> Nat -> Bool
eqNat Zero     Zero     = True
eqNat Zero     (Succ _) = False
eqNat (Succ _) Zero     = False
eqNat (Succ m) (Succ n) = eqNat m n

-- | Compare two Peano naturals by structural recursion.
compareNat :: Nat -> Nat -> Ordering
compareNat Zero     Zero     = EQ
compareNat Zero     (Succ _) = LT
compareNat (Succ _) Zero     = GT
compareNat (Succ m) (Succ n) = compareNat m n
