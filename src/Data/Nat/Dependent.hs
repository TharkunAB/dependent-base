{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Peano natural numbers ('Nat'), total arithmetic, and order relations.
module Data.Nat.Dependent (
    Nat (..),
    Size,
    plus,
    type (+),
    mul,
    minus,
    minNat,
    maxNat,
    minSize,
    eqNat,
    eqSize,
    compareNat,
    natToInt,
    natToInteger,
    LE (..),
    LTNat,
) where

import Data.Nat.Dependent.Internal (
    Nat (..),
    Size,
    compareNat,
    eqNat,
    eqSize,
    maxNat,
    minNat,
    minSize,
    minus,
    mul,
    plus,
 )
import Prelude (Eq, Int, Integer, Show, (+))

-- | Add two Peano naturals in a type using the checked equations of 'plus'.
type (m :: Nat) + (n :: Nat) = plus m n

infixl 6 type +

-- | Convert a finite Peano natural to a machine 'Int'.
natToInt :: Nat -> Int
natToInt Zero = 0
natToInt (Succ n) = 1 + natToInt n

-- | Convert a finite Peano natural to an arbitrary-precision 'Integer'.
natToInteger :: Nat -> Integer
natToInteger Zero = 0
natToInteger (Succ n) = 1 + natToInteger n

-- | Inductive less-than-or-equal evidence for Peano naturals.
data LE (m :: Nat) (n :: Nat) where
    LEZero :: forall {n :: Nat}. LE Zero n
    LESucc :: forall {m :: Nat} {n :: Nat}. LE m n -> LE (Succ m) (Succ n)

deriving instance Show (LE m n)
deriving instance Eq (LE m n)

{- | Strict less-than relation on Peano naturals: @LTNat m n@ holds when
@Succ m@ is at most @n@.
-}
type LTNat (m :: Nat) (n :: Nat) = LE (Succ m) n
