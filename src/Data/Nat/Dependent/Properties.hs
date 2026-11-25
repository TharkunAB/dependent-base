{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE EmptyCase #-}

-- | Arithmetic and order lemmas for Peano naturals ('Nat').
module Data.Nat.Dependent.Properties
  ( congSucc
  , congFirst
  , succInjective
  , eqSizeRefl
  , eqNatRefl
  , plusZero
  , plusSucc
  , plusAssoc
  , plusComm
  , mulZero
  , mulSucc
  , mulOneL
  , mulOneR
  , mulDistribR
  , mulDistribL
  , mulAssoc
  , mulComm
  , minusZeroR
  , minusDiag
  , leRefl
  , leTrans
  , leAntisym
  , leSuccR
  , invLESucc
  , decLE
  ) where

import Data.Decision (Dec (No, Yes))
import Data.Nat.Dependent (LE (..), Nat (..), eqSize, minus, mul, plus)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong, sym, trans)
import GHC.Matchability (U)
import Prelude (Bool (True))

-- | Equal naturals have equal successors.
congSucc :: forall (m :: Nat) (n :: Nat). m :~: n -> Succ m :~: Succ n
congSucc Refl = Refl

-- | Lift an equality through the first operand of a binary 'Nat' operation.
congFirst
  :: forall (f :: Nat %U -> Nat %U -> Nat) r m n.
     m :~: n -> f m r :~: f n r
congFirst Refl = Refl

-- | Constructor 'Succ' is injective.
succInjective :: forall {m :: Nat} {n :: Nat}. Succ m :~: Succ n -> m :~: n
succInjective Refl = Refl

-- | Comparing any finite natural with itself yields 'True'.
eqSizeRefl :: foreach (n :: Nat) -> eqSize n n :~: True
eqSizeRefl Zero     = Refl
eqSizeRefl (Succ n) = eqSizeRefl n

-- | Alias for 'eqSizeRefl' under the 'Data.Nat.Dependent.eqNat' name.
eqNatRefl :: foreach (n :: Nat) -> eqSize n n :~: True
eqNatRefl = eqSizeRefl

-- | Right identity of 'plus'.
plusZero :: foreach (m :: Nat) -> plus m Zero :~: m
plusZero Zero     = Refl
plusZero (Succ m) = cong Succ (plusZero m)

-- | Move 'Succ' out of the right operand of 'plus'.
plusSucc :: foreach (m :: Nat) -> foreach (n :: Nat) -> plus m (Succ n) :~: Succ (plus m n)
plusSucc Zero     _ = Refl
plusSucc (Succ m) n = cong Succ (plusSucc m n)

-- | Associativity of 'plus'.
plusAssoc
  :: foreach (m :: Nat)
  -> foreach (n :: Nat)
  -> foreach (p :: Nat)
  -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc Zero     _ _ = Refl
plusAssoc (Succ m) n p = cong Succ (plusAssoc m n p)

-- | Commutativity of 'plus'.
plusComm :: foreach (m :: Nat) -> foreach (n :: Nat) -> plus m n :~: plus n m
plusComm m Zero     = plusZero m
plusComm m (Succ n) = trans (plusSucc m n) (cong Succ (plusComm m n))

-- | Right annihilation of 'mul' by 'Zero'.
mulZero :: foreach (m :: Nat) -> mul m Zero :~: Zero
mulZero Zero     = Refl
mulZero (Succ m) = mulZero m

-- | Step the right operand of 'mul' by one successor.
mulSucc
  :: foreach (m :: Nat)
  -> foreach (n :: Nat)
  -> mul m (Succ n) :~: plus m (mul m n)
mulSucc Zero     _ = Refl
mulSucc (Succ m) n =
  cong Succ
    (trans (cong (plus n) (mulSucc m n))
      (trans (sym (plusAssoc n m (mul m n)))
        (trans (cong (\k -> plus k (mul m n)) (plusComm n m))
               (plusAssoc m n (mul m n)))))

-- | Left multiplicative identity: @mul 1 n@ equals @n@.
mulOneL :: foreach (n :: Nat) -> mul (Succ Zero) n :~: n
mulOneL n = plusZero n

-- | Right multiplicative identity: @mul m 1@ equals @m@.
mulOneR :: foreach (m :: Nat) -> mul m (Succ Zero) :~: m
mulOneR Zero     = Refl
mulOneR (Succ m) = cong Succ (mulOneR m)

-- | Right distributivity of 'mul' over 'plus':
-- @mul (plus m n) p@ equals @plus (mul m p) (mul n p)@.
mulDistribR
  :: foreach (m :: Nat)
  -> foreach (n :: Nat)
  -> foreach (p :: Nat)
  -> mul (plus m n) p :~: plus (mul m p) (mul n p)
mulDistribR Zero     _ _ = Refl
mulDistribR (Succ m) n p =
  trans (cong (plus p) (mulDistribR m n p)) (sym (plusAssoc p (mul m p) (mul n p)))

-- | Left distributivity of 'mul' over 'plus':
-- @mul m (plus n p)@ equals @plus (mul m n) (mul m p)@.
mulDistribL
  :: foreach (m :: Nat)
  -> foreach (n :: Nat)
  -> foreach (p :: Nat)
  -> mul m (plus n p) :~: plus (mul m n) (mul m p)
mulDistribL Zero     _ _ = Refl
mulDistribL (Succ m) n p =
  trans (cong (\k -> plus (plus n p) k) (mulDistribL m n p))
    (trans (plusAssoc n p (plus (mul m n) (mul m p)))
      (trans (cong (plus n) (sym (plusAssoc p (mul m n) (mul m p))))
        (trans (cong (plus n) (cong (\k -> plus k (mul m p)) (plusComm p (mul m n))))
          (trans (cong (plus n) (plusAssoc (mul m n) p (mul m p)))
                 (sym (plusAssoc n (mul m n) (plus p (mul m p))))))))

-- | Associativity of 'mul'.
mulAssoc
  :: foreach (m :: Nat)
  -> foreach (n :: Nat)
  -> foreach (p :: Nat)
  -> mul (mul m n) p :~: mul m (mul n p)
mulAssoc Zero     _ _ = Refl
mulAssoc (Succ m) n p =
  trans (mulDistribR n (mul m n) p) (cong (\k -> plus (mul n p) k) (mulAssoc m n p))

-- | Commutativity of 'mul'.
mulComm :: foreach (m :: Nat) -> foreach (n :: Nat) -> mul m n :~: mul n m
mulComm m Zero     = mulZero m
mulComm m (Succ n) = trans (mulSucc m n) (cong (plus m) (mulComm m n))

-- | Subtracting 'Zero' on the right preserves a natural number.
minusZeroR :: foreach (m :: Nat) -> minus m Zero :~: m
minusZeroR Zero     = Refl
minusZeroR (Succ _) = Refl

-- | Subtracting any natural number from itself yields 'Zero'.
minusDiag :: foreach (n :: Nat) -> minus n n :~: Zero
minusDiag Zero     = Refl
minusDiag (Succ n) = minusDiag n

-- | Reflexivity of 'LE'.
leRefl :: foreach (n :: Nat) -> LE n n
leRefl Zero     = LEZero
leRefl (Succ n) = LESucc (leRefl n)

-- | Transitivity of 'LE'.
leTrans :: forall {m :: Nat} {n :: Nat} {p :: Nat}. LE m n -> LE n p -> LE m p
leTrans LEZero      _           = LEZero
leTrans (LESucc mn) (LESucc np) = LESucc (leTrans mn np)

-- | Antisymmetry of 'LE'.
leAntisym :: forall {m :: Nat} {n :: Nat}. LE m n -> LE n m -> m :~: n
leAntisym LEZero      LEZero      = Refl
leAntisym (LESucc mn) (LESucc nm) = cong Succ (leAntisym mn nm)

-- | Every natural is less than or equal to its successor.
leSuccR :: forall {m :: Nat} {n :: Nat}. LE m n -> LE m (Succ n)
leSuccR LEZero      = LEZero
leSuccR (LESucc mn) = LESucc (leSuccR mn)

-- | Invert 'LE' under two 'Succ' constructors.
invLESucc :: forall {m :: Nat} {n :: Nat}. LE (Succ m) (Succ n) -> LE m n
invLESucc (LESucc mn) = mn

-- | Decide whether @LE m n@ holds for any two runtime naturals.
decLE :: foreach (m :: Nat) -> foreach (n :: Nat) -> Dec (LE m n)
decLE Zero     _        = Yes LEZero
decLE (Succ _) Zero     = No (\ev -> case ev of {})
decLE (Succ m) (Succ n) = case decLE m n of
  Yes mn   -> Yes (LESucc mn)
  No notMn -> No (\smSn -> notMn (invLESucc smSn))
