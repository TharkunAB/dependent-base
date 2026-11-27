{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE ListTuplePuns #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-missing-signatures -fno-enable-rewrite-rules #-}

{- | Dependent Haskell test client exercising every module of @dependent-base@
and all dependent '(.)' ergonomics cases.
-}
module DependentClient (checkDependentSuite, SizedVec (..)) where

import Data.Bool.Dependent qualified as B
import Data.Decision qualified as D
import Data.Either.Dependent qualified as E
import Data.Exists.Dependent qualified as Ex
import Data.Fin.Dependent qualified as F
import Data.Function.Dependent qualified as Fn
import Data.List.Dependent qualified as L
import Data.List.Dependent.All qualified as LA
import Data.List.Dependent.Properties qualified as LP
import Data.Maybe.Dependent qualified as M
import Data.Nat.Dependent qualified as N
import Data.Nat.Dependent.Properties qualified as NP
import Data.Sigma.Dependent qualified as S
import Data.Tuple.Dependent qualified as T
import Data.Type.Equality.Dependent qualified as Eq
import Data.Vec.Dependent qualified as V
import Data.Vec.Dependent.Properties qualified as VP
import Prelude.Dependent
import Prelude qualified as P

-- 1. First-class dependent (.) ergonomics & PLFH-NOTES regressions

zeros :: foreach (n :: Nat) -> Vec Nat n
zeros Zero = VNil
zeros (Succ n) = VCons Zero (zeros n)

-- Gap 1: overloaded numeral in retained function arg under -dcore-lint
zerosPlus1 :: foreach (n :: Nat) -> Vec Nat (plus 1 n)
zerosPlus1 = (.) zeros (plus 1)

-- Gap 2a: compound equality codomain without helper synonym
plusIdPlusOne :: foreach (n :: Nat) -> plus (plus (Succ Zero) n) Zero :~: plus (Succ Zero) n
plusIdPlusOne = NP.plusZero . plus (Succ Zero)

-- Gap 2b: explicit inline type lambda in @(\y -> ...)
plusIdExplicitLam :: foreach (n :: Nat) -> plus (plus (Succ Zero) n) Zero :~: plus (Succ Zero) n
plusIdExplicitLam = (.) @(\y -> plus y Zero :~: y) NP.plusZero (plus (Succ Zero))

-- Gap 3a: constructor Succ as retained function arg
plusIdSucc :: foreach (n :: Nat) -> plus (Succ n) Zero :~: Succ n
plusIdSucc = NP.plusZero . Succ

-- Gap 3b: cong (Succ . plus m) on open foreach variables
congSuccPlus ::
    foreach (m :: Nat) ->
    forall (x :: Nat) (y :: Nat).
    x :~: y -> Succ (plus m x) :~: Succ (plus m y)
congSuccPlus m eq = cong (Succ . plus m) eq

-- Gap 4a: same-module signed & unsigned functions as retained function args
addOneSigned :: Nat -> Nat
addOneSigned n = Succ n

addOneUnsigned n = Succ n

plusIdAddOneSigned :: foreach (n :: Nat) -> plus (Succ n) Zero :~: Succ n
plusIdAddOneSigned = NP.plusZero . addOneSigned

plusIdAddOneUnsigned :: foreach (n :: Nat) -> plus (Succ n) Zero :~: Succ n
plusIdAddOneUnsigned = NP.plusZero . addOneUnsigned

-- Gap 4b: inline lambda as retained function arg
plusIdLambda :: foreach (n :: Nat) -> plus (Succ n) Zero :~: Succ n
plusIdLambda = NP.plusZero . (\n -> Succ n)

-- Note 1: same-module dependent record selector vecLen v in type signature
data SizedVec a = SizedVec
    { vecLen :: Nat
    , vecItems :: Vec a vecLen
    }

extractSizedItems :: foreach (v :: SizedVec a) -> Vec a (vecLen v)
extractSizedItems (SizedVec _ xs) = xs

-- Abstract and concrete dependent composition + PLFH composeLeft + local where
depAbstract ::
    forall
        a
        b
        {mh :: Matchability}
        {mk :: Matchability}
        (h :: b %mh -> a)
        (k :: a %mk -> b).
    (foreach (y :: b) -> k (h y) :~: y) ->
    foreach (f :: a -> b) ->
    foreach (x :: a) ->
    k (h (f x)) :~: f x
depAbstract kh f x = (kh . f) x

depSwapConcrete ::
    forall a b.
    foreach (p :: (a, b)) ->
    swap (swap (swap p)) :~: swap p
depSwapConcrete p = (T.swapInvolutive . swap) p

isoTransWhere :: forall a b c. Iso a b -> Iso b c -> Iso a c
isoTransWhere (MkIso f g gf fg) (MkIso h k kh hk) =
    MkIso @a @c
        to
        from
        (T.composeLeft f g h k gf kh)
        (T.composeLeft k h g f hk fg)
  where
    to = h . f
    from = g . k

nonDepDirect :: (Int -> Int) -> (Int -> Int) -> Int -> Int
nonDepDirect g f x = (g . f) x

nonDepPointfree :: (Int -> Int) -> (Int -> Int) -> Int -> Int
nonDepPointfree g f = g . f

-- 2. Inspect view idiom & ASCII equational reasoning

classifyEqNat :: foreach (m :: Nat) -> foreach (n :: Nat) -> Either (N.eqNat m n :~: True) (N.eqNat m n :~: False)
classifyEqNat m n = case inspect (N.eqNat m) n of
    Reveal True eq -> Left eq
    Reveal False eq -> Right eq

stepReasoning :: foreach (m :: Nat) -> foreach (n :: Nat) -> plus m (Succ n) :~: Succ (plus n m)
stepReasoning m n =
    begin
        ( stepEq @(Succ (plus m n))
            (NP.plusSucc m n)
            ( stepEq @(Succ (plus n m))
                (cong Succ (NP.plusComm m n))
                (qed @(Succ (plus n m)))
            )
        )

chainReasoning :: foreach (m :: Nat) -> plus (plus m Zero) Zero :~: m
chainReasoning m = NP.plusZero (plus m Zero) === NP.plusZero m

type VecAt :: Type -> Nat %U -> Type
type VecAt a = \n -> Vec a n

checkZerosLen :: foreach (n :: Nat) -> Vec Nat n -> plus n Zero :~: n
checkZerosLen n _ = NP.plusZero n

-- 2b. Compile-time bounds-checked Fin numerals (fin, OverloadedLabels, FromNatural)

finZeroOpen :: forall (n :: Nat). Fin (Succ n)
finZeroOpen = fin 0

finOneOpen :: forall (n :: Nat). Fin (Succ (Succ n))
finOneOpen = fin 1

finPlusOpen :: forall (n :: Nat). Fin (plus 2 n)
finPlusOpen = fin 1

labelZeroOpen :: forall (n :: Nat). Fin (Succ n)
labelZeroOpen = #0

labelOneOpen :: forall (n :: Nat). Fin (Succ (Succ n))
labelOneOpen = #1

finToNatStepProof :: foreach (i :: Fin 3) -> F.finToNat ('FS i) :~: Succ (F.finToNat i)
finToNatStepProof _ = Refl

-- 3. Runtime verification of all dependent-base modules
checkDependentSuite :: Bool
checkDependentSuite =
    let two = Succ (Succ Zero)
        three = Succ two
        litTwo = 2 :: Nat
        i1 = 1 :: Int
        i2 = 2 :: Int
        i3 = 3 :: Int
        i7 = 7 :: Int
        i9 = 9 :: Int
        fz3 :: Fin (Succ (Succ (Succ Zero)))
        fz3 = FZ
        fs3 :: Fin (Succ (Succ (Succ Zero)))
        fs3 = FS FZ
        v12 = VCons two (VCons three VNil)
        sv = SizedVec (Succ (Succ Zero)) v12
        iso1 = T.prodCommIso @Int @Bool
        iso2 = T.prodCommIso @Bool @Int
        exPkg :: exists (n :: Nat) | Vec Char n
        exPkg = Pack (type (Succ (Succ Zero))) (VCons 'a' (VCons 'b' VNil))
        cPair :: Show Int /\ Int
        cPair = Ex.MkCPair 42
        allLe :: All (LE (Succ (Succ Zero))) '[Succ (Succ Zero), Succ (Succ (Succ Zero))]
        allLe = AllCons (NP.leRefl (Succ (Succ Zero))) (AllCons (LESucc (LESucc LEZero)) AllNil)
        elem3 :: Elem (Succ (Succ (Succ Zero))) '[Succ (Succ Zero), Succ (Succ (Succ Zero))]
        elem3 = There (Here Refl)
        isoOk = case (isoTrans iso1 iso2, isoTransWhere iso1 iso2) of
            (MkIso rtTo rtFrom rtGF rtFG, MkIso whTo whFrom whGF whFG) ->
                rtTo (i7, True)
                    == (i7, True)
                    && rtFrom (i7, True)
                    == (i7, True)
                    && whTo (i7, True)
                    == (i7, True)
                    && whFrom (i7, True)
                    == (i7, True)
                    && ( case (rtGF (i7, True), rtFG (i7, True), whGF (i7, True), whFG (i7, True)) of
                            (Refl, Refl, Refl, Refl) -> True
                       )
     in toListVec (zerosPlus1 litTwo)
            == [Zero, Zero, Zero]
            && (case (plusIdPlusOne two, plusIdExplicitLam two, plusIdSucc two) of (Refl, Refl, Refl) -> True)
            && ( case (congSuccPlus two (Refl :: Zero :~: Zero), plusIdAddOneSigned two, plusIdAddOneUnsigned two, plusIdLambda two) of
                    (Refl, Refl, Refl, Refl) -> True
               )
            && toListVec (extractSizedItems sv)
            == [two, three]
            && toListVec sv.vecItems
            == [two, three]
            && ( case (depAbstract @Nat @Nat @id @id (\_ -> Refl) Succ two, depSwapConcrete (i1, True)) of
                    (Refl, Refl) -> True
               )
            && nonDepDirect (+ 1) (* 2) 10
            == 21
            && nonDepPointfree (+ 1) (* 2) 10
            == 21
            && isoOk
            && (case (NP.plusZero $ two, Fn.applyDep NP.plusZero two) of (Refl, Refl) -> True)
            && (case Fn.composeDep @(\k -> plus k Zero :~: k) checkZerosLen zeros two of Refl -> True)
            && Fn.composeSigma @(\n -> plus n Zero :~: n) (\p -> case second p of Refl -> natToInt (first p)) NP.plusZero two
            == 2
            && Fn.idDep two
            == two
            && Fn.constDep 'k' two
            == 'k'
            && (case Fn.flipDep NP.plusComm two three of Refl -> True)
            && Fn.on (==) natToInt two (Succ (Succ Zero))
            && (case classifyEqNat two two of Left Refl -> True; Right _ -> False)
            && (case classifyEqNat two three of Left _ -> False; Right Refl -> True)
            && ( case (stepReasoning two three, chainReasoning two, Eq.cong2 plus (Refl :: Zero :~: Zero) (Refl :: Zero :~: Zero), Eq.congApp @Zero (Refl :: Succ :~: Succ)) of
                    (Refl, Refl, Refl, Refl) -> True
               )
            && Eq.subst (Vec Char) (NP.plusZero (Succ Zero)) (VCons 'x' VNil)
            == VCons 'x' VNil
            && Eq.substImplicit (NP.plusZero (Succ Zero)) (VCons 'x' VNil)
            == VCons 'x' VNil
            -- Decision & DecEq across (), Bool, Ordering, Nat, Fin, Maybe, Either, (,), [], Vec
            && decToBool (decEq () ())
            && decToBool (decEq True True)
            && not (decToBool (decEq True False))
            && decToBool (decEq LT LT)
            && not (decToBool (decEq LT GT))
            && decToBool (decEq two two)
            && not (decToBool (decEq two three))
            && decToBool (decEq fz3 fz3)
            && not (decToBool (decEq fz3 fs3))
            && decToBool (decEq (Just two) (Just two))
            && not (decToBool (decEq (Just two) Nothing))
            && decToBool (decEq (Left two :: Either Nat Bool) (Left two))
            && not (decToBool (decEq (Left two :: Either Nat Bool) (Right True)))
            && decToBool (decEq (two, True) (two, True))
            && not (decToBool (decEq (two, True) (three, True)))
            && decToBool (decEq [two, three] [two, three])
            && not (decToBool (decEq [two] [two, three]))
            && decToBool (decEq v12 v12)
            && not (decToBool (decEq v12 (VCons three (VCons two VNil))))
            && decToBool (D.decNot (decEq two three))
            && decToBool (D.decAnd (decEq two two) (decEq True True))
            && decToBool (D.decOr (decEq two three) (decEq True True))
            && decToBool (D.decImp (decEq two three) (decEq True False))
            && (case D.reflectsBoolToDec (D.decToReflectsBool (decEq two two)) of Yes Refl -> True; No _ -> False)
            -- Bool, Maybe, Either, Tuple laws
            && bool 10 (20 :: Int) True
            == 20
            && ( case (B.notInvolutive True, B.andAssoc True False True, B.orAssoc False True False, B.deMorganAnd True False, B.deMorganOr False True) of
                    (Refl, Refl, Refl, Refl, Refl) -> True
               )
            && M.mapMaybe (\n -> if n > (1 :: Int) then Just (n * 10) else Nothing) [1, 2, 3]
            == [20, 30]
            && M.catMaybes [Nothing, Just (4 :: Int), Nothing, Just 5]
            == [4, 5]
            && ( case (M.fmapMaybeId (Just i3), M.fmapMaybeCompose Succ (plus two) (Just three), M.isJustJust True, M.listToMaybeMaybeToList (Just 'a')) of
                    (Refl, Refl, Refl, Refl) -> True
               )
            && E.bimapEither (+ 1) not (Left i3)
            == Left 4
            && E.swapEither (Left 'a' :: Either Char Int)
            == Right 'a'
            && (case (E.swapEitherInvolutive (Left 'a' :: Either Char Int), E.mapLeftId (Left 'a' :: Either Char Int), E.mapRightId (Right i3 :: Either Char Int)) of (Refl, Refl, Refl) -> True)
            && (case E.sumAssocIso @Int @Bool @Char of MkIso t f gf fg -> case (gf (Left (Right True)), fg (Right (Left True))) of (Refl, Refl) -> f (t (Right 'z')) == Right 'z')
            && (case T.prodAssocIso @Int @Bool @Char of MkIso t f gf fg -> case (gf ((i1, True), 'x'), fg (i1, (True, 'x'))) of (Refl, Refl) -> f (t ((i1, True), 'x')) == ((i1, True), 'x'))
            && (case T.prodUnitLIso @Int of MkIso t f gf fg -> case (gf ((), i9), fg i9) of (Refl, Refl) -> t (f i9) == i9)
            && (case T.prodUnitRIso @Int of MkIso t f gf fg -> case (gf (i9, ()), fg i9) of (Refl, Refl) -> t (f i9) == i9)
            && (case T.prodDistribEitherIso @Int @Bool @Char of MkIso t f gf fg -> case (gf (i1, Left True), fg (Right (i1, 'c'))) of (Refl, Refl) -> f (t (i1, Right 'c')) == (i1, Right 'c'))
            -- Nat, Fin, Vec, List, All, Sigma, Exists
            && natToInteger (mul two three)
            == 6
            && natToInt (minus three two)
            == 1
            && natToInt (minNat two three)
            == 2
            && natToInt (maxNat two three)
            == 3
            && ( case (NP.mulZero three, NP.mulSucc two three, NP.mulDistribR two three two, NP.mulAssoc two three two, NP.mulComm two three) of
                    (Refl, Refl, Refl, Refl, Refl) -> True
               )
            && (case NP.decLE two three of Yes ev -> NP.leTrans (NP.leRefl two) ev == ev; No _ -> False)
            && (case NP.leAntisym (NP.leRefl two) (NP.leRefl two) of Refl -> True)
            && F.finToInt (F.oppositeFin 3 fz3)
            == 2
            && F.finToInt (F.oppositeFin 3 (FS (FS FZ) :: Fin 3))
            == 0
            && F.finToInt (F.shiftFin two (FZ :: Fin 3))
            == 2
            && finZeroOpen @Zero
            == FZ
            && finOneOpen @Zero
            == FS FZ
            && finPlusOpen @Zero
            == FS FZ
            && labelZeroOpen @Zero
            == FZ
            && labelOneOpen @Zero
            == FS FZ
            && F.finToNat (fin 2 :: Fin 3)
            == two
            && F.finToNat (#2 :: Fin 3)
            == two
            && (case finToNatStepProof fz3 of Refl -> True)
            && ( let combined :: Vec String 3
                     combined = VCons "alpha" (VCons "beta" (VCons "gamma" VNil))
                  in lookupVec (fin 0) combined
                        == "alpha"
                        && lookupVec (fin 1) combined
                        == "beta"
                        && lookupVec (fin 2) combined
                        == "gamma"
                        && lookupVec #0 combined
                        == "alpha"
                        && lookupVec #1 combined
                        == "beta"
                        && lookupVec #2 combined
                        == "gamma"
               )
            && toListVec (V.snocVec v12 Zero)
            == [two, three, Zero]
            && toListVec (V.initVec v12)
            == [two]
            && V.lastVec v12
            == three
            && toListVec (V.reverseVec v12)
            == [three, two]
            && toListVec (V.updateAtVec (FS FZ) Succ v12)
            == [two, Succ three]
            && toListVec (V.updateAtVec (fin 1) Succ v12)
            == [two, Succ three]
            && toListVec (V.updateAtVec #1 Succ v12)
            == [two, Succ three]
            && ( case (VP.vconsCong two (Refl :: 'VNil :~: ('VNil :: Vec Nat Zero)), VP.appendVecNilL v12, VP.appendVecCons two v12 v12) of
                    (Refl, Refl, Refl) -> True
               )
            && (case VP.splitAtAppendVec @Nat @(Succ Zero) (Succ Zero) v12 of Pair l (Pair r Refl) -> toListVec l == [two] && toListVec r == [three])
            && (case (VP.appendVecNilR v12, VP.appendVecAssoc v12 v12 v12) of (HRefl, HRefl) -> True)
            && L.reverseShunt [1 :: Int, 2, 3]
            == [3, 2, 1]
            && ( case (LP.appendNilR [i1, i2], LP.appendAssoc [i1] [i2] [i3], LP.mapId [i1, i2], LP.mapCompose Succ (plus two) [two, three], LP.reverseShuntInvolutive [i1, i2, i3]) of
                    (Refl, Refl, Refl, Refl, Refl) -> True
               )
            && lookupAll allLe elem3
            == LESucc (LESucc LEZero)
            && decToBool (decAll (NP.decLE two) [two, three])
            && not (decToBool (decAll (NP.decLE three) [two, three]))
            && decToBool (decAny (NP.decLE three) [two, three])
            && decToBool (decElem three [two, three])
            && ( let allZ1 :: All (LE Zero) '[Zero]
                     allZ1 = LA.tabulateAll [Zero] (\_ -> LEZero)
                     allZ2 :: All (LE Zero) '[Succ Zero, Succ (Succ Zero)]
                     allZ2 = AllCons LEZero (AllCons LEZero AllNil)
                     mapped :: All (LE (Succ Zero)) '[Succ (Succ Zero), Succ (Succ (Succ Zero))]
                     mapped = LA.mapAll (NP.leTrans (LESucc LEZero)) allLe
                  in case (mapped, LA.splitAllAppend @'[Succ Zero, Succ (Succ Zero)] [Zero] (LA.allAppend allZ1 allZ2)) of
                        (AllCons _ _, (AllCons LEZero AllNil, AllCons _ _)) -> True
               )
            && ( let s1 :: Sigma Nat (VecAt Char)
                     s1 = Pair (Succ (Succ Zero)) (VCons 'a' (VCons 'a' VNil))
                     s2 :: Sigma Nat (VecAt Char)
                     s2 = mapSigma @(VecAt Char) @(VecAt Char) Succ (\_ v -> VCons 'z' v) s1
                     s3 :: Sigma Nat (VecAt Nat)
                     s3 = S.mapSigmaSecond @(VecAt Char) @(VecAt Nat) (\n _ -> zeros n) s1
                  in natToInt (first s2) == 3 && toListVec (second s2) == "zaa" && toListVec (second s3) == [Zero, Zero]
               )
            && uncurrySigma @(VecAt Nat) (currySigma @(VecAt Nat) (\p -> natToInt (first p))) (Pair @Nat @(VecAt Nat) (Succ (Succ Zero)) v12)
            == 2
            && withExists @(VecAt Char) exPkg (\_ v -> toListVec v)
            == "ab"
            && withExists @(VecAt Char) (mapExists @(VecAt Char) @(VecAt Char) (\_ v -> mapVec P.succ v) exPkg) (\_ v -> toListVec v)
            == "bc"
            && discardEvidence cPair
            == 42
            && withEvidence cPair show
            == "42"
