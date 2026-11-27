{-# LANGUAGE Haskell2010 #-}
{-# OPTIONS_GHC -Wno-gadt-mono-local-binds #-}

{- | Pure Haskell2010 client verifying that @dependent-base@ interfaces can be
imported and used from ordinary code without @-XDependentTypes@ or @.hs@
sources on the search path.
-}
module OrdinaryInteropClient (checkOrdinaryInterop) where

import qualified Data.Nat.Dependent.Properties as NP
import Prelude.Dependent
import qualified Prelude as P

checkOrdinaryInterop :: P.IO Bool
checkOrdinaryInterop = do
    let two = Succ (Succ Zero)
        three = Succ two
        vec = VCons 'x' (VCons 'y' VNil)
        okDec = decToBool (decEq two two) && not (decToBool (decEq two three))
        okVec = case fromListExact two "hi" of
            Just v -> toListVec (appendVec v vec) == "hixy"
            Nothing -> False
        okFin = case mkFin three 1 of
            Just i -> finToInt (oppositeFin three i) == 1
            Nothing -> False
        okEq = case (NP.plusComm two three, NP.mulAssoc two three two) of
            (Refl, Refl) -> True
        okSig = withSigma (packListVec "abc") (\n v -> (natToInteger n, toListVec v)) == (3, "abc")
        okDot = ((+ 1) . (* 2)) (5 :: Int) == 11
    P.pure (okDec && okVec && okFin && okEq && okSig && okDot)
