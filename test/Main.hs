module Main (main) where

import DependentClient (checkDependentSuite)
import OrdinaryInteropClient (checkOrdinaryInterop)

main :: IO ()
main = do
    interopOk <- checkOrdinaryInterop
    if interopOk && checkDependentSuite
        then pure ()
        else fail "dependent-base test suite failed"
