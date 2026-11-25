{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}

-- | Certified total operations on ordinary Haskell lists.
module Data.List.Dependent
  ( size
  , lengthNat
  , (++)
  , append
  , map
  , List.foldr
  , zip
  , zipWith
  , reverse
  , shunt
  , reverseShunt
  , takeSize
  ) where

import Data.Nat.Dependent (Nat (..))
import qualified GHC.Internal.List as List
import Prelude (map, reverse, zip, zipWith, (++))

-- | Count the cells of a list without inspecting its elements.
size :: forall a. [a] -> Nat
size []       = Zero
size (_ : xs) = Succ (size xs)

-- | Count the cells of a list as a Peano natural (synonym for 'size').
lengthNat :: forall a. [a] -> Nat
lengthNat = size

-- | Concatenate two lists by structural recursion on the left list.
append :: forall a. [a] -> [a] -> [a]
append []       ys = ys
append (x : xs) ys = x : append xs ys

-- | Reverse a list onto an accumulator by structural recursion.
shunt :: forall a. [a] -> [a] -> [a]
shunt []       acc = acc
shunt (x : xs) acc = shunt xs (x : acc)

-- | Reverse a list using 'shunt' with an empty initial accumulator.
reverseShunt :: forall a. [a] -> [a]
reverseShunt xs = shunt xs []

-- | Take at most @n@ elements from the front of a list.
takeSize :: forall a. Nat -> [a] -> [a]
takeSize Zero     _        = []
takeSize (Succ _) []       = []
takeSize (Succ n) (x : xs) = x : takeSize n xs
