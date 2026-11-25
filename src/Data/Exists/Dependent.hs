{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Erased existential packages ('Pack'), constraint pairing ('/\'), witness
-- tokens ('Witness'), and elimination combinators.
module Data.Exists.Dependent
  ( pattern Pack
  , type (/\) (..)
  , discardEvidence
  , withEvidence
  , Witness (..)
  , withExists
  , mapExists
  , uncurryExists
  ) where

import GHC.Exists
  ( Witness (..)
  , discardEvidence
  , mapExists
  , pattern Pack
  , uncurryExists
  , withEvidence
  , withExists
  , type (/\) (..)
  )
import Prelude ()
