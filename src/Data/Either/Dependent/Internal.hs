{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}

-- | Certified total operations on 'Either' sums.
module Data.Either.Dependent.Internal
  ( Either (..)
  , either
  , isLeft
  , isRight
  , bimapEither
  , mapLeft
  , mapRight
  , swapEither
  , assocEitherTo
  , assocEitherFrom
  ) where

import Prelude (Bool (..), Either (..))

-- | Eliminate an 'Either' sum with one handler for each branch.
either :: forall a b c. (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left x)  = f x
either _ g (Right y) = g y

-- | Test whether an 'Either' value uses 'Left'.
isLeft :: forall a b. Either a b -> Bool
isLeft (Left _)  = True
isLeft (Right _) = False

-- | Test whether an 'Either' value uses 'Right'.
isRight :: forall a b. Either a b -> Bool
isRight (Left _)  = False
isRight (Right _) = True

-- | Map independent functions over both branches of an 'Either' value.
bimapEither :: forall a b c d. (a -> c) -> (b -> d) -> Either a b -> Either c d
bimapEither f _ (Left x)  = Left (f x)
bimapEither _ g (Right y) = Right (g y)

-- | Map a function over the 'Left' branch and preserve 'Right'.
mapLeft :: forall a b c. (a -> c) -> Either a b -> Either c b
mapLeft f (Left x)  = Left (f x)
mapLeft _ (Right y) = Right y

-- | Map a function over the 'Right' branch and preserve 'Left'.
mapRight :: forall a b d. (b -> d) -> Either a b -> Either a d
mapRight _ (Left x)  = Left x
mapRight g (Right y) = Right (g y)

-- | Exchange the 'Left' and 'Right' branches of an 'Either' sum.
swapEither :: forall a b. Either a b -> Either b a
swapEither (Left x)  = Right x
swapEither (Right y) = Left y

-- | Reassociate a left-nested 'Either' sum to the right.
assocEitherTo :: forall a b c. Either (Either a b) c -> Either a (Either b c)
assocEitherTo (Left (Left x))  = Left x
assocEitherTo (Left (Right y)) = Right (Left y)
assocEitherTo (Right z)        = Right (Right z)

-- | Reassociate a right-nested 'Either' sum to the left.
assocEitherFrom :: forall a b c. Either a (Either b c) -> Either (Either a b) c
assocEitherFrom (Left x)          = Left (Left x)
assocEitherFrom (Right (Left y))  = Left (Right y)
assocEitherFrom (Right (Right z)) = Right z
