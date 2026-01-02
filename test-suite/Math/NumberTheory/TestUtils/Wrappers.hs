-- |
-- Module:      Math.NumberTheory.TestUtils.Wrappers
-- Copyright:   (c) 2016 Andrew Lelechenko
-- Licence:     MIT
-- Maintainer:  Andrew Lelechenko <andrew.lelechenko@gmail.com>
--
-- Utils to test Math.NumberTheory
--

{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}

{-# OPTIONS_GHC -fno-warn-orphans       #-}

module Math.NumberTheory.TestUtils.Wrappers
  ( AnySign(..)
  , Power(..)
  , Huge(..)
  , Humoungous(..)
  , Gargantuan(..)
  , Googolplex(..)
  , FZeight(..)
  , Boogol(..)
  , BoogolZeight(..)
  ) where

import Control.Applicative
import Data.Functor.Classes

import Test.Tasty.QuickCheck as QC hiding (Positive(..), NonNegative(..))
import Test.SmallCheck.Series (Positive(..), NonNegative(..), Serial(..), Series)

-------------------------------------------------------------------------------
-- AnySign

newtype AnySign a = AnySign { getAnySign :: a }
  deriving (Eq, Ord, Read, Show, Num, Enum, Bounded, Integral, Real, Functor, Foldable, Traversable, Arbitrary)

instance (Monad m, Serial m a) => Serial m (AnySign a) where
  series = AnySign <$> series

instance Eq1 AnySign where
  liftEq eq (AnySign a) (AnySign b) = a `eq` b

instance Ord1 AnySign where
  liftCompare cmp (AnySign a) (AnySign b) = a `cmp` b

instance Show1 AnySign where
  liftShowsPrec shw _ p (AnySign a) = shw p a

-------------------------------------------------------------------------------
-- Positive from smallcheck

instance (Num a, Ord a, Arbitrary a) => Arbitrary (Positive a) where
  arbitrary = Positive <$> (arbitrary `suchThat` (> 0))
  shrink (Positive x) = Positive <$> filter (> 0) (shrink x)

instance Eq1 Positive where
  liftEq eq (Positive a) (Positive b) = a `eq` b

instance Ord1 Positive where
  liftCompare cmp (Positive a) (Positive b) = a `cmp` b

instance Show1 Positive where
  liftShowsPrec shw _ p (Positive a) = shw p a

-------------------------------------------------------------------------------
-- NonNegative from smallcheck

instance (Num a, Ord a, Arbitrary a) => Arbitrary (NonNegative a) where
  arbitrary = NonNegative <$> (arbitrary `suchThat` (>= 0))
  shrink (NonNegative x) = NonNegative <$> filter (>= 0) (shrink x)

instance Eq1 NonNegative where
  liftEq eq (NonNegative a) (NonNegative b) = a `eq` b

instance Ord1 NonNegative where
  liftCompare cmp (NonNegative a) (NonNegative b) = a `cmp` b

instance Show1 NonNegative where
  liftShowsPrec shw _ p (NonNegative a) = shw p a

-------------------------------------------------------------------------------
-- Huge

newtype Huge a = Huge { getHuge :: a }
  deriving (Eq, Ord, Read, Show, Num, Enum, Bounded, Integral, Real, Functor, Foldable, Traversable)

instance (Num a, Arbitrary a) => Arbitrary (Huge a) where
  arbitrary = do
    Positive l <- arbitrary
    ds <- vector l
    return $ Huge $ foldl1 (\acc n -> acc * 2 ^ (63 :: Int) + n) ds

instance Eq1 Huge where
  liftEq eq (Huge a) (Huge b) = a `eq` b

instance Ord1 Huge where
  liftCompare cmp (Huge a) (Huge b) = a `cmp` b

instance Show1 Huge where
  liftShowsPrec shw _ p (Huge a) = shw p a

-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Humoungous

newtype Humoungous a = Humoungous { getHumoungous :: a }
  deriving (Eq, Ord, Read, Show, Num, Enum, Bounded, Integral, Real, Functor, Foldable, Traversable)

instance (Num a, Arbitrary a) => Arbitrary (Humoungous a) where
  arbitrary = do
    Positive l <- arbitrary
    ds <- vector l
    return $ Humoungous $ foldl1 (\acc n -> acc * 2 ^ (127 :: Int) + n) ds

instance Eq1 Humoungous where
  liftEq eq (Humoungous a) (Humoungous b) = a `eq` b

instance Ord1 Humoungous where
  liftCompare cmp (Humoungous a) (Humoungous b) = a `cmp` b

instance Show1 Humoungous where
  liftShowsPrec shw _ p (Humoungous a) = shw p a

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Gargantuan

newtype Gargantuan a = Gargantuan { getGargantuan :: a }
  deriving (Eq, Ord, Read, Show, Num, Enum, Bounded, Integral, Real, Functor, Foldable, Traversable)

instance (Num a, Arbitrary a) => Arbitrary (Gargantuan a) where
  arbitrary = do
    Positive l <- arbitrary
    ds <- vector l
    return $ Gargantuan $ foldl1 (\acc n -> acc * 2 ^ (255 :: Int) + n) ds

instance Eq1 Gargantuan where
  liftEq eq (Gargantuan a) (Gargantuan b) = a `eq` b

instance Ord1 Gargantuan where
  liftCompare cmp (Gargantuan a) (Gargantuan b) = a `cmp` b

instance Show1 Gargantuan where
  liftShowsPrec shw _ p (Gargantuan a) = shw p a

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Googolplex

newtype Googolplex a = Googolplex { getGoogolplex :: a }
  deriving (Eq, Ord, Read, Show, Num, Enum, Bounded, Integral, Real, Functor, Foldable, Traversable)

instance (Num a, Arbitrary a) => Arbitrary (Googolplex a) where
  arbitrary = do
    Positive l <- arbitrary
    ds <- vector l
    return $ Googolplex $ foldl1 (\acc n -> acc * 2 ^ (511 :: Int) + n) ds

instance Eq1 Googolplex where
  liftEq eq (Googolplex a) (Googolplex b) = a `eq` b

instance Ord1 Googolplex where
  liftCompare cmp (Googolplex a) (Googolplex b) = a `cmp` b

instance Show1 Googolplex where
  liftShowsPrec shw _ p (Googolplex a) = shw p a

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- FZeight

newtype FZeight a = FZeight { getFZeight :: a }
  deriving (Eq, Ord, Read, Show, Num, Enum, Bounded, Integral, Real, Functor, Foldable, Traversable)

instance (Num a, Arbitrary a) => Arbitrary (FZeight a) where
  arbitrary = do
    Positive l <- arbitrary
    ds <- vector l
    return $ FZeight $ foldl1 (\acc n -> acc * 2 ^ (1023 :: Int) + n) ds

instance Eq1 FZeight where
  liftEq eq (FZeight a) (FZeight b) = a `eq` b

instance Ord1 FZeight where
  liftCompare cmp (FZeight a) (FZeight b) = a `cmp` b

instance Show1 FZeight where
  liftShowsPrec shw _ p (FZeight a) = shw p a

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Boogol

newtype Boogol a = Boogol { getBoogol :: a }
  deriving (Eq, Ord, Read, Show, Num, Enum, Bounded, Integral, Real, Functor, Foldable, Traversable)

instance (Num a, Arbitrary a) => Arbitrary (Boogol a) where
  arbitrary = do
    Positive l <- arbitrary
    ds <- vector l
    return $ Boogol $ foldl1 (\acc n -> acc * 2 ^ (2046 :: Int) + n) ds

instance Eq1 Boogol where
  liftEq eq (Boogol a) (Boogol b) = a `eq` b

instance Ord1 Boogol where
  liftCompare cmp (Boogol a) (Boogol b) = a `cmp` b

instance Show1 Boogol where
  liftShowsPrec shw _ p (Boogol a) = shw p a

-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- BoogolZeight

newtype BoogolZeight a = BoogolZeight { getBoogolZeight :: a }
  deriving (Eq, Ord, Read, Show, Num, Enum, Bounded, Integral, Real, Functor, Foldable, Traversable)

instance (Num a, Arbitrary a) => Arbitrary (BoogolZeight a) where
  arbitrary = do
    Positive l <- arbitrary
    ds <- vector l
    return $ BoogolZeight $ foldl1 (\acc n -> acc * 2 ^ (4096 :: Int) + n) ds 

instance Eq1 BoogolZeight where
  liftEq eq (BoogolZeight a) (BoogolZeight b) = a `eq` b

instance Ord1 BoogolZeight where
  liftCompare cmp (BoogolZeight a) (BoogolZeight b) = a `cmp` b

instance Show1 BoogolZeight where
  liftShowsPrec shw _ p (BoogolZeight a) = shw p a

-------------------------------------------------------------------------------

-- Power

newtype Power a = Power { getPower :: a }
  deriving (Eq, Ord, Read, Show, Num, Enum, Bounded, Integral, Real, Functor, Foldable, Traversable)

instance (Monad m, Num a, Ord a, Serial m a) => Serial m (Power a) where
  series = Power <$> series `suchThatSerial` (> 0)

instance (Num a, Ord a, Integral a, Arbitrary a) => Arbitrary (Power a) where
  arbitrary = Power <$> arbitrarySizedNatural `suchThat` (> 0)
  shrink (Power x) = Power <$> filter (> 0) (shrink x)

instance Eq1 Power where
  liftEq eq (Power a) (Power b) = a `eq` b

instance Ord1 Power where
  liftCompare cmp (Power a) (Power b) = a `cmp` b

instance Show1 Power where
  liftShowsPrec shw _ p (Power a) = shw p a

-------------------------------------------------------------------------------
-- Odd

newtype Odd a = Odd { getOdd :: a }
  deriving (Eq, Ord, Read, Show, Num, Enum, Bounded, Integral, Real, Functor, Foldable, Traversable)

instance (Monad m, Serial m a, Integral a) => Serial m (Odd a) where
  series = Odd <$> series `suchThatSerial` odd

instance (Integral a, Arbitrary a) => Arbitrary (Odd a) where
  arbitrary = Odd <$> (arbitrary `suchThat` odd)
  shrink (Odd x) = Odd <$> filter odd (shrink x)

instance Eq1 Odd where
  liftEq eq (Odd a) (Odd b) = a `eq` b

instance Ord1 Odd where
  liftCompare cmp (Odd a) (Odd b) = a `cmp` b

instance Show1 Odd where
  liftShowsPrec shw _ p (Odd a) = shw p a

-------------------------------------------------------------------------------
-- Utils

suchThatSerial :: Series m a -> (a -> Bool) -> Series m a
suchThatSerial s p = s >>= \x -> if p x then pure x else empty
