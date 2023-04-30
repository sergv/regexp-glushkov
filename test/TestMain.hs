-- |
-- Module:     TestMain
-- Copyright:  (c) Sergey Vinokurov 2023
-- License:    Apache-2.0 (see LICENSE)
-- Maintainer: serg.foo@gmail.com

{-# LANGUAGE ApplicativeDo        #-}
{-# LANGUAGE ImportQualifiedPost  #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module TestMain (main) where

import Data.List qualified as L

import Text.Regex.Glushkov

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [properties, unitTests]

properties :: TestTree
properties = testGroup "Properties"
  [ QC.testProperty "matches" $
      \(RegexTestCase r strs) ->
        label ("size = " ++ show (L.length strs)) $
        all (match r) strs
  , QC.testProperty "reverse matches" $
      \(RegexTestCase r strs) ->
        label ("size = " ++ show (L.length strs)) $
        all (match (reversed r) . reverse) strs
  ]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  []
  -- [ testCase "List comparison (different length)" $
  --     [1, 2, 3] `compare` [1,2] @?= GT
  --
  -- -- the following test does not hold
  -- , testCase "List comparison (same length)" $
  --     [1, 2, 3] `compare` [1,2,2] @?= LT
  -- ]


-- removeConjunctions :: Rx -> Rx
-- removeConjunctions r = mapRx f r
--     where
--         f (Rx { reg = (And p q) }) = (True,
--                                       rnot (ror (rnot (removeConjunctions p))
--                                                 (rnot (removeConjunctions q))))
--         f rx                       = (False, rx)

alphabet :: [Char]
alphabet = ['a', 'b', 'c', 'd', 'e']

charGen :: Gen Char
charGen = elements alphabet

instance Arbitrary (f (Fix f)) => Arbitrary (Fix f) where
  arbitrary = Fix <$> arbitrary
  shrink = genericShrink

instance Arbitrary (RxF Rx) where
  arbitrary = do
    Fix x <- frequency
      [ (1, pure reps)
      , (3, pure rall)
      , (3, rsym <$> charGen)
      , (1, ror <$> smaller arbitrary <*> smaller arbitrary)
      , (2, rseq <$> smaller arbitrary <*> smaller arbitrary)
      , (1, rrep <$> smaller arbitrary)
      , (1, rand <$> smaller arbitrary <*> smaller arbitrary)
      ]
    pure x
    where
      smaller = scale (\x -> x * 5 `div` 10)

  shrink = genericShrink

instance Arbitrary a => Arbitrary (RegexF a) where
  arbitrary = error "Not defined, only for shrinking"
  shrink = genericShrink


data RegexTestCase a = RegexTestCase a [String]
  deriving (Eq, Ord, Show)

instance {-# OVERLAPPING #-} Show (RegexTestCase Rx) where
  show (RegexTestCase r strs) =
    show (RegexTestCase (cata (Fix . reg) r) strs :: RegexTestCase Regex)

maxLen :: Int
maxLen = 6

generateStrs :: Rx -> [String]
generateStrs r = generateStrings maxLen alphabet r

instance Arbitrary (RegexTestCase Rx) where
  arbitrary = do
    r <- arbitrary
    pure $ RegexTestCase r $ generateStrs r

  shrink (RegexTestCase r _) =
    [RegexTestCase r' $ generateStrs r' | r' <- shrink r]
