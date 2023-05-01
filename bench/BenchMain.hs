-- |
-- Module:     BenchMain
-- Copyright:  (c) Sergey Vinokurov 2023
-- License:    Apache-2.0 (see LICENSE)
-- Maintainer: serg.foo@gmail.com

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module BenchMain (main) where

import Control.DeepSeq
import Control.Exception
import Data.ByteString.Char8 qualified as C8
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Prettyprinter
import Prettyprinter.Combinators
import Test.Tasty.Bench

import Text.Regex.Glushkov qualified as Glushkov
import Text.Regex.TDFA qualified as TDFA
import Text.Regex.TDFA.Text qualified as TDFA

import Text.Regex.Base.RegexLike

-- import Data.ByteString.Unsafe qualified as Unsafe

compileRe :: Text -> TDFA.Regex
compileRe = compileReWithOpts compOpts
  where
    compOpts = TDFA.defaultCompOpt
      { TDFA.multiline     = False
      , TDFA.caseSensitive = True
      }

compileReWithOpts
  :: TDFA.CompOption -> Text -> TDFA.Regex
compileReWithOpts compOpts re =
  case TDFA.compile compOpts execOpts re of
    Left err -> error $ renderString $
      "Failed to compile regular expression:" <+> pretty err <> ":" <> line <> pretty re
    Right x  -> x
  where
    execOpts = TDFA.defaultExecOpt
      { TDFA.captureGroups = False
      }

reAllByteStringMatches
  :: TDFA.Regex -> C8.ByteString -> AllMatches [] (MatchOffset, MatchLength)
reAllByteStringMatches = TDFA.match

reAllTextMatches
  :: TDFA.Regex -> Text -> AllMatches [] (MatchOffset, MatchLength)
reAllTextMatches = TDFA.match

reAllStringMatches
  :: TDFA.Regex -> [Char] -> AllMatches [] (MatchOffset, MatchLength)
reAllStringMatches = TDFA.match

-- extractMatches :: C8.ByteString -> AllMatches [] (MatchOffset, MatchLength) -> [C8.ByteString]
-- extractMatches str ms
--   = map (\(offset, len) -> Unsafe.unsafeTake len $ Unsafe.unsafeDrop offset str)
--   $ getAllMatches ms

deriving instance NFData (f b) => NFData (AllMatches f b)

instance NFData Glushkov.Match

main :: IO ()
main = do
  strC8 <- C8.readFile "src/Text/Regex/Glushkov.hs"
  let strText = T.decodeUtf8 strC8
      strList = T.unpack strText

      re :: Text
      re = "Regex"

      reTDFA     = compileRe re
      reGlushkov = Glushkov.fromString $ T.unpack re

  evaluate $ rnf strC8
  evaluate $ rnf strText
  evaluate $ rnf strList

  let tdfaLen     = length $ getAllMatches $ reAllByteStringMatches reTDFA strC8
      glushkovLen = length $ Glushkov.allMatches reGlushkov strText

  putStrLn $ "tdfaLen = " ++ show tdfaLen ++ ", glushkovLen = " ++ show glushkovLen

  defaultMain
    [                      bench "tdfa bs"     $ nf (reAllByteStringMatches reTDFA) strC8
    ,                      bench "tdfa text"   $ nf (reAllTextMatches reTDFA) strText
    ,                      bench "tdfa string" $ nf (reAllStringMatches reTDFA) strList
    , bcompare "tdfa bs" $ bench "glushkov"    $ nf (Glushkov.allMatches reGlushkov) strText
    ]
