-- |
-- Module:     RegexRunner
-- Copyright:  (c) Sergey Vinokurov 2023
-- License:    Apache-2.0 (see LICENSE)
-- Maintainer: serg.foo@gmail.com

{-# LANGUAGE ApplicativeDo   #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE RecordWildCards #-}

module RegexRunner (main) where

import Data.Bifunctor
import Data.Foldable
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Options.Applicative
import System.File.OsPath
import System.OsPath

import Text.Regex.Glushkov

data Config = Config
  { cfgRegex    :: !String
  , cfgInputFile :: OsPath
  }

optsParser :: Parser Config
optsParser = do
  cfgRegex <- strOption $
    long "regex" <>
    metavar "RE" <>
    help "Regexp to look for within input file"
  cfgInputFile <- option (eitherReader (bimap show id . encodeUtf)) $
    long "input" <>
    metavar "FILE" <>
    help "An input file"
  pure Config{..}

progInfo :: ParserInfo Config
progInfo = info
  (helper <*> optsParser)
  (fullDesc <> header "My new shiny program!")

main :: IO ()
main = do
  Config{cfgRegex, cfgInputFile} <-
    customExecParser (prefs (showHelpOnEmpty <> noBacktrack <> multiSuffix "*")) progInfo

  contents <- T.decodeUtf8 <$> readFile' cfgInputFile

  let regex   = fromString cfgRegex
      matches = allMatches regex contents

  putStrLn $ "Regex = " ++ show regex
  putStrLn $ "Input length = " ++ show (T.length contents)
  traverse_ print matches

  pure ()

