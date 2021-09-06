{-# LANGUAGE OverloadedStrings #-}

module PLFA.Build.Metadata
  ( Metadata
  , getMetadata
  , getPermalink
  ) where

import Data.Aeson.Types
import Data.ByteString qualified as B
import Data.Frontmatter (parseYamlFrontmatterEither)
import Data.HashMap.Strict qualified as H
import Data.Text qualified as T
import PLFA.Util (Url, liftEither)

type Metadata = Object

getMetadata :: FilePath -> IO Metadata
getMetadata inputFile = do
  contents <- B.readFile inputFile
  value <-
    liftEither (\msg -> "Parse error in " <> inputFile <> ": " <> msg) $
      parseYamlFrontmatterEither contents
  case value of
    Object object -> return object
    _             -> fail $ "Expected metadata object, found " <> show value

getPermalink :: Metadata -> IO Url
getPermalink metadata =
  case H.lookup "permalink" metadata of
    Just (String permalink) -> return (T.unpack permalink)
    Nothing                 -> fail $ "Key 'permalink' not found in\n" <> show metadata
    Just value              -> fail $ "Key 'permalink' not a string in\n" <> show metadata
