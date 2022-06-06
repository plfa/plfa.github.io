module Buildfile.Book where

import Data.Aeson.Types (FromJSON (..), withObject, (.!=), (.:), (.:?))
import Data.Text (Text)

newtype Book = Book
  { bookParts :: [Part]
  }
  deriving (Show)

instance FromJSON Book where
  parseJSON = withObject "Book" $ \v ->
    Book
      <$> v .: "part"

data Part = Part
  { partTitle :: Text,
    partSections :: [Section],
    partFrontmatter :: Bool,
    partMainmatter :: Bool,
    partBackmatter :: Bool
  }
  deriving (Show)

instance FromJSON Part where
  parseJSON = withObject "Part" $ \v ->
    Part
      <$> v .: "title"
      <*> v .: "section"
      <*> v .:? "frontmatter" .!= False
      <*> v .:? "mainmatter" .!= False
      <*> v .:? "backmatter" .!= False

newtype Section = Section
  { sectionInclude :: FilePath
  }
  deriving (Show)

instance FromJSON Section where
  parseJSON = withObject "Section" $ \v ->
    Section
      <$> v .: "include"