module Buildfile.Book where

import Control.Monad ((<=<))
import Data.Aeson.Types (FromJSON (..), ToJSON (..), object, withObject, (.!=), (.:), (.:?), (.=))
import Data.Bimap qualified as Bimap
import Data.Text (Text)

newtype Book = Book
  { bookParts :: [Part]
  }
  deriving (Show)

instance FromJSON Book where
  parseJSON = withObject "Book" $ \v ->
    Book
      <$> v .: "part"

instance ToJSON Book where
  toJSON Book {..} =
    object
      [ "part" .= bookParts
      ]

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

instance ToJSON Part where
  toJSON Part {..} =
    object
      [ "title" .= partTitle,
        "section" .= partSections,
        "frontmatter" .= partFrontmatter,
        "mainmatter" .= partMainmatter,
        "backmatter" .= partBackmatter
      ]

data Section = Section
  { sectionInclude :: FilePath,
    sectionEpubType :: Text
  }
  deriving (Show)

instance FromJSON Section where
  parseJSON = withObject "Section" $ \v ->
    Section
      <$> v .: "include"
      <*> v .:? "epub-type" .!= "bodymatter"

instance ToJSON Section where
  toJSON Section {..} =
    object
      [ "include" .= sectionInclude,
        "epub-type" .= sectionEpubType
      ]

newtype SectionTable = SectionTable {sectionBimap :: Bimap.Bimap FilePath FilePath}

fromBook :: Book -> SectionTable
fromBook book = SectionTable {..}
  where
    sectionBimap :: Bimap.Bimap FilePath FilePath
    sectionBimap = Bimap.fromList $ zip sectionList (tail sectionList)

    sectionList :: [FilePath]
    sectionList = flattenBook book
      where
        flattenBook :: Book -> [FilePath]
        flattenBook = flattenPart <=< bookParts

        flattenPart :: Part -> [FilePath]
        flattenPart = flattenSection <=< partSections

        flattenSection :: Section -> [FilePath]
        flattenSection = return . sectionInclude

nextSection :: SectionTable -> FilePath -> Maybe FilePath
nextSection SectionTable {..} src = Bimap.lookup src sectionBimap

previousSection :: SectionTable -> FilePath -> Maybe FilePath
previousSection SectionTable {..} src = Bimap.lookupR src sectionBimap