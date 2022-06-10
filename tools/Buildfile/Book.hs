module Buildfile.Book where

import Data.Aeson.Types (FromJSON (..), withObject, (.!=), (.:), (.:?))
import Data.Bimap qualified as Bimap
import Data.Text (Text)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Control.Monad ((<=<))

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

data Section = Section
  { sectionInclude :: FilePath
  , sectionEpubType :: Text
  }
  deriving (Show)

instance FromJSON Section where
  parseJSON = withObject "Section" $ \v ->
    Section
      <$> v .: "include"
      <*> v .:? "epub-type" .!= "bodymatter"



newtype SectionTable = SectionTable { sectionBimap :: Bimap.Bimap FilePath FilePath }

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
nextSection SectionTable{..} src = Bimap.lookup src sectionBimap

previousSection :: SectionTable -> FilePath -> Maybe FilePath
previousSection SectionTable{..} src = Bimap.lookupR src sectionBimap