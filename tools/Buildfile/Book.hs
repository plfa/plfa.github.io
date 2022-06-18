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
    partChapters :: [Chapter],
    partFrontmatter :: Bool,
    partMainmatter :: Bool,
    partBackmatter :: Bool
  }
  deriving (Show)

instance FromJSON Part where
  parseJSON = withObject "Part" $ \v ->
    Part
      <$> v .: "title"
      <*> v .: "chapter"
      <*> v .:? "frontmatter" .!= False
      <*> v .:? "mainmatter" .!= False
      <*> v .:? "backmatter" .!= False

instance ToJSON Part where
  toJSON Part {..} =
    object
      [ "title" .= partTitle,
        "chapter" .= partChapters,
        "frontmatter" .= partFrontmatter,
        "mainmatter" .= partMainmatter,
        "backmatter" .= partBackmatter
      ]

data Chapter = Chapter
  { chapterInclude :: FilePath,
    chapterEpubType :: Text
  }
  deriving (Show)

instance FromJSON Chapter where
  parseJSON = withObject "Chapter" $ \v ->
    Chapter
      <$> v .: "include"
      <*> v .:? "epub-type" .!= "bodymatter"

instance ToJSON Chapter where
  toJSON Chapter {..} =
    object
      [ "include" .= chapterInclude,
        "epub-type" .= chapterEpubType
      ]

newtype ChapterTable = ChapterTable {chapterBimap :: Bimap.Bimap FilePath FilePath}

fromBook :: Book -> ChapterTable
fromBook book = ChapterTable {..}
  where
    chapterBimap :: Bimap.Bimap FilePath FilePath
    chapterBimap = Bimap.fromList $ zip chapterList (tail chapterList)

    chapterList :: [FilePath]
    chapterList = flattenBook book
      where
        flattenBook :: Book -> [FilePath]
        flattenBook = flattenPart <=< bookParts

        flattenPart :: Part -> [FilePath]
        flattenPart = flattenChapter <=< partChapters

        flattenChapter :: Chapter -> [FilePath]
        flattenChapter = return . chapterInclude

nextChapter :: ChapterTable -> FilePath -> Maybe FilePath
nextChapter ChapterTable {..} src = Bimap.lookup src chapterBimap

previousChapter :: ChapterTable -> FilePath -> Maybe FilePath
previousChapter ChapterTable {..} src = Bimap.lookupR src chapterBimap
