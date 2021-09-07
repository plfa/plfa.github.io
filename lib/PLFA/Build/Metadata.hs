module PLFA.Build.Metadata
  ( Metadata (..),
    readYaml',
    readYaml,
    readYamlFrontmatter',
    readYamlFrontmatter,
    (^.),
    (.~),
    (&),
    Author (..),
    Contributor (..),
    lastModified,
    sourceFile
  ) where

import Data.Aeson (encode)
import Data.Aeson.Types
import Data.ByteString qualified as B
import Data.Frontmatter (parseYamlFrontmatterEither)
import Data.Function ((&))
import Data.HashMap.Strict qualified as H
import Data.Text qualified as T
import Data.Time.Format (formatTime, defaultTimeLocale)
import Data.Yaml qualified as Y
import System.Directory
import System.IO.Unsafe (unsafePerformIO)
import PLFA.Build.Prelude hiding (Error)

--------------------------------------------------------------------------------
-- Metadata
--------------------------------------------------------------------------------

newtype Metadata = Metadata Object


infixr 4 .~

-- | Set a value on a metadata object.
(.~) :: ToJSON a => Text -> a -> Metadata -> Metadata
(key .~ value) (Metadata obj) = Metadata $ H.insert key (toJSON value) obj


infixl 8 ^.

-- | Get a value from a metadata object.
(^.) :: (MonadFail m, FromJSON a) => Metadata -> Text -> m a
metadata@(Metadata obj) ^. key = do
  let msg = "Key '" <> T.unpack key <> "' not found in metadata:\n" <> show metadata
  v <- liftMaybe msg $ H.lookup key obj
  a <- liftResult $ fromJSON v
  return a


-- | Read a YAML file as a Shake action.
readYaml' :: FromJSON a => FilePath -> Action a
readYaml' inputFile = do
  need [inputFile]
  liftIO $ readYaml inputFile

-- | Read a YAML file.
readYaml :: FromJSON a => FilePath -> IO a
readYaml inputFile = Y.decodeFileThrow inputFile

-- | Read the YAML frontmatter from a file as a Shake action.
readYamlFrontmatter' :: FromJSON a => FilePath -> Action a
readYamlFrontmatter' inputFile = do
  need [inputFile]
  liftIO $ readYamlFrontmatter inputFile

-- | Read the YAML frontmatter from a file.
readYamlFrontmatter :: FromJSON a => FilePath -> IO a
readYamlFrontmatter inputFile = do
  contents <- B.readFile inputFile
  liftEither (\msg -> "Parse error in " <> inputFile <> ": " <> msg) $
    parseYamlFrontmatterEither contents


-- * Instances

instance Show Metadata where
  show (Metadata obj) = T.unpack $ unsafePerformIO $ toTextLazy $ encode obj

instance ToJSON Metadata where
  toJSON (Metadata obj) = Object obj

instance FromJSON Metadata where
  parseJSON = withObject "Metadata" $ \v -> Metadata <$> return v

instance Semigroup Metadata where
  (Metadata m1) <> (Metadata m2) = Metadata (H.union m1 m2)

instance Monoid Metadata where
  mempty = Metadata H.empty


--------------------------------------------------------------------------------
-- Authors & Contributors
--------------------------------------------------------------------------------

data Author = Author
  { authorName          :: Text
  , authorEmail         :: Text
  , authorGithub        :: Maybe Text
  , authorTwitter       :: Maybe Text
  , authorCorresponding :: Bool
  }

instance ToJSON Author where
  toJSON Author{..} =
    object [ "name"          .= authorName
           , "email"         .= authorEmail
           , "github"        .= authorGithub
           , "twitter"       .= authorTwitter
           , "corresponding" .= authorCorresponding
           ]

instance FromJSON Author where
  parseJSON = withObject "Author" $ \v -> Author
    <$> v .:  "name"
    <*> v .:  "email"
    <*> v .:? "github"
    <*> v .:? "twitter"
    <*> v .:  "corresponding"

data Contributor = Contributor
  { contributorName   :: Text
  , contributorGithub :: Text
  , contributorCount  :: Int
  }

instance ToJSON Contributor where
  toJSON Contributor{..} =
    object [ "name"    .= contributorName
           , "github"  .= contributorGithub
           , "count"   .= contributorCount
           ]

instance FromJSON Contributor where
  parseJSON = withObject "Contributor" $ \v -> Contributor
    <$> v .: "name"
    <*> v .: "github"
    <*> v .: "count"


--------------------------------------------------------------------------------
-- Modification time
--------------------------------------------------------------------------------

-- | Adapted from hakyll's 'Hakyll.Web.Template.Context.modificationTimeField'
lastModified :: FilePath -> Text -> Action Metadata
lastModified inputFile key = liftIO $ do
  time <- getModificationTime inputFile
  let modified = formatTime defaultTimeLocale "%0Y-%m-%dT%H:%M:%SZ" time
  return $ mempty & key .~ modified


--------------------------------------------------------------------------------
-- Source file
--------------------------------------------------------------------------------

sourceFile :: FilePath -> Text -> Metadata
sourceFile inputFile key =
  mempty & key .~ inputFile
