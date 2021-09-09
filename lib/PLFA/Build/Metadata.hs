module PLFA.Build.Metadata
  ( Metadata (..),
    readYaml',
    readYaml,
    readYamlFrontmatter',
    readYamlFrontmatter,
    readFileWithMetadata',
    readFileWithMetadata,
    (^.),
    (.~),
    (&),
    Author (..),
    Contributor (..),
    lastModified,
    dateFromFilePath,
    sourceFile,
    teaser,
    addTitleVariants,
    resolveIncludes
  ) where

import Data.Aeson (encode)
import Data.Aeson.Types
import Data.ByteString qualified as B
import Data.Frontmatter as Frontmatter (Result, IResult (..), parseYamlFrontmatter)
import Data.Function ((&))
import Data.HashMap.Strict qualified as H
import Data.Text qualified as T
import Data.Time.Format (formatTime, defaultTimeLocale)
import Data.Vector ()
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
readYamlFrontmatter inputFile =
  snd <$> readFileWithMetadata inputFile

-- | Read a file with its YAML frontmatter and return both as a Shake action.
readFileWithMetadata' :: FromJSON a => FilePath -> Action (Text, a)
readFileWithMetadata' inputFile = do
  need [inputFile]
  liftIO $ readFileWithMetadata inputFile

-- | Read a file with its YAML frontmatter and return both.
readFileWithMetadata :: FromJSON a => FilePath -> IO (Text, a)
readFileWithMetadata inputFile = do
  contents <- B.readFile inputFile
  withResult (parseYamlFrontmatter contents)
  where
    withResult :: (FromJSON a) => Frontmatter.Result a -> IO (Text, a)
    withResult (Done body metadata) = do tbody <- toText body; return (tbody, metadata)
    withResult (Fail _ _ message)   = fail message
    withResult (Partial k)          = withResult (k "")

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
-- Metadata fields
--------------------------------------------------------------------------------

-- | Create a metadata object containing the file modification time.
--
--   Adapted from hakyll's 'Hakyll.Web.Template.Context.modificationTimeField'.
lastModified :: FilePath -> Text -> Action Metadata
lastModified inputFile key = liftIO $ do
  time <- getModificationTime inputFile
  let modified = formatTime defaultTimeLocale "%0Y-%m-%dT%H:%M:%SZ" time
  return $ mempty & key .~ modified


-- | Create a metadata object containing the source path.
sourceFile :: FilePath -> Text -> Metadata
sourceFile inputFile key =
  mempty & key .~ inputFile


-- | Create a metadata object containing the date inferred from the file path.
dateFromFilePath :: FilePath -> Text -> Metadata
dateFromFilePath inputFile key =
  case T.splitOn "-" $ T.pack inputFile of
    (year : month : day : _) -> mempty & key .~ T.concat [year, "-", month, "-", day]
    _                        -> mempty


-- | Create a metadata object containing a teaser constructed from the first argument.
teaser :: Text -> Text -> Metadata
teaser body key
  | T.null rest = mempty
  | otherwise   = mempty & key .~ teaserBody
  where
    (teaserBody, rest) = T.breakOn "<!--more-->" body


-- | Add running title and subtitle, if title contains a colon.
addTitleVariants :: Metadata -> Metadata
addTitleVariants metadata = case metadata ^. "title" of
  Nothing    -> metadata
  Just title ->
    let (titlerunning, subtitle) = T.breakOn ":" title in
      if T.null subtitle then
        metadata -- No titlerunning/subtitle distinction
      else
        metadata & "titlerunning" .~ T.strip titlerunning
                 & "subtitle"     .~ T.strip (T.drop 1 subtitle)


-- | Resolve 'include' fields by including metadata from files.
resolveIncludes :: (FilePath -> Action Metadata) -> Metadata -> Action Metadata
resolveIncludes reader (Metadata object) = fromValue <$> walkValue (Object object)
  where
    fromValue :: Value -> Metadata
    fromValue (Object object) = Metadata object

    walkValue :: Value -> Action Value
    walkValue (Object object) = do
      object' <- resolveInclude object
      Object <$> traverse walkValue object'
    walkValue (Array array)   = Array <$> traverse walkValue array
    walkValue value           = return value

    resolveInclude :: Object -> Action Object
    resolveInclude object =
      case Metadata object ^. "include" of
        Nothing       -> return object
        Just filePath -> do
          Metadata includedObject <- reader filePath
          return (object <> includedObject)
