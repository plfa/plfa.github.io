module PLFA.Build.Metadata
  ( Metadata (..),
    readYaml',
    readYaml,
    writeYaml',
    writeYaml,
    readYamlFrontmatter',
    readYamlFrontmatter,
    readFileWithMetadata',
    readFileWithMetadata,
    (^.),
    (.~),
    (&),
    Author (..),
    Contributor (..),
    lastModifiedField,
    dateFromFileNameField,
    currentDateField,
    constField,
    teaserField,
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
import Data.Time
import Data.Time.Format.ISO8601 (iso8601Show)
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


--------------------------------------------------------------------------------
-- Reading and writing
--------------------------------------------------------------------------------

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


writeYaml' :: ToJSON a => FilePath -> a -> Action ()
writeYaml' outputFile a = liftIO $ Y.encodeFile outputFile a

writeYaml :: ToJSON a => FilePath -> a -> IO ()
writeYaml outputFile a = Y.encodeFile outputFile a


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

prettyDate :: FormatTime t => t -> String
prettyDate time = formatTime defaultTimeLocale "%a %-d %b, %Y" time

-- | Create a metadata object containing the file modification time.
--
--   Adapted from hakyll's 'Hakyll.Web.Template.Context.modificationTimeField'.
lastModifiedField :: FilePath -> Text -> Action Metadata
lastModifiedField inputFile key = liftIO $ do
  modificationTime <- getModificationTime inputFile
  return $ constField key (iso8601Show modificationTime)

-- | Create a metadata object containing the current date.
currentDateField :: Text -> Action Metadata
currentDateField key = liftIO $ do
  currentTime <- getCurrentTime
  return $ constField key (prettyDate currentTime)

-- | Create a metadata object containing the date inferred from the file path.
dateFromFileNameField :: FilePath -> Text -> Metadata
dateFromFileNameField inputFile key
  | length chunks >= 3 = constField key (prettyDate date)
  | otherwise          = mempty
  where
    inputFileName = takeFileName inputFile
    chunks        = map T.unpack $ T.splitOn "-" $ T.pack inputFileName
    ~(y:m:d:_)    = map read chunks
    date          = fromGregorian y (fromInteger m) (fromInteger d)

-- | Create a metadata object containing the provided value.
constField :: ToJSON a => Text -> a -> Metadata
constField key a = mempty & key .~ a

-- | Create a metadata object containing a teaser constructed from the first argument.
teaserField :: Text -> Text -> Metadata
teaserField body key
  | T.null rest = mempty
  | otherwise   = constField key teaserBody
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
