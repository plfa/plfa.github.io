{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where

import Buildfile.Author (Author)
import Buildfile.Configuration
import Buildfile.Contributor (Contributor (..))
import Conduit (MonadIO (liftIO), MonadTrans (lift))
import Control.Applicative ((<|>))
import Control.Concurrent.MVar (MVar, modifyMVar, modifyMVar_, newMVar, withMVar)
import Control.Exception (Exception (..), throwIO)
import Control.Monad (join, unless, when, (<=<))
import Control.Monad.IO.Class (MonadIO)
import Data.Aeson.Types
import Data.Conduit
  ( ConduitT,
    awaitForever,
    runConduit,
    sequenceConduits,
    yield,
    (.|),
  )
import Codec.Text.Detect qualified as Codec
import Data.ByteString qualified as ByteString
import Data.ByteString.Lazy qualified as ByteStringLazy
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text.ICU.Convert qualified as Convert
import Data.Conduit.Combinators (headDef)
import Data.Conduit.Combinators qualified as Conduit
import Data.Conduit.List (sourceList)
import Data.Foldable (for_)
import Data.Function (on)
import Data.Git.Monad (GitM, GitMonad (..), Resolvable (resolve), getCommit, headGet, headResolv, withCurrentRepo)
import Data.Git.Ref (HashAlgorithm, Ref, SHA1)
import Data.Git.Types (Commit (..), Person (..))
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.List (sortBy)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String (IsString (..))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding (decodeUtf8)
import Data.Vector qualified as Vector
import GitHub qualified as GH
import Shoggoth.Metadata (readYamlIO)
import Shoggoth.Prelude (getDirectoryFilesIO, (</>))
import System.Environment (lookupEnv)
import System.IO (hPutStrLn, stderr)

instance MonadIO GitM where
  liftIO = liftGit

toText :: ByteString.ByteString -> IO Text
toText bs = toTextLazy (ByteStringLazy.fromStrict bs)

toTextLazy :: ByteStringLazy.ByteString -> IO Text
toTextLazy lbs = do
  let maybeEncoding = Codec.detectEncodingName lbs
  let encoding = fromMaybe "" maybeEncoding
  converter <- Convert.open encoding (Just True)
  return $ Convert.toUnicode converter (ByteStringLazy.toStrict lbs)

readAuthors :: FilePath -> IO [Author]
readAuthors dir = do
  authorFiles <- getDirectoryFilesIO dir ["*.yml"]
  authors <- traverse (\src -> readYamlIO $ dir </> src) authorFiles
  return (authors :: [Author])

readContributors :: FilePath -> IO [Contributor]
readContributors dir = do
  contributorFiles <- getDirectoryFilesIO dir ["*.yml"]
  contributors <- traverse (\src -> readYamlIO $ dir </> src) contributorFiles
  let sortedContributors = sortBy (compare `on` contributorCommits) contributors
  return (sortedContributors :: [Contributor])

-- | Get an authentication token from the environment.
getAuth :: IO GH.Auth
getAuth = do
  mtoken <- lookupEnv "GITHUB_TOKEN"
  case mtoken of
    Nothing -> error "Please set GITHUB_TOKEN"
    Just token -> return (GH.OAuth . fromString $ token)

type RefCache = Set (Ref SHA1)

streamGitCommitsFrom :: GitMonad m => MVar RefCache -> ConduitT (Ref SHA1) (Commit SHA1) m ()
streamGitCommitsFrom refCacheVar = do
  awaitForever $ \ref -> do
    seen <-
      lift . liftGit $
        modifyMVar refCacheVar $ \refCache ->
          return (Set.insert ref refCache, ref `Set.member` refCache)
    unless seen $ do
      maybeCommit <- lift (getCommit ref)
      case maybeCommit of
        Nothing -> return ()
        Just commit -> do
          yield commit
          sourceList (commitParents commit) .| streamGitCommitsFrom refCacheVar

streamGitHead :: GitMonad m => ConduitT () (Ref SHA1) m ()
streamGitHead = lift headResolv >>= maybe (return ()) yield

-- searchUsersR :: Text -> FetchCount -> Request k (SearchResult SimpleUser)
-- executeRequest :: (AuthMethod am, ParseResponse mt a) => am -> GenRequest mt rw a -> IO (Either Error a)

personToContributor :: Person -> IO Contributor
personToContributor person = do
  let contributorName = toText (personName person)
  let contributorEmail = toText (personEmail person)
  return $
    Contributor
      { contributorGithub = "",
        contributorCommits = 1,
        ..
      }

newtype InvalidEmail = InvalidEmail Text deriving (Show)

instance Exception InvalidEmail

newtype LoginCache = LoginCache
  { fromEmail :: HashMap Text Text
  }
  deriving (Semigroup, Monoid, Show)

instance ToJSON LoginCache where
  toJSON LoginCache {..} =
    object
      [ "by-email" .= fromEmail
      ]

instance FromJSON LoginCache where
  parseJSON = withObject "LoginCache" $ \v ->
    LoginCache
      <$> v .: "by-email"

lookupByEmail :: Text -> LoginCache -> Maybe Text
lookupByEmail email LoginCache {..} = HashMap.lookup email fromEmail

insertByEmail :: Contributor -> LoginCache -> LoginCache
insertByEmail Contributor {..} loginCache@LoginCache {..}
  | Text.null contributorEmail = loginCache
  | otherwise = LoginCache {fromEmail = HashMap.insert contributorEmail contributorGithub fromEmail, ..}

addContributorGithub :: MonadIO m => GH.Auth -> MVar LoginCache -> ConduitT Contributor Contributor m ()
addContributorGithub auth loginCacheVar = do
  awaitForever $ \contributor -> do
    contributor <-
      lift . runConduit $
        sequence_ -- Try each approach in order
          [ viaLoginCache loginCacheVar contributor,
            viaContributorEmail contributor,
            viaGitHub loginCacheVar contributor
          ]
          .| headDef contributor
    yield contributor
  where
    viaLoginCache :: MonadIO m => MVar LoginCache -> Contributor -> ConduitT () Contributor m ()
    viaLoginCache loginCacheVar contributor@Contributor {..} = do
      maybeContributorGithub <-
        liftIO $
          withMVar loginCacheVar $
            return . lookupByEmail contributorEmail
      maybe mempty (\contributorGithub -> yield $ contributor {contributorGithub = contributorGithub}) maybeContributorGithub

    viaContributorEmail :: MonadIO m => Contributor -> ConduitT () Contributor m ()
    viaContributorEmail contributor@Contributor {..}
      | "@users.noreply.github.com" `Text.isSuffixOf` contributorEmail = do
        let contributorGithub = Text.takeWhile (/= '@') contributorEmail
        yield $ contributor {contributorGithub = contributorGithub}
      | otherwise = mempty

    viaGitHub :: MonadIO m => MVar LoginCache -> Contributor -> ConduitT () Contributor m ()
    viaGitHub loginCacheVar contributor@Contributor {..} = do
      let searchByEmail = GH.searchUsersR contributorEmail (GH.FetchAtLeast 1)
      searchResultOrError <- lift . liftIO $ GH.executeRequest auth searchByEmail
      GH.SearchResult {..} <- lift . liftIO $ either (fail . displayException) return searchResultOrError
      when (searchResultTotalCount >= 1) $ do
        let contributorGithub = GH.untagName . GH.simpleUserLogin . Vector.unsafeHead $ searchResultResults
        let contributor' = contributor {contributorGithub = contributorGithub}
        lift . liftIO $ modifyMVar_ loginCacheVar (return . insertByEmail contributor')
        yield contributor'

commitToContributor :: MonadIO m => ConduitT (Commit SHA1) Contributor m ()
commitToContributor = awaitForever $ \commit -> do
  contributor <- lift . liftIO $
    personToContributor (commitAuthor commit)
  yield contributor

main :: IO ()
main = do
  -- Get GitHub authentication token
  auth <- getAuth

  -- Get contributors already in contributorDir
  knownAuthors <- readContributors authorDir
  knownContributors <- readContributors contributorDir
  let loginCache = foldr insertByEmail mempty (knownAuthors <> knownContributors)

  loginCacheVar <- newMVar loginCache
  refCacheVar <- newMVar Set.empty
  resultOrError <- withCurrentRepo $ do
    runConduit $
      streamGitHead
        .| streamGitCommitsFrom refCacheVar
        .| Conduit.take 5
        .| commitToContributor
        .| addContributorGithub auth loginCacheVar
        .| Conduit.print
  withMVar loginCacheVar print
  return ()
