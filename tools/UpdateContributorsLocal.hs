module Main where

import Buildfile.Configuration
import Buildfile.Contributor (Contributor (..))
import Conduit (MonadIO (liftIO), MonadTrans (lift))
import Control.Applicative ((<|>))
import Control.Concurrent.MVar (MVar, modifyMVar_, newMVar, withMVar)
import Control.Exception (Exception (..), throwIO)
import Control.Monad (join, when, (<=<))
import Control.Monad.IO.Class (MonadIO)
import Data.Conduit
  ( ConduitT,
    awaitForever,
    runConduit,
    sequenceConduits,
    yield,
    (.|),
  )
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

readContributors :: FilePath -> IO [Contributor]
readContributors dir = do
  contributorFiles <- getDirectoryFilesIO contributorDir ["*.yml"]
  contributors <- traverse (\src -> readYamlIO $ contributorDir </> src) contributorFiles
  let sortedContributors = sortBy (compare `on` contributorCount) contributors
  return (sortedContributors :: [Contributor])

-- | Get an authentication token from the environment.
getAuth :: IO GH.Auth
getAuth = do
  mtoken <- lookupEnv "GITHUB_TOKEN"
  case mtoken of
    Nothing -> error "Please set GITHUB_TOKEN"
    Just token -> return (GH.OAuth . fromString $ token)

streamCommitsFrom :: (GitMonad m, Resolvable ref) => ConduitT ref (Commit SHA1) m ()
streamCommitsFrom = awaitForever $ \ref -> do
  maybeCommit <- lift (getCommit ref)
  case maybeCommit of
    Nothing -> return ()
    Just commit -> do
      yield commit
      sourceList (commitParents commit) .| streamCommitsFrom

streamHead :: GitMonad m => ConduitT () (Ref SHA1) m ()
streamHead = lift headResolv >>= maybe (return ()) yield

-- searchUsersR :: Text -> FetchCount -> Request k (SearchResult SimpleUser)
-- executeRequest :: (AuthMethod am, ParseResponse mt a) => am -> GenRequest mt rw a -> IO (Either Error a)

personToContributor :: Person -> Contributor
personToContributor person =
  Contributor
    { contributorName = decodeUtf8 (personName person),
      contributorGithub = "",
      contributorEmail = decodeUtf8 (personEmail person),
      contributorCount = 1
    }

newtype InvalidEmail = InvalidEmail Text deriving (Show)

instance Exception InvalidEmail

type LoginCache = HashMap Text Text

addContributorGithub :: MonadIO m => GH.Auth -> MVar LoginCache -> ConduitT Contributor Contributor m ()
addContributorGithub auth loginCacheVar = do
  awaitForever $ \contributor -> do
    contributor <-
      runConduit $
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
      maybeContributorGithub <- liftIO $
        withMVar loginCacheVar $ \loginCache -> do
          let byContributorName = HashMap.lookup contributorName loginCache
          let byContributorEmail = HashMap.lookup contributorEmail loginCache
          return $ byContributorName <|> byContributorEmail
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
        yield $ contributor {contributorGithub = contributorGithub}

commitToContributor :: Monad m => ConduitT (Commit SHA1) Contributor m ()
commitToContributor = awaitForever $ \commit -> do
  yield $ personToContributor (commitAuthor commit)

main :: IO ()
main = do
  auth <- getAuth
  loginCacheVar <- newMVar HashMap.empty
  resultOrError <- withCurrentRepo $ do
    runConduit $
      streamHead
        .| streamCommitsFrom
        .| Conduit.take 5
        .| commitToContributor
        .| addContributorGithub auth loginCacheVar
        .| Conduit.print
  withMVar loginCacheVar print
  return ()
