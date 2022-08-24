module Main where

import Buildfile.Contributor (Contributor (..))
import Conduit (MonadIO (liftIO), MonadTrans (lift))
import Control.Monad (when, (<=<))
import Control.Monad.IO.Class (MonadIO)
import Data.Conduit
  ( ConduitT,
    awaitForever,
    runConduit,
    yield,
    (.|),
  )
import Data.Conduit.Combinators qualified as Conduit
import Data.Foldable (for_)
import Data.Git.Monad (GitM, GitMonad (..), Resolvable (resolve), getCommit, headGet, withCurrentRepo, headResolv)
import Data.Git.Ref (HashAlgorithm, SHA1, Ref)
import Data.Git.Types (Commit (..), Person (..))
import Data.String (IsString (..))
import Data.Text.Encoding (decodeUtf8)
import GitHub qualified as GH
import System.Environment (lookupEnv)
import Data.Conduit.List (sourceList)

instance MonadIO GitM where
  liftIO = liftGit

-- | Get an authentication token from the environment.
getAuth :: IO GH.Auth
getAuth = do
  mtoken <- lookupEnv "GITHUB_TOKEN"
  case mtoken of
    Nothing -> error "Please set GITHUB_TOKEN"
    Just token -> return (GH.OAuth . fromString $ token)

commitsFrom :: (GitMonad m, Resolvable ref) => ConduitT ref (Commit SHA1) m ()
commitsFrom = awaitForever $ \ref -> do
  maybeCommit <- lift (getCommit ref)
  case maybeCommit of
    Nothing -> return ()
    Just commit -> do
      yield commit
      sourceList (commitParents commit) .| commitsFrom

head :: GitMonad m => ConduitT () (Ref SHA1) m ()
head = lift headResolv >>= maybe (return ()) yield

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

commitToContributor :: Monad m => ConduitT (Commit SHA1) Contributor m ()
commitToContributor = awaitForever $ \commit -> do
  yield $ personToContributor (commitAuthor commit)

main :: IO ()
main = do
  either putStrLn return <=< withCurrentRepo $ do
    runConduit (commitConduit .| commitToContributor .| Conduit.print)
    return ()
