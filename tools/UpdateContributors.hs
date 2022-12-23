{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
module Main where

import Buildfile.Author (Author (..))
import Buildfile.Contributor (Contributor (..))
import Buildfile.Configuration
import Control.Monad (forM, forM_)
import Data.ByteString qualified as B
import Data.ByteString.Char8 qualified as BC
import Data.Frontmatter (parseYamlFrontmatterEither)
import Data.Function (on)
import Data.List (sortBy)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromMaybe, mapMaybe)
import Data.String (IsString (..))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Data.Yaml (FromJSON (..), ToJSON (..), (.:), (.:?), (.=))
import Data.Yaml qualified as Y
import GitHub qualified as GH
import Shoggoth.Metadata (readYamlIO)
import Shoggoth.Prelude (getDirectoryFilesIO)
import System.Directory (createDirectoryIfMissing)
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.FilePath ((<.>), (</>))
import System.FilePath.Glob (namesMatching)
import Text.Printf (printf)

-- * Configuration

githubErrors :: [Text]
githubErrors = ["invalid-email-address"]

-- * Main

main :: IO ()
main = do
  -- Get the GitHub authentication token from `GITHUB_TOKEN`
  auth <- getAuth

  -- Read the current set of authors from `authorDir`
  authors <- readAuthors authorDir

  -- Read the current set of contributors from `contributorDir`
  localContributors <- readContributors contributorDir
  remoteContributorAndAuthors <-
    getContributors auth (GH.mkOwnerName githubOwner) (GH.mkRepoName githubRepo)

  -- Filter the contributor list by the authors
  let authorGithubs :: [Text]
      authorGithubs = mapMaybe authorGithub authors

  let isAuthorOrError :: Contributor -> Bool
      isAuthorOrError Contributor {..} =
        contributorGithub `elem` authorGithubs || contributorGithub `elem` githubErrors

  let remoteContributors :: [Contributor]
      remoteContributors = filter (not . isAuthorOrError) remoteContributorAndAuthors

  -- Turn contributor lists into maps and merge them
  let localContributorMap :: Map Text Contributor
      localContributorMap = M.fromList [(contributorGithub c, c) | c <- localContributors]

  let remoteContributorMap :: Map Text Contributor
      remoteContributorMap = M.fromList [(contributorGithub c, c) | c <- remoteContributors]

  let contributorMap :: Map Text Contributor
      contributorMap = M.unionWith (<>) localContributorMap remoteContributorMap

  -- Write contributor files
  createDirectoryIfMissing True contributorDir
  forM_ (M.toList contributorMap) $ \(github, contributor) -> do
    let contributorFile = contributorDir </> T.unpack github <.> "yml"
    let contributorBS = Y.encode contributor
    BC.writeFile contributorFile contributorBS

-- * Authors

readAuthors :: FilePath -> IO [Author]
readAuthors dir = do
  authorFiles <- getDirectoryFilesIO authorDir ["*.yml"]
  authors <- traverse (\src -> readYamlIO $ authorDir </> src) authorFiles
  return (authors :: [Author])

-- * Contributors

readContributors :: FilePath -> IO [Contributor]
readContributors dir = do
  contributorFiles <- getDirectoryFilesIO contributorDir ["*.yml"]
  contributors <- traverse (\src -> readYamlIO $ contributorDir </> src) contributorFiles
  let sortedContributors = sortBy (compare `on` contributorCount) contributors
  return (sortedContributors :: [Contributor])

-- * Github interaction

-- | Get user information for every user who authored a commit.
getContributors :: GH.Auth -> GH.Name GH.Owner -> GH.Name GH.Repo -> IO [Contributor]
getContributors auth owner repo = do
  commits <- getCommits auth owner repo
  -- If there author has an invalid email address, GitHub returns a SimpleUser
  -- with the name "invalid-email-address", rather than throwing an error
  let commitAuthors = flip mapMaybe commits $ \commit -> do
        simpleUser <- GH.commitAuthor commit
        let simpleUserName = GH.untagName $ GH.simpleUserLogin simpleUser
        if simpleUserName == "invalid-email-address"
          then fail "Invalid email address"
          else return simpleUser
  forM (frequency commitAuthors) $ \(simpleUser, count) -> do
    printf "Get user info for %s\n" (T.unpack $ GH.untagName $ GH.simpleUserLogin simpleUser)
    user <- getUserInfo auth simpleUser
    return $ toContributor user count

-- | Convert a |GH.User| value to a |Contributor| value.
toContributor :: GH.User -> Int -> Contributor
toContributor commitAuthor count = Contributor name github count
  where
    name = fromMaybe github (GH.userName commitAuthor)
    github = GH.untagName (GH.userLogin commitAuthor)

-- | Get an authentication token from the environment.
getAuth :: IO GH.Auth
getAuth = do
  mtoken <- lookupEnv "GITHUB_TOKEN"
  case mtoken of
    Nothing -> error "Please set GITHUB_TOKEN"
    Just token -> return (GH.OAuth . fromString $ token)

-- | Get user information from a user login.
getUserInfo :: GH.Auth -> GH.SimpleUser -> IO GH.User
getUserInfo auth simpleUser =
  fromRight =<< GH.github auth GH.userInfoForR (GH.simpleUserLogin simpleUser)

-- | Get commit history for a repository.
getCommits :: GH.Auth -> GH.Name GH.Owner -> GH.Name GH.Repo -> IO [GH.Commit]
getCommits auth owner repo =
  V.toList <$> (fromRight =<< GH.github auth GH.commitsForR owner repo GH.FetchAll)

-- * Utils

frequency :: (Ord a) => [a] -> [(a, Int)]
frequency xs = M.toList (M.fromListWith (+) [(x, 1) | x <- xs])

fromRight :: Show e => Either e a -> IO a
fromRight = either (fail . show) return
