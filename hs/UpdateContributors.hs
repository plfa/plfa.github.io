{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Monad (forM, forM_)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import           Data.Frontmatter (parseYamlFrontmatterEither)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromMaybe, mapMaybe)
import           Data.String (IsString(..))
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector as V
import           Data.Yaml (FromJSON(..), ToJSON(..), (.:), (.:?), (.=))
import qualified Data.Yaml as Y
import qualified GitHub as GH
import           System.Directory (createDirectoryIfMissing)
import           System.Exit (exitFailure)
import           System.FilePath ((</>), (<.>))
import           System.FilePath.Glob (namesMatching)
import           System.Environment (lookupEnv)
import           Text.Printf (printf)


-- * Configuration

authorDir, contributorDir :: FilePath
authorDir      = "authors"
contributorDir = "contributors"

githubOwner, githubRepo :: Text
githubOwner  = "plfa"
githubRepo   = "plfa.github.io"

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
      authorGithubs = map authorGithub authors

  let isAuthorOrError :: Contributor -> Bool
      isAuthorOrError Contributor{..} =
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
    let contributorFile = contributorDir </> T.unpack github <.> "metadata"
    let contributorBS = "---\n" <> Y.encode contributor <> "---\n"
    BC.writeFile contributorFile contributorBS


-- * Authors

data Author = Author
  { authorName          :: Text
  , authorEmail         :: Text
  , authorCorresponding :: Bool
  , authorGithub        :: Text
  , authorTwitter       :: Maybe Text
  }
  deriving (Show)

readAuthors :: FilePath -> IO [Author]
readAuthors dir = do
  authorFiles <- namesMatching (dir </> "*.metadata")
  forM authorFiles $ \authorFile -> do
    authorOrError <- parseYamlFrontmatterEither <$> B.readFile authorFile
    case authorOrError of
      Left  errmsg -> do
        printf "Parse error in '%s': %s\n" authorFile errmsg
        exitFailure
      Right author ->
        return author

instance FromJSON Author where
  parseJSON = Y.withObject "Author" $ \v -> Author
    <$> v .:  "name"
    <*> v .:  "email"
    <*> v .:  "corresponding"
    <*> v .:  "github"
    <*> v .:? "twitter"

instance ToJSON Author where
  toJSON Author{..} =
    Y.object [ "name"          .= authorName
             , "email"         .= authorEmail
             , "corresponding" .= authorCorresponding
             , "github"        .= authorGithub
             , "twitter"       .= authorTwitter
             ]


-- * Contributors

data Contributor = Contributor
  { contributorName   :: Text
  , contributorGithub :: Text
  , contributorCount  :: Int
  }

instance Semigroup Contributor where
  Contributor _name1 github1 count1 <> Contributor name2 github2 count2
    = if github1 == github2
      then Contributor name2 github2 (count1 `max` count2)
      else error $ printf "Cannot merge unrelated contributors '%s' and '%s'" github1 github2

instance FromJSON Contributor where
  parseJSON = Y.withObject "Contributor" $ \v -> Contributor
    <$> v .: "name"
    <*> v .: "github"
    <*> v .: "count"

instance ToJSON Contributor where
  toJSON Contributor{..} =
    Y.object [ "name"   .= contributorName
             , "github" .= contributorGithub
             , "count"  .= contributorCount
             ]

readContributors :: FilePath -> IO [Contributor]
readContributors dir = do
  contributorFiles <- namesMatching (dir </> "*.metadata")
  forM contributorFiles $ \contributorFile -> do
    contributorOrError <- parseYamlFrontmatterEither <$> B.readFile contributorFile
    case contributorOrError of
      Left errmsg -> do
        printf "Parse error in '%s': %s\n" contributorFile errmsg
        exitFailure
      Right contributor ->
        return contributor


-- * Github interaction

-- |Get user information for every user who authored a commit.
getContributors :: GH.Auth -> GH.Name GH.Owner -> GH.Name GH.Repo -> IO [Contributor]
getContributors auth owner repo = do
  commits <- getCommits auth owner repo
  forM (frequency (mapMaybe GH.commitAuthor commits)) $ \(simpleUser, count) -> do
    user <- getUserInfo auth simpleUser
    return $ toContributor user count

-- |Convert a |GH.User| value to a |Contributor| value.
toContributor :: GH.User -> Int -> Contributor
toContributor commitAuthor count = Contributor name github count
  where
    name = fromMaybe github (GH.userName commitAuthor)
    github = GH.untagName (GH.userLogin commitAuthor)

-- |Get an authentication token from the environment.
getAuth :: IO GH.Auth
getAuth = do
    mtoken <- lookupEnv "GITHUB_TOKEN"
    case mtoken of
      Nothing -> error "Please set GITHUB_TOKEN"
      Just token -> return (GH.OAuth . fromString $ token)

-- |Get user information from a user login.
getUserInfo :: GH.Auth -> GH.SimpleUser -> IO GH.User
getUserInfo auth simpleUser =
  fromRight =<< GH.github auth GH.userInfoForR (GH.simpleUserLogin simpleUser)

-- |Get commit history for a repository.
getCommits :: GH.Auth -> GH.Name GH.Owner -> GH.Name GH.Repo -> IO [GH.Commit]
getCommits auth owner repo =
  V.toList <$> (fromRight =<< GH.github auth GH.commitsForR owner repo GH.FetchAll)


-- * Utils

frequency :: (Ord a) => [a] -> [(a, Int)]
frequency xs = M.toList (M.fromListWith (+) [(x, 1) | x <- xs])

fromRight :: Show e => Either e a -> IO a
fromRight = either (fail . show) return
