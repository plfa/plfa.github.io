--------------------------------------------------------------------------------
-- Contributors
--------------------------------------------------------------------------------

module Buildfile.Contributor where

import Control.Applicative (Alternative ((<|>)))
import Data.Aeson.Types
import Data.Maybe (fromJust, fromMaybe)
import Data.Text (Text)
import Text.Printf (printf)

data Contributor = Contributor
  { contributorName :: Text,
    contributorGithub :: Text,
    contributorEmail :: Text,
    contributorCommits :: Int
  }
  deriving (Show)

instance ToJSON Contributor where
  toJSON Contributor {..} =
    object
      [ "name" .= contributorName,
        "github" .= contributorGithub,
        "email" .= contributorEmail,
        "commits" .= contributorCommits
      ]

instance FromJSON Contributor where
  parseJSON = withObject "Contributor" $ \v ->
    Contributor
      <$> (fromMaybe "" <$> v .:? "name")
      <*> (fromMaybe "" <$> v .:? "github")
      <*> (fromMaybe "" <$> v .:? "email")
      <*> (fromMaybe 0 <$> (v .:? "count" <|> v .:? "commits"))
