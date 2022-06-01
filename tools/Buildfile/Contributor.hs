--------------------------------------------------------------------------------
-- Contributors
--------------------------------------------------------------------------------

module Buildfile.Contributor where

import Data.Aeson.Types
import Data.Text (Text)

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

