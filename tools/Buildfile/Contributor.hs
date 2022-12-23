--------------------------------------------------------------------------------
-- Contributors
--------------------------------------------------------------------------------

module Buildfile.Contributor where

import Data.Aeson.Types
import Data.Text (Text)
import Text.Printf (printf)

data Contributor = Contributor
  { contributorName   :: Text
  , contributorGithub :: Text
  , contributorCount  :: Int
  }
  deriving (Show)

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

instance Semigroup Contributor where
  Contributor _name1 github1 count1 <> Contributor name2 github2 count2
    = if github1 == github2
      then Contributor name2 github2 (count1 `max` count2)
      else error $ printf "Cannot merge unrelated contributors '%s' and '%s'" github1 github2
