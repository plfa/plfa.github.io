--------------------------------------------------------------------------------
-- Authors
--------------------------------------------------------------------------------

module Buildfile.Author where

import Data.Aeson.Types
import Data.Text (Text)

data Author = Author
  { authorName          :: Text
  , authorEmail         :: Text
  , authorGithub        :: Maybe Text
  , authorTwitter       :: Maybe Text
  , authorCorresponding :: Bool
  }
  deriving (Show)

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
