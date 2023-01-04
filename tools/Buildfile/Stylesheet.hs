module Buildfile.Stylesheet where

import Data.Aeson.Types (KeyValue ((.=)), ToJSON (toJSON), object)
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Lazy qualified as LazyText
import Shoggoth.Configuration (Mode (Development), getMode)
import Shoggoth.Prelude (Action, Url, getEnvWithDefault, takeBaseName)
import Shoggoth.Routing (RoutingTable, routeUrl)

data Stylesheet = Stylesheet
  { stylesheetTitle :: Text,
    stylesheetRelation :: Text,
    stylesheetId :: Text,
    stylesheetEnabled :: Bool,
    stylesheetUrl :: Url,
    stylesheetIntegrity :: Maybe LazyText.Text
  }

alternate :: Stylesheet -> Stylesheet
alternate ss = ss {stylesheetRelation = "stylesheet", stylesheetEnabled = False}

fromFilePath ::
  ( ?getDigest :: FilePath -> Action (Maybe LazyText.Text),
    ?routingTable :: RoutingTable
  ) =>
  FilePath ->
  Action Stylesheet
fromFilePath out = do
  let id = Text.pack (takeBaseName out)
  (url, integrity) <- (,) <$> routeUrl out <*> ?getDigest out
  return $
    Stylesheet
      { stylesheetTitle = Text.toTitle id,
        stylesheetRelation = "stylesheet",
        stylesheetId = "stylesheet-" <> id,
        stylesheetEnabled = True,
        stylesheetUrl = url,
        stylesheetIntegrity = integrity
      }

instance ToJSON Stylesheet where
  toJSON Stylesheet {..} =
    object
      [ "title" .= stylesheetTitle,
        "rel" .= stylesheetRelation,
        "id" .= stylesheetId,
        "enabled" .= stylesheetEnabled,
        "url" .= stylesheetUrl,
        "integrity" .= stylesheetIntegrity
      ]
