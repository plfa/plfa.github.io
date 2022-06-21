module Buildfile.Script where

import Data.Aeson.Types (KeyValue ((.=)), ToJSON (..), object)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Lazy qualified as LazyText
import Shoggoth.Configuration (Mode (Development), getMode)
import Shoggoth.Prelude (Action, Url, takeBaseName)
import Shoggoth.Routing (RoutingTable, routeUrl)

data Script
  = ScriptFile
      { scriptId :: Text,
        scriptUrl :: Url,
        scriptIntegrity :: Maybe LazyText.Text
      }
  | ScriptBody Text

inline :: Text -> Script
inline = ScriptBody

fromFilePath ::
  ( ?getDigest :: FilePath -> Action (Maybe LazyText.Text),
    ?routingTable :: RoutingTable
  ) =>
  FilePath ->
  Action Script
fromFilePath out = do
  let id = Text.pack (takeBaseName out)
  url <- routeUrl out
  (url, integrity) <- (,) <$> routeUrl out <*> ?getDigest out
  return $
    ScriptFile
      { scriptId = "script-" <> id,
        scriptUrl = url,
        scriptIntegrity = integrity
      }

instance ToJSON Script where
  toJSON ScriptFile {..} =
    object
      [ "id" .= scriptId,
        "url" .= scriptUrl,
        "integrity" .= scriptIntegrity
      ]
  toJSON (ScriptBody scriptBody) =
    object
      [ "body" .= scriptBody
      ]
