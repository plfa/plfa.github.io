module PLFA.Build.Route
  ( permalinkRoute
  , getPermalinkRoutingTable
  ) where

import Control.Monad (forM)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T
import PLFA.Build.Metadata
import PLFA.Build.Prelude

permalinkRoute :: FilePath -> FilePath -> IO FilePath
permalinkRoute targetDir src = do
  metadata <- readYamlFrontmatter src
  permalink <- metadata ^. "permalink"
  let safePermalink = T.dropAround (=='/') permalink
  return $
    targetDir </> T.unpack safePermalink </> "index.html"

getPermalinkRoutingTable :: FilePath -> [FilePath] -> IO (Map FilePath FilePath)
getPermalinkRoutingTable targetDir sources = do
  permalinkRoutes <-
    forM sources $ \src -> do
      out <- permalinkRoute targetDir src
      return (src, normalise out)
  return $
    M.fromList permalinkRoutes
