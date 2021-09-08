module PLFA.Build.Route
  ( permalinkRoute
  , getPermalinkRoutingTable
  ) where

import Control.Monad (forM)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (catMaybes)
import Data.Text qualified as T
import PLFA.Build.Metadata
import PLFA.Build.Prelude

permalinkRoute :: FilePath -> FilePath -> IO (Maybe FilePath)
permalinkRoute targetDir src = do
  metadata <- readYamlFrontmatter src
  forM (metadata ^. "permalink") $ \permalink -> do
    let safePermalink = T.dropAround (=='/') permalink
    return $ targetDir </> T.unpack safePermalink </> "index.html"

getPermalinkRoutingTable :: FilePath -> [FilePath] -> IO (Map FilePath FilePath)
getPermalinkRoutingTable targetDir sources = do
  permalinkRoutes <-
    forM sources $ \src -> do
      maybeOut <- permalinkRoute targetDir src
      return $ fmap (\out -> (src, normalise out)) maybeOut
  return $ M.fromList (catMaybes permalinkRoutes)
