module PLFA.Build.Route
  ( RoutingTable
  , buildPermalinkRoutingTable
  , asRoutingTable
  , route
  ) where

import Control.Monad (forM)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (catMaybes)
import Data.Text qualified as T
import PLFA.Build.Metadata
import PLFA.Build.Prelude

addIndexHtml :: Url -> Url
addIndexHtml url
  | "/" `T.isSuffixOf` url = url <> "index.html"
  | otherwise              = url


type RoutingTable = Map FilePath FilePath

buildPermalinkRoutingTable :: FilePath -> [FilePath] -> IO RoutingTable
buildPermalinkRoutingTable targetDir sources = do
  permalinkRoutes <-
    forM sources $ \src -> do
      maybeOut <- permalinkRoute targetDir src
      return $ fmap (\out -> (src, normalise out)) maybeOut
  return $ M.fromList (catMaybes permalinkRoutes)

permalinkRoute :: FilePath -> FilePath -> IO (Maybe FilePath)
permalinkRoute targetDir src = do
  metadata <- readYamlFrontmatter src
  forM (metadata ^. "permalink") $ \permalink -> do
    let permalink' = T.unpack $ T.dropWhile (=='/') $ addIndexHtml $ permalink
    return $ targetDir </> permalink'

asRoutingTable :: (FilePath -> FilePath) -> [FilePath] -> RoutingTable
asRoutingTable f sources = M.fromList [ (src, f src) | src <- sources ]

route :: RoutingTable -> FilePath -> FilePath
route table src = case M.lookup src table of
  Nothing  -> error $ "Could not find route for " <> src
  Just out -> out
