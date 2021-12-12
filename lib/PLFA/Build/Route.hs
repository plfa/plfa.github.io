{-# LANGUAGE TupleSections #-}

module PLFA.Build.Route
  ( RoutingTable
  , buildPermalinkRoutingTable
  , asRoutingTable
  , routeUrl
  , routeFile
  , wantAllTargets
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


type RoutingTable = Map FilePath Url

buildPermalinkRoutingTable :: [FilePath] -> IO RoutingTable
buildPermalinkRoutingTable sources = do
  permalinkRoutes <-
    forM sources $ \src -> do
      maybeOut <- permalinkRoute src
      return $ fmap (src,) maybeOut
  return $ M.fromList (catMaybes permalinkRoutes)

permalinkRoute :: FilePath -> IO (Maybe Url)
permalinkRoute src = do
  metadata <- readYamlFrontmatter src
  forM (metadata ^. "permalink") $ \permalink -> do
    return $ addIndexHtml permalink

asRoutingTable :: (FilePath -> FilePath) -> [FilePath] -> RoutingTable
asRoutingTable f sources = M.fromList [ (src, T.pack $ f src) | src <- sources ]

routeUrl :: RoutingTable -> FilePath -> Url
routeUrl table src = case M.lookup src table of
  Nothing  -> error $ "Could not find route for " <> src
  Just out -> out

routeFile :: FilePath -> RoutingTable -> FilePath -> FilePath
routeFile targetDir table src =
  urlToFile targetDir (routeUrl table src)

wantAllTargets :: FilePath -> RoutingTable -> Rules ()
wantAllTargets targetDir table =
  want [ urlToFile targetDir url | url <- M.elems table ]

urlToFile :: FilePath -> Url -> FilePath
urlToFile targetDir url =
  targetDir </> (T.unpack $ T.dropWhile (=='/') $ url)
