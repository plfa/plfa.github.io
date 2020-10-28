{-# LANGUAGE OverloadedStrings #-}

module Hakyll.Web.Routes.Permalink
  ( convertPermalink
  , permalinkRoute
  , permalinkRouteWithDefault
  , stripIndexFile
  ) where

import           Data.List (stripPrefix)
import           Data.List.Extra (stripSuffix)
import           Data.Maybe (fromMaybe)
import           Hakyll
import           System.FilePath ((</>))

-- By a quirk of history, permalinks for PLFA are written as, e.g., "/DeBruijn/".
-- We convert these to links by stripping the "/" prefix, and adding "index.html".
convertPermalink :: FilePath -> FilePath
convertPermalink link = fromMaybe link (stripPrefix "/" link) </> "index.html"

permalinkRoute :: Routes
permalinkRoute = permalinkRouteWithDefault (error "Missing field 'permalink'.")

permalinkRouteWithDefault :: Routes -> Routes
permalinkRouteWithDefault def = metadataRoute $ \metadata ->
  maybe def (constRoute . convertPermalink) (lookupString "permalink" metadata)

-- Removes "index.html" from URLs.
stripIndexFile :: String -> String
stripIndexFile = withUrls dir
  where
    dir link = fromMaybe link (stripSuffix "index.html" link)
