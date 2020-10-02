--------------------------------------------------------------------------------
-- Create a route based on the 'permalink' metadata field
--------------------------------------------------------------------------------

module Hakyll.Web.Routes.Permalink (permalinkRoute) where

import           Hakyll
import           Data.List (stripPrefix)
import           Data.Maybe (fromMaybe)
import           System.FilePath ((</>))

permalinkRoute :: Routes -> Routes
permalinkRoute def = metadataRoute $ \metadata ->
  maybe def (constRoute . conv) (lookupString "permalink" metadata)
  where
    -- By a quirk of history, permalinks for PLFA are written as, e.g., "/DeBruijn/".
    -- We convert these to links by stripping the "/" prefix, and adding "index.html".
    conv :: FilePath -> FilePath
    conv permalink = fromMaybe permalink (stripPrefix "/" permalink) </> "index.html"
