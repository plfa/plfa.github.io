{-# LANGUAGE OverloadedStrings #-}

module PLFA.Build.Prelude.Url
  ( Url
  , relativizeUrl
  , withUrls
  , withUrlsPandoc
  , withUrlsBlockPandoc
  , withUrlsInlinePandoc
  ) where

import Data.Function ((&))
import Data.Text (Text)
import Data.Text qualified as T
import Text.HTML.TagSoup qualified as TS
import Text.Pandoc (Block (..), Format (..), Inline (..), Pandoc)
import Text.Pandoc.Walk (Walkable (..))
import PLFA.Build.Prelude.FilePath

type Url = Text


-- | Make a Url relative to the site's root directory.
--
--   Adapted from hakyll's 'Hakyll.Web.Html.RelativizeUrls.relativizeUrls'
relativizeUrl :: Url -> Url
relativizeUrl url
  | "/" `T.isPrefixOf` url && not ("//" `T.isPrefixOf` url) =
    let (path, _anchor) = T.breakOn "#" url in toRoot path <> url
  | otherwise = url
  where
    -- | Creates the relative URL path to the site root for a given absolute URL path.
    toRoot :: Url -> Url
    toRoot = T.pack .
             joinPath .
             map (const "..") .
             filter (`notElem` [".", "/", "./"]) .
             splitDirectories .
             takeDirectory .
             T.unpack



-- | Apply a function to each Url in a raw HTML document.
--
--   Adapted from hakyll's 'Hakyll.Web.Html.withUrls'
withUrls :: (Url -> Url) -> Url -> Url
withUrls f = TS.renderTags . map tag . TS.parseTags
  where
    tag (TS.TagOpen s a) = TS.TagOpen s $ map attr a
    tag x                = x
    attr (k, v)          = (k, if k `elem` refs then f v else v)
    refs                 = ["src", "href"]

-- | Apply a function to each Url in a Pandoc document.
withUrlsPandoc :: (Url -> Url) -> Pandoc -> Pandoc
withUrlsPandoc f doc
  = doc
  & walk (withUrlsInlinePandoc f)
  & walk (withUrlsBlockPandoc f)

-- | Apply a function to each Url in a Pandoc 'Block' element.
withUrlsBlockPandoc :: (Url -> Url) -> Block -> Block
withUrlsBlockPandoc f (RawBlock fmt@(Format "html") raw) =
  RawBlock fmt (withUrls f raw)
withUrlsBlockPandoc f (RawBlock fmt@(Format _) raw) =
  RawBlock fmt (withUrls f raw)
withUrlsBlockPandoc _f block = block

-- | Apply a function to each Url in a Pandoc 'Inline' element.
withUrlsInlinePandoc :: (Url -> Url) -> Inline -> Inline
withUrlsInlinePandoc f (Link attr inlines (url, title)) =
  Link attr inlines (f url, title)
withUrlsInlinePandoc f (RawInline fmt@(Format "html") raw) =
  RawInline fmt (withUrls f raw)
withUrlsInlinePandoc f (RawInline fmt@(Format _) raw) =
  RawInline fmt (withUrls f raw)
withUrlsInlinePandoc _f inline = inline
