module Main where

import Control.Monad (forM)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.IO.Class (MonadIO)
import Data.Default.Class (Default (def))
import Data.Either (isRight)
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.List (isPrefixOf)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Shoggoth.Agda qualified as Agda
import Shoggoth.PostInfo
import Shoggoth.Prelude
import Shoggoth.Routing
import Shoggoth.CSS.Minify qualified as CSS
import Shoggoth.CSS.Sass qualified as CSS
import Shoggoth.CSS.Sass (SassOptions (..))
import Shoggoth.Template
import Shoggoth.Template.Pandoc qualified as Pandoc
import Shoggoth.Template.Pandoc.Builder qualified as Builder
import Shoggoth.Template.Pandoc.Citeproc qualified as Citeproc
import Shoggoth.Template.TagSoup qualified as TagSoup

outDir, tmpDir :: FilePath
outDir = "_site"
tmpDir = "_cache"


main :: IO ()
main = do
  shakeArgs shakeOptions {shakeFiles = tmpDir, shakeProgress = progressSimple} $ do

    --------------------------------------------------------------------------------
    -- Agda libraries

    standardLibrary <- Agda.getStandardLibrary "standard-library"
    let localLibraries = [plfaLibrary, tspl19Library]
    let otherLibraries = []
    let ?agdaLibraries = [standardLibrary] <> localLibraries <> otherLibraries

    --------------------------------------------------------------------------------
    -- Routing table

    let ?routingTable =
          mconcat
            [ -- Pure routes
              ["pages/404.md"] |-> outDir </> "404.html",
              -- Volatile routes
              [assetSrcDir <//> "*"]     %-> assetRouter,
              [styleSrcDir </> "*.scss"] %-> styleRouter
            ]

    --------------------------------------------------------------------------------
    -- Cached file, template, and metadata getters

    cachedGetSiteMetadata <- newCache getSiteMetadata
    let ?getSiteMetadata = cachedGetSiteMetadata
    cachedGetFileWithMetadata <- newCache getFileWithMetadata
    let ?getFileWithMetadata = cachedGetFileWithMetadata
    cachedGetTemplateFile <- newCache getTemplateFile
    let ?getTemplateFile = getTemplateFile
    let ?readerOpts = def {readerExtensions = markdownDialect}
    let ?writerOpts =
          def
            { writerHTMLMathMethod = KaTeX "",
              writerEmailObfuscation = JavascriptObfuscation,
              writerHighlightStyle = Just highlightStyle
            }

    --------------------------------------------------------------------------------
    -- Phony targets

    "build" ~> do
      need [styleOutDir </> "highlight.css"]
      need =<< outputs

    "clean" ~> do
      removeFilesAfter tmpDir ["//*"]

    "clobber" ~> do
      removeFilesAfter outDir ["//*"]
      removeFilesAfter tmpDir ["//*"]

    --------------------------------------------------------------------------------
    -- File targets

    alternatives $ do
      styleRules -- Style sheets
      assetRules -- Static assets

    -- 404.html
    outDir </> "404.html" %> \out -> do
      src <- routeSource out
      metadata <- ?getSiteMetadata ()
      readFile' src
        >>= markdownToPandoc
        <&> Pandoc.shiftHeadersBy 2
        >>= pandocToHtml5
        >>= applyTemplate "default.html" metadata
        <&> postprocessHtml5 outDir out
        >>= writeFile' out


--------------------------------------------------------------------------------
-- Agda

plfaSrcDir :: FilePath
plfaSrcDir = "src"

plfaLibrary :: Agda.Library
plfaLibrary =
  Agda.Library
    { libraryRoot = "",
      includePaths = ["src"],
      canonicalBaseUrl = "https://plfa.github.io/"
    }

tspl19Library :: Agda.Library
tspl19Library =
  Agda.Library
    { libraryRoot = "courses/tspl/2019",
      includePaths = [""],
      canonicalBaseUrl = "https://plfa.github.io/TSPL/2019/"
    }

--------------------------------------------------------------------------------
-- Posts

postSrcDir, postHtmlAgdaDir, postHtmlBodyDir, postOutDir :: FilePath
postSrcDir = "posts"
postHtmlAgdaDir = tmpDir </> "stage1" </> "posts" -- Render .lagda.md to .md
postHtmlBodyDir = tmpDir </> "stage2" </> "posts" -- Render .md to .html
postOutDir = outDir -- NOTE: cannot rely on 'postOutDir' to test if a FilePath is an output

postRouter :: (?agdaLibraries :: [Agda.Library]) => Source -> Either String Stages
postRouter src = do
  let postSrc = makeRelative postSrcDir src
  PostInfo {..} <- parsePostSource postSrc
  let htmlBody = postHtmlBodyDir </> postSrc
  let out = postOutDir </> year </> month </> day </> fileName </> "index.html"
  let stages = "html-body" :@: htmlBody :>: Output out
  if Agda.isAgdaFile src
    then do
      highlightAgda <- Agda.htmlOutputPath postHtmlAgdaDir ?agdaLibraries src
      return (highlightAgda :>: stages)
    else return stages

isPostSrc, isPostHtmlAgda, isPostHtmlBody, isPostOut :: FilePath -> Bool
isPostSrc src = postSrcDir `isPrefixOf` src
isPostHtmlAgda tmp = postHtmlAgdaDir `isPrefixOf` tmp
isPostHtmlBody tmp = postHtmlBodyDir `isPrefixOf` tmp
isPostOut out = isRight (parsePostOutput out)

-- postRules ::
--   ( ?routingTable :: RoutingTable,
--     ?getTemplateFile :: FilePath -> Action Template,
--     ?getPostWithMetadata :: FilePath -> Action (Metadata, Text),
--     ?agdaLibraries :: [Agda.Library],
--     ?getAgdaLinkFixer :: () -> Action (Url -> Url),
--     ?readerOpts :: Pandoc.ReaderOptions,
--     ?writerOpts :: Pandoc.WriterOptions
--   ) =>
--   Rules ()
-- postRules = do
--   -- Compile literate Agda to Markdown & HTML
--   isPostHtmlAgda ?> \next -> do
--     prev <- routePrev next
--     Agda.compileTo Agda.Html ?agdaLibraries postHtmlAgdaDir prev

--   -- Compile Markdown to HTML
--   isPostHtmlBody ?> \next -> do
--     (out, prev, src) <- (,,) <$> route next <*> routePrev next <*> routeSource next
--     agdaLinkFixer <- ?getAgdaLinkFixer ()
--     let maybeAgdaLinkFixer = if Agda.isAgdaFile src then Just (Pandoc.withUrls agdaLinkFixer) else Nothing
--     readFile' prev
--       >>= markdownToPandoc
--       >>= processCitations
--       <&> Pandoc.shiftHeadersBy 2
--       <&> fromMaybe id maybeAgdaLinkFixer
--       >>= pandocToHtml5 -- postprocessHtml5 in next rule
--       >>= writeFile' next

--   -- Apply templates
--   isPostOut ?> \out -> do
--     (prev, src) <- (,) <$> routePrev out <*> routeSource out
--     metadata <- fst <$> ?getPostWithMetadata src
--     readFile' prev
--       >>= applyTemplates ["post.html", "default.html"] metadata
--       <&> postprocessHtml5 outDir out
--       >>= writeFile' out

--------------------------------------------------------------------------------
-- Style Sheets

styleSrcDir, styleOutDir :: FilePath
styleSrcDir = "sass"
styleOutDir = outDir </> "assets" </> "css"

styleRouter :: FilePath -> Stages
styleRouter src =
  Output $
    styleOutDir </> makeRelative styleSrcDir src -<.> "css"

sassOptions :: SassOptions
sassOptions =
  def
    { sassIncludePaths = Just [styleSrcDir],
      sassImporters = Just [CSS.minCssImporter styleSrcDir 1]
    }

styleRules :: (?routingTable :: RoutingTable) => Rules ()
styleRules = alternatives $ do
  styleOutDir </> "style.css" %> \out -> do
    src <- routeSource out
    CSS.compileSassWith sassOptions src
      >>= CSS.minifyCSS
      >>= writeFile' out

  styleOutDir </> "highlight.css" %> \out -> do
    let css = Text.pack $ Pandoc.styleToCss highlightStyle
    writeFile' out =<< CSS.minifyCSS css

  styleOutDir </> "*.css" %> \out -> do
    src <- routeSource out
    readFile' src
      >>= CSS.minifyCSS
      >>= writeFile' out

--------------------------------------------------------------------------------
-- Assets

assetSrcDir, assetOutDir :: FilePath
assetSrcDir = "assets"
assetOutDir = outDir </> "assets"

assetRouter :: FilePath -> Stages
assetRouter src =
  Output $
    assetOutDir </> makeRelative assetSrcDir src

assetRules :: (?routingTable :: RoutingTable) => Rules ()
assetRules =
  assetOutDir <//> "*" %> \out -> do
    src <- routeSource out
    copyFile' src out

--------------------------------------------------------------------------------
-- Markdown to HTML compilation

highlightStyle :: Pandoc.HighlightStyle
highlightStyle = Pandoc.pygments

markdownDialect :: Extensions
markdownDialect = Pandoc.pandocExtensions

markdownToPandoc ::
  ( ?readerOpts :: Pandoc.ReaderOptions
  ) =>
  Text ->
  Action Pandoc
markdownToPandoc =
  Pandoc.runPandoc . Pandoc.readMarkdown ?readerOpts

pandocToHtml5 ::
  ( ?writerOpts :: Pandoc.WriterOptions
  ) =>
  Pandoc ->
  Action Text
pandocToHtml5 =
  Pandoc.runPandoc . Pandoc.writeHtml5String ?writerOpts

processCitations :: Pandoc -> Action Pandoc
processCitations =
  Pandoc.runPandoc . Citeproc.processCitations

postprocessHtml5 :: FilePath -> FilePath -> Text -> Text
postprocessHtml5 outDir out html5 =
  html5
    & TagSoup.withUrls (implicitIndexFile . relativizeUrl outDir out)
    & TagSoup.addDefaultTableHeaderScope "col"
    & Pandoc.postprocessHtml5

--------------------------------------------------------------------------------
-- Metadata

-- | Get the default metadata for the website.
getSiteMetadata :: () -> Action Metadata
getSiteMetadata () = do
  siteMetadata <- readYaml' "src/site.yml"
  buildDateFld <- currentDateField rfc822DateFormat "build_date"
  let metadata = mconcat [siteMetadata, buildDateFld]
  return $ constField "site" metadata

-- | Get a file body and its metadata, including derived metadata.
--
--   This function adds the following metadata fields,
--   in addition to the metadata added by 'getSiteMetadata':
--
--     - @url@: The URL to the output file.
--     - @body@: The body of the source file.
--     - @source@: The path to the source file.
--     - @modified_date@: The date at which the file was last modified, in the ISO8601 format.
--     - @build_date@: The date at which the is website was last built, in the RFC822 format.
--     - @highlight-css@: The CSS for syntax highlighting, if the original file specifies 'highlight'.
getFileWithMetadata ::
  ( ?routingTable :: RoutingTable,
    ?getSiteMetadata :: () -> Action Metadata
  ) =>
  FilePath ->
  Action (Metadata, Text)
getFileWithMetadata src = do
  out <- route src
  let url = "/" <> makeRelative outDir out
  siteMetadata <- ?getSiteMetadata ()
  (fileMetadata, body) <- readFileWithMetadata' src
  let urlFld = constField "url" url
  let bodyFld = constField "body" body
  let sourceFld = constField "source" src
  modifiedDateFld <- lastModifiedISO8601Field src "modified_date"
  let metadata = mconcat [siteMetadata, fileMetadata, urlFld, bodyFld, sourceFld, modifiedDateFld]
  return (metadata, body)

-- | Get a metadata object representing all posts.
--
--   This function adds the following metadata fields for each post,
--   in addition to the metadata added by 'getFileWithMetadata':
--
--   - @date@: The date of the post, in a human readable format.
--   - @date_rfc822@: The date of the post, in the RFC822 date format.
getPostWithMetadata ::
  ( ?routingTable :: RoutingTable,
    ?getFileWithMetadata :: FilePath -> Action (Metadata, Text)
  ) =>
  FilePath ->
  Action (Metadata, Text)
getPostWithMetadata src = do
  (fileMetadata, body) <- ?getFileWithMetadata src
  dateFld <- either fail return $ postDateField "%a %-d %b, %Y" src "date"
  dateRfc822Fld <- either fail return $ postDateField rfc822DateFormat src "date_rfc822"
  let metadata = mconcat [fileMetadata, dateFld, dateRfc822Fld]
  return (metadata, body)

-- | Get a metadata object representing all posts.
--
--   This function adds the following metadata fields for each post,
--   in addition to the metadata added by 'getFileWithMetadata':
--
--   - @body_html@: The rendered HTML body of the source file.
--   - @teaser_html@: The rendered HTML teaser for the post.
--   - @teaser_plain@: The plain text teaser for the post.
getPostsMetadata ::
  ( ?routingTable :: RoutingTable,
    ?getPostWithMetadata :: FilePath -> Action (Metadata, Text)
  ) =>
  () ->
  Action Metadata
getPostsMetadata () = do
  -- Get posts from routing table
  postSrcs <- filter isPostSrc <$> sources
  -- Gather metadata for each post
  postsMetadata <- forM postSrcs $ \src -> do
    -- Get output file for URL and html-body anchor for teaser
    (out, ankHtmlBody) <- (,) <$> route src <*> routeAnchor "html-body" src
    let url = "/" <> makeRelative outDir out
    postMetadata <- fst <$> ?getPostWithMetadata src
    bodyHtml <- readFile' ankHtmlBody
    let bodyHtmlFld = constField "body_html" bodyHtml
    teaserHtmlFld <- either fail return $ htmlTeaserField url bodyHtml "teaser_html"
    teaserPlainFld <- either fail return $ textTeaserField bodyHtml "teaser_plain"
    return $ mconcat [postMetadata, bodyHtmlFld, teaserHtmlFld, teaserPlainFld]
  return $ constField "post" (reverse postsMetadata)

-- | Get a template from the @templates/@ directory.
getTemplateFile :: FilePath -> Action Template
getTemplateFile inputFile = do
  let inputPath = "templates" </> inputFile
  need [inputPath]
  compileTemplateFile inputPath
