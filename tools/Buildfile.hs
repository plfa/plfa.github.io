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

    -- NOTE: required by 'makeFileWithMetadataGetter', 'makePostMetadataGetter', and 'makePostListMetadataGetter'
    let ?outputDirectory = outDir

    --------------------------------------------------------------------------------
    -- Cached file, template, and metadata getters

    defaultMetadataGetter <-
      makeDefaultMetadataGetter
        def
          { defaultMetadataFiles = ["src/site.yml", "src/toc.yml"],
            includeBuildDate = Just "build_date"
          }
    let ?getDefaultMetadata = defaultMetadataGetter

    fileWithMetadataGetter <-
      makeFileWithMetadataGetter
        def
    let ?getFileWithMetadata = fileWithMetadataGetter

    templateFileGetter <-
      makeTemplateFileGetter
        def
          { templateDirectory = "templates"
          }
    let ?getTemplateFile = templateFileGetter

    -- Default Pandoc options
    let ?readerOpts =
          def
            { readerExtensions = markdownDialect
            }
    let ?writerOpts =
          def
            { writerHTMLMathMethod = KaTeX "",
              writerEmailObfuscation = JavascriptObfuscation,
              writerHighlightStyle = Just highlightStyle
            }

    --------------------------------------------------------------------------------
    -- Agda link fixers

    cachedGetAgdaLinkFixer <- newCache $ \() ->
      Agda.makeAgdaLinkFixer (Just standardLibrary) localLibraries otherLibraries
    let ?getAgdaLinkFixer = cachedGetAgdaLinkFixer

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
