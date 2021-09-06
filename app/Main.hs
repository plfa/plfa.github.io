{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

import Control.Exception (displayException)
import Control.Monad (forM_)
import Data.Default.Class (Default (..))
import Data.Map qualified as M
import Data.Text (Text)
import Data.Text.ICU qualified as ICU
import Data.Text.ICU.Replace qualified as ICU
import Development.Shake
import Development.Shake.FilePath
import PLFA.Build.Agda
import PLFA.Build.Metadata
import PLFA.Build.Style.CSS
import PLFA.Build.Style.Sass
import PLFA.Build.Text qualified as T
import PLFA.Util
import System.FilePath.Find
import Text.Mustache as Mustache
import Text.Mustache.Compile as Mustache
import Text.Pandoc as Pandoc
import Text.Pandoc.Writers.HTML as Pandoc


-- Directories

cacheDir      = "_build"
htmlCacheDir  = cacheDir </> "html"
epubCacheDir  = cacheDir </> "epub"
texCacheDir   = cacheDir </> "tex"
siteDir       = "_site"
srcDir        = "src"
staticSrcDir  = "public"
cssSrcDir     = "css"
stdlibDir     = "standard-library"
templateDir   = "templates"

-- Options

shakeOpts = shakeOptions
  { shakeFiles = cacheDir </> "shake"
  }

permalinkPath :: FilePath -> IO FilePath
permalinkPath src = do
  metadata <- getMetadata src
  permalink <- getPermalink metadata
  return $ siteDir </> permalink </> "index.html"


main :: IO ()
main = do

  -- * Input & Output Files

  -- All files in '$staticSrcDir' are copied verbatim to '$siteDir',
  -- preserving their relative paths.
  staticFiles <- find always (fileType ==? RegularFile) staticSrcDir

  -- All .lagda.md files are rendered to highlighted Markdown and LaTeX files,
  -- for construction of the EPUB and PDF versions of PLFA, and the Markdown
  -- versions are further compiled to standalone HTML pages for the web version
  -- of PLFA.
  lagdaMdFiles <- find always (fileName ~~? "*.lagda.md") srcDir

  -- All files in '$cssSrcDir' are compiled into a single minified css file,
  -- written to '$siteDir/$staticSrcDir/style.css'
  scssFiles <- find always (fileName ~~? "*.scss") cssSrcDir
  let styleFile = siteDir </> staticSrcDir </> "style.css"

  -- Options for Agda highlighting
  stdlib <- standardLibraryAgdaLib stdlibDir
  fixLinks <- prepareFixLinks [def{libDir = srcDir}, stdlib]


  -- * Build Tasks

  shakeArgs shakeOpts $ do

    -- Compile a Mustache template
    compileTemplate <- newCache $ \src -> do
      tplOrError <- liftIO (Mustache.automaticCompile [templateDir] src)
      tpl <- liftEither @Action show tplOrError
      need (Mustache.getPartials (Mustache.ast tpl))
      return tpl

    -- Highlight a source file as HTML
    highlightHTML <- newCache $ \(dir, src) -> do
      resultMap <- highlightAgdaWith def
                   { formats   = [Markdown],
                     libraries = [def{libDir = dir}, stdlib],
                     inputFile = src
                   }
      liftMaybe ("Highlight failed for " <> src) $
        M.lookup Markdown resultMap

    -- Render Markdown to HTML
    markdownToHTML <- newCache $ \src -> do
      runPandocIO $ do
        ast <- Pandoc.readMarkdown readerOpts src
        Pandoc.writeHtml5String writerOpts ast

    -- Render Markdown to EPUB HTML
    markdownToEPUB <- newCache $ \src -> do
      runPandocIO $ do
        ast <- Pandoc.readMarkdown readerOpts src
        Pandoc.writeHtmlStringForEPUB EPUB3 writerOpts ast

    -- Copy static files
    want staticFiles

    forM_ staticFiles $ \src ->
      siteDir </> src %> \out -> do
        putInfo $ "Copy " <> src
        copyFile' src out

    -- Compile literate Agda files to HTML
    let htmlStage1, htmlStage2, htmlStage3 :: FilePath -> FilePath
        htmlStage1 src = htmlCacheDir </> "stage1" </> src
        htmlStage2 src = htmlCacheDir </> "stage2" </> replaceExtensions src "md"
        epubStage3 src = epubCacheDir </> "stage3" </> replaceExtensions src "html"
        htmlStage3 src = htmlCacheDir </> "stage3" </> replaceExtensions src "html"

    forM_ lagdaMdFiles $ \src -> do

      want [htmlStage3 src, epubStage3 src]

      -- Stage 1: Preprocess the Markdown files
      htmlStage1 src %> \out -> do
        content <- T.readFile' src
        putInfo $ "Preprocess " <> src
        T.writeFile' out (preprocessForHtml content)

      -- Stage 2: Highlight the Agda source
      htmlStage2 src %> \out -> do
        need [htmlStage1 fp | fp <- lagdaMdFiles]
        putInfo $ "Highlight " <> src
        markdown <- highlightHTML (htmlStage1 srcDir, htmlStage1 src)
        T.writeFile' out markdown

      -- Stage 3: Render the Markdown to HTML
      htmlStage3 src %> \out -> do
        markdown <- T.readFile' (htmlStage2 src)
        putInfo $ "Render " <> src
        html5 <- markdownToHTML markdown
        T.writeFile' out html5

      -- Stage 3: Render the Markdown to HTML (EPUB)
      epubStage3 src %> \out -> do
        markdown <- T.readFile' (htmlStage2 src)
        putInfo $ "Render " <> src
        xhtml <- markdownToEPUB markdown
        T.writeFile' out xhtml

    -- Compile style files
    want [styleFile]

    styleFile %> \out -> do
      let src = cssSrcDir </> "style.scss"
      need scssFiles
      putInfo $ "Compile " <> src
      css <- compileSassWith def {sassIncludePaths = Just [cssSrcDir]} src
      cssMin <- minifyCSSWith def css
      T.writeFile' out cssMin

runPandocIO :: PandocIO a -> Action a
runPandocIO action = do
  resultOrError <- liftIO (Pandoc.runIO action)
  liftEither displayException resultOrError

readerOpts :: ReaderOptions
readerOpts = def
  { readerExtensions =
      extensionsFromList
      [ Ext_all_symbols_escapable
      , Ext_smart
      , Ext_superscript
      , Ext_subscript
      , Ext_citations
      , Ext_footnotes
      , Ext_header_attributes
      , Ext_intraword_underscores
      , Ext_markdown_in_html_blocks
      , Ext_shortcut_reference_links
      , Ext_yaml_metadata_block
      , Ext_raw_attribute
      ]
      <>
      githubMarkdownExtensions
  }

writerOpts :: WriterOptions
writerOpts = def


--------------------------------------------------------------------------------
-- Preprocessing literate Agda files
--------------------------------------------------------------------------------

reCodeBlock :: ICU.Regex
reCodeBlock = ICU.regex [ICU.DotAll, ICU.Multiline] "^```\\s*agda\\s*$(.*?)^```\\s*$"

preprocessForHtml :: Text -> Text
preprocessForHtml = ICU.replaceAll reCodeBlock "\n\n~~~{=html}\n```agda$1```\n\n~~~\n\n"

preprocessForLaTeX :: Text -> Text
preprocessForLaTeX = ICU.replaceAll reCodeBlock "\n\n~~~{=latex}\n\\begin{code}$1\\end{code}\n\n~~~\n\n"
