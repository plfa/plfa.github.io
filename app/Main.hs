import Control.Exception (assert)
import Control.Monad (forM_)
import Data.Map qualified as M
import Development.Shake
import Development.Shake.Agda
import Development.Shake.CSS
import Development.Shake.FilePath
import Development.Shake.Sass
import Development.Shake.Text qualified as T
import General.Extra
import System.FilePath.Find
import Text.Pandoc
import Text.Pandoc.Highlighting (tango)
import Text.Printf


-- Directories

cacheDir      = "_build"
htmlCacheDir  = cacheDir </> "html"
mdCacheDir    = cacheDir </> "md"
texCacheDir   = cacheDir </> "tex"
siteDir       = "_site"
srcDir        = "src"
staticSrcDir  = "public"
cssSrcDir     = "css"
stdlibDir     = "standard-library"

-- Options

shakeOpts = shakeOptions
  { shakeFiles = cacheDir </> "shake"
  }


-- Build rules

-- | Convert paths from Markdown source files to highlighted TeX files.
texCachePath :: FilePath -> FilePath
texCachePath filePath = texCacheDir </> replaceExtensions filePath "tex"

-- | Convert paths from Markdown source files to highlighted Markdown files.
mdCachePath :: FilePath -> FilePath
mdCachePath filePath = mdCacheDir </> replaceExtensions filePath "md"

main :: IO ()
main = do

  -- Enumerate files

  -- All files in '$staticSrcDir' are copied verbatim to '$siteDir',
  -- preserving their relative paths.
  staticFiles <- find always (fileType ==? RegularFile) staticSrcDir

  -- All .lagda.md files are rendered to highlighted Markdown and LaTeX files,
  -- for construction of the EPUB and PDF versions of PLFA, and the Markdown
  -- versions are further compiled to standalone HTML pages for the web version
  -- of PLFA.
  lagdaMdFiles <- find always (fileName ~~? "*.lagda.md") srcDir
  let mdCacheFiles = map mdCachePath lagdaMdFiles
  let texCacheFiles = map texCachePath lagdaMdFiles

  -- All files in '$cssSrcDir' are compiled into a single minified css file,
  -- written to '$siteDir/$staticSrcDir/style.css'
  scssFiles <- find always (fileName ~~? "*.scss") cssSrcDir
  let styleFile = siteDir </> staticSrcDir </> "style.css"

  -- Options for Agda highlighting
  let plfa = def {libDir = srcDir}
  stdlib <- standardLibraryAgdaLib stdlibDir
  let agdaLibs = [plfa, stdlib]
  let agdaOpts = def {
        formats   = [LaTeX, Markdown],
        tmpDir    = cacheDir </> "tmp",
        libraries = agdaLibs
        }
  fixLinks <- prepareFixLinks agdaLibs

  -- Main dependency logic.
  shakeArgs shakeOpts $ do

    -- compile static files
    want staticFiles

    forM_ staticFiles $ \src ->
      siteDir </> src %> \out -> do
        putInfo $ printf "Copy %s to %s" src out
        copyFile' src out

    -- Compile templates

    -- Compile Markdown files

    -- Compile literate Agda files to HTML and LaTeX
    want (texCacheFiles <> mdCacheFiles)

    forM_ lagdaMdFiles $ \src -> do
      let texCacheOut = texCachePath src
      let mdCacheOut = mdCachePath src
      [texCacheOut, mdCacheOut] &%> \_ -> do

        -- Register the source file as a dependency
        need [src]

        -- Run Agda with both LaTeX and HTML highlighting.
        putInfo $ "Highlight " <> src
        let outMap = M.fromList [(LaTeX, texCacheOut), (Markdown, mdCacheOut)]
        contentMap <- highlightAgdaWith agdaOpts {inputFile = src, outputFiles = outMap}
        assert (M.null contentMap) $ return ()

    -- Compile style files
    want [styleFile]

    styleFile %> \out -> do
      let src = cssSrcDir </> "style.scss"
      need scssFiles
      putInfo $ printf "Compile %s to %s" src out
      css <- compileSassWith def {sassIncludePaths = Just [cssSrcDir]} src
      cssMin <- minifyCSSWith def css
      T.writeFile' out cssMin

pandocReaderOpts :: ReaderOptions
pandocReaderOpts = def
  { readerExtensions =
      extensionsFromList
      [ Ext_all_symbols_escapable
      , Ext_auto_identifiers
      , Ext_citations
      , Ext_footnotes
      , Ext_header_attributes
      , Ext_implicit_header_references
      , Ext_intraword_underscores
      , Ext_markdown_in_html_blocks
      , Ext_shortcut_reference_links
      , Ext_smart
      , Ext_superscript
      , Ext_subscript
      , Ext_task_lists
      , Ext_yaml_metadata_block
      ]
      <>
      githubMarkdownExtensions
  }

pandocWriterOpts :: WriterOptions
pandocWriterOpts = def
  { writerHighlightStyle = Just tango
  }
