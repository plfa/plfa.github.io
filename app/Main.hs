import Data.List qualified as L
import Development.Shake
import Development.Shake.FilePath
import PLFA.Agda
import PLFA.CSS
import PLFA.Data.Text qualified as T
import Text.Pandoc
import Text.Pandoc.Highlighting (tango)

cacheDir, htmlDir, siteDir, srcDir, stdlibSrcDir :: FilePath
cacheDir     = "_build"
htmlDir      = cacheDir </> "html"
texDir       = cacheDir </> "tex"
siteDir      = "_site"
srcDir       = "src"
stdlibSrcDir = "standard-library" </> "src"
agdaOpts     = AgdaOpts
  { format = undefined,
    tmpDir = cacheDir </> "tmp",
    includePaths = [srcDir, stdlibSrcDir],
    inputFile = undefined
  }

opts :: ShakeOptions
opts = shakeOptions { shakeFiles = cacheDir </> "shake" }

main :: IO ()
main = shakeArgs opts $ do

  -- compile static files

  -- Compile templates


  -- Compile Markdown files

  -- Compile literate Agda files to HTML
  want [texDir </> "src/plfa/part1/Naturals.lagda.tex"]
  texDir </> "**/*.tex" %> \out -> do
    src <- dropPrefix texDir (out -<.> "md")
    need [src]
    content <- callAgdaWith agdaOpts {format = LaTeX, inputFile = src}
    T.writeFile out content

  -- Compile literate Agda files to HTML
  want [htmlDir </> "src/plfa/part1/Naturals.lagda.md"]
  htmlDir </> "**/*.md" %> \out -> do
    src <- dropPrefix htmlDir out
    need [src]
    content <- callAgdaWith agdaOpts {format = Markdown, inputFile = src}
    T.writeFile out content

  -- Compile style files
  siteDir </> "css/style.css" %> \out -> do
    let src = "css/minima.scss"
    need [src]
    css <- compileSassWith def {sassIncludePaths = Just ["css"]} src
    min <- minifyCSSWith def css
    T.writeFile out min

dropPrefix :: FilePath -> FilePath -> Action FilePath
dropPrefix prefixPath filePath = do
  case L.stripPrefix (splitDirectories prefixPath) (splitDirectories filePath) of
    Nothing   -> fail $ "Cannot strip prefix " <> prefixPath <> " from " <> filePath
    Just path -> return (joinPath path)

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
