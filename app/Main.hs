import Control.Monad (forM, forM_, when)
import Data.Function (on)
import Data.Functor ((<&>))
import Data.List (sortBy)
import Data.Map qualified as M
import Data.Text.ICU qualified as ICU
import Data.Text.ICU.Replace qualified as ICU
import PLFA.Build.Agda
import PLFA.Build.Metadata
import PLFA.Build.Pandoc as Pandoc
import PLFA.Build.Prelude
import PLFA.Build.Route
import PLFA.Build.Style.CSS
import PLFA.Build.Style.Sass
import System.FilePath.Find


--------------------------------------------------------------------------------
-- Directories
--------------------------------------------------------------------------------

cacheDir       = "_build"
htmlCacheDir   = cacheDir </> "html"
epubCacheDir   = cacheDir </> "epub"
texCacheDir    = cacheDir </> "tex"
siteDir        = "_site"
srcDir         = "src"
authorDir      = "authors"
contributorDir = "contributors"
publicDir      = "public"
cssDir         = "css"
stdlibDir      = "standard-library"
templateDir    = "templates"


-- TODO:
--
--   - Adapt code which unfolds include paths to include metadata from included files.
--   - Copy code which includes titlerunning and subtitle.
--   - Finish PDF and EPUB.
--

main :: IO ()
main = do

  --------------------------------------------------------------------------------
  -- Gather input files
  --------------------------------------------------------------------------------

  staticFiles <-
    find always (fileType ==? RegularFile) publicDir

  mdFiles <-
    find always (fileType ==? RegularFile &&? fileName ~~? "*.md") srcDir

  lagdaMdFiles <-
    find always (fileType ==? RegularFile &&? fileName ~~? "*.lagda.md") srcDir

  permalinkRoutingTable <-
    getPermalinkRoutingTable siteDir mdFiles

  shakeArgs shakeOpts $ do

    --------------------------------------------------------------------------------
    -- Highlighting literate Agda files
    --------------------------------------------------------------------------------

    getStandardLibraryAgdaLib <- newCache $ \() -> liftIO $
      standardLibraryAgdaLib stdlibDir

    let highlightHTML :: (FilePath, FilePath) -> Action Text
        highlightHTML (dir, src) = do
          stdlib <- getStandardLibraryAgdaLib ()
          resultMap <- highlightAgdaWith def
                       { formats   = [Markdown],
                         libraries = [def{libDir = dir}, stdlib],
                         inputFile = src
                       }
          liftMaybe ("Highlight failed for " <> src) $
            M.lookup Markdown resultMap

    let highlightLaTeX :: (FilePath, FilePath) -> Action Text
        highlightLaTeX (dir, src) = do
          stdlib <- getStandardLibraryAgdaLib ()
          resultMap <- highlightAgdaWith def
                       { formats   = [Markdown],
                         libraries = [def{libDir = dir}, stdlib],
                         inputFile = src
                       }
          liftMaybe ("Highlight failed for " <> src) $
            M.lookup LaTeX resultMap


    --------------------------------------------------------------------------------
    -- Format conversion with Pandoc
    --------------------------------------------------------------------------------

    getFixLinks <- newCache $ \() -> do
      stdlib <- getStandardLibraryAgdaLib ()
      liftIO $
        prepareFixLinks [def{libDir = srcDir}, stdlib]

    let markdownToHTML :: Text -> Action Text
        markdownToHTML src = do
          fixLinks <- getFixLinks ()
          runPandocIO $ do
            ast <- Pandoc.readMarkdown readerOpts src
            let ast' = withUrlsPandoc fixLinks ast
            Pandoc.writeHtml5String writerOpts ast'

    let markdownToEPUB :: Text -> Action Text
        markdownToEPUB src = runPandocIO $ do
          ast <- Pandoc.readMarkdown readerOpts src
          Pandoc.writeHtmlStringForEPUB EPUB3 writerOpts ast

    let markdownToLaTeX :: Text -> Action Text
        markdownToLaTeX src = runPandocIO $ do
          ast <- Pandoc.readMarkdown readerOpts src
          Pandoc.writeLaTeX writerOpts ast


    --------------------------------------------------------------------------------
    -- Templates
    --------------------------------------------------------------------------------

    getTemplate <- newCache $ \inputFile -> do
      need [inputFile]
      Pandoc.compileTemplate inputFile

    let applyTemplate :: FilePath -> Metadata -> Text -> Action Text
        applyTemplate inputFile metadata body = do
          tpl <- getTemplate inputFile
          return $ Pandoc.renderTemplate tpl (metadata & "body" .~ body)

    let applyAsTemplate :: FilePath -> Metadata -> Action Text
        applyAsTemplate inputFile metadata = do
          tpl <- getTemplate inputFile
          return $ Pandoc.renderTemplate tpl metadata


    --------------------------------------------------------------------------------
    -- Metadata
    --------------------------------------------------------------------------------

    getAuthors <- newCache $ \() -> do
      authorFiles <- liftIO $ find always (fileName ~~? "*.metadata") authorDir
      authors <- traverse readYamlFrontmatter' authorFiles
      return (authors :: [Author])

    getContributors <- newCache $ \() -> do
      contributorFiles <- liftIO $ find always (fileName ~~? "*.metadata") contributorDir
      contributors <- traverse readYamlFrontmatter' contributorFiles
      let sortedContributors = sortBy (compare `on` contributorCount) contributors
      return (sortedContributors :: [Contributor])

    getSiteMetadata <- newCache $ \() -> do
      metadata <- readYamlFrontmatter' $ srcDir </> "site.metadata"
      authors <- getAuthors ()
      contributors <- getContributors()
      return $
        metadata & "authors"      .~ authors
                 & "contributors" .~ contributors

    getFileMetadata <- newCache $ \inputFile -> do
      siteMetadata <- getSiteMetadata ()
      frontmatterMetadata <- readYamlFrontmatter' inputFile
      lastModifiedMetadata <- lastModified inputFile "modified_date"
      return $ mconcat
        [ siteMetadata,
          frontmatterMetadata,
          lastModifiedMetadata,
          sourceFile inputFile "source"
        ]


    --------------------------------------------------------------------------------
    -- Static files
    --
    -- All files in '$publicDir' are copied verbatim to '$siteDir', preserving
    -- their relative paths.
    --------------------------------------------------------------------------------

    forM_ staticFiles $ \src -> do
      let out = siteDir </> src

      want [out]

      out %> \_ -> do
        putInfo $ "Copy " <> src
        copyFile' src out

    --------------------------------------------------------------------------------
    -- HTML compilation
    --------------------------------------------------------------------------------

    let htmlStage1, htmlStage2, htmlStage3 :: FilePath -> FilePath
        htmlStage1 src = htmlCacheDir </> "stage1" </> src
        htmlStage2 src = htmlCacheDir </> "stage2" </> replaceExtensions src "md"
        htmlStage3 src = htmlCacheDir </> "stage3" </> replaceExtensions src "html"
        htmlStage4 src = permalinkRoutingTable M.! src

    --------------------------------------------------------------------------------
    -- Compile source files to HTML
    --
    -- Literate Agda files are rendered in four stages:
    --
    --   Stage 1. Preprocessing. Literate code blocks are marked as raw HTML or
    --            LaTeX by wrapping them in a code block with the appropriate raw
    --            attribute. For the LaTeX backend, the backtick fences are replaced
    --            by a LaTeX code environment.
    --
    --   Stage 2. Highlighting. Literate code blocks are highlighted using Agda.
    --
    --   Stage 3. Rendering. The surrounding Markdown is rendered as either HTML or
    --            LaTeX using Pandoc. The files used on the website are rendered as
    --            HTML5 and the files used in the EPUB are rendered to XHTML.
    --
    --   Stage 4. Templating. The relevant templates are applied, and the file is
    --            written to the path determined by its permalink.
    --
    -- Markdown files are copied verbatim to Stage 2 and pass through Stages 3 & 4.
    --
    --------------------------------------------------------------------------------

    want [htmlStage4 src | src <- mdFiles]

    forM_ mdFiles $ \src -> do

      if (src `elem` lagdaMdFiles) then do

        -- Stage 1: Preprocess literate Agda files
        htmlStage1 src %> \out -> do
          putInfo $ "Preprocess " <> src
          content <- readFile' src
          writeFile' out (preprocessForHtml content)

        -- Stage 2: Highlight literate Agda files
        htmlStage2 src %> \out -> do
          putInfo $ "Highlight " <> src
          need [htmlStage1 fp | fp <- lagdaMdFiles]
          markdown <- highlightHTML (htmlStage1 srcDir, htmlStage1 src)
          writeFile' out markdown

      else do

        -- Stage 2: Copy Markdown files verbatim
        htmlStage2 src %> \out -> do
          putInfo $ "Copy " <> src
          copyFile' src out

      -- Stage 3: Render the Markdown to HTML
      htmlStage3 src %> \out -> do
        putInfo $ "Render " <> src
        markdown <- readFile' (htmlStage2 src)
        html5 <- markdownToHTML markdown
        writeFile' out html5

      -- Stage 4: Apply page template to HTML
      htmlStage4 src %> \out -> do
        putInfo $ "Template " <> src
        metadata <- getFileMetadata src
        applyAsTemplate (htmlStage3 src) metadata
          >>= applyTemplate "templates/page.html" metadata
          >>= applyTemplate "templates/default.html" metadata
          <&> withUrls relativizeUrl
          >>= writeFile' out



    --------------------------------------------------------------------------------
    -- Compile style files
    --
    -- All Sass files in '$cssDir' are compiled into a single minified CSS file,
    -- which is then written to '$styleFile'.
    --------------------------------------------------------------------------------

    getSCSSFiles <- newCache $ \() -> liftIO $
      find always (fileType ==? RegularFile &&? fileName ~~? "*.scss") cssDir

    let styleFile = siteDir </> publicDir </> cssDir </> "style.css"

    want [styleFile]

    styleFile %> \out -> do
      let src = cssDir </> "style.scss"
      putInfo $ "Compile " <> src
      need =<< getSCSSFiles ()
      css <- compileSassWith def {sassIncludePaths = Just [cssDir]} src
      cssMin <- minifyCSSWith def css
      writeFile' out cssMin


--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------

shakeOpts = shakeOptions
  { shakeFiles = cacheDir </> "shake"
  }

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

preprocessForHtml :: Text -> Text
preprocessForHtml = ICU.replaceAll reCodeBlock "\n\n~~~{=html}\n```agda$1```\n\n~~~\n\n"

preprocessForLaTeX :: Text -> Text
preprocessForLaTeX = ICU.replaceAll reCodeBlock "\n\n~~~{=latex}\n\\begin{code}$1\\end{code}\n\n~~~\n\n"

reCodeBlock :: ICU.Regex
reCodeBlock = ICU.regex [ICU.DotAll, ICU.Multiline] "^```\\s*agda\\s*$(.*?)^```\\s*$"
