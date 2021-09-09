import Control.Monad (forM, forM_, when)
import Data.Function (on)
import Data.Functor ((<&>))
import Data.List (sortBy)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromMaybe)
import Data.Text qualified as T
import Data.Text.ICU qualified as ICU
import Data.Text.ICU.Replace qualified as ICU
import PLFA.Build.Agda
import PLFA.Build.Gather
import PLFA.Build.Metadata
import PLFA.Build.Pandoc as Pandoc
import PLFA.Build.Prelude
import PLFA.Build.Route
import PLFA.Build.Style.CSS
import PLFA.Build.Style.Sass


--------------------------------------------------------------------------------
-- Directories
--------------------------------------------------------------------------------

authorDir         = rootDir </> "authors"
cacheDir          = rootDir </> "_build"
contributorDir    = rootDir </> "contributors"
courseDir         = rootDir </> "courses"
cssDir            = rootDir </> "css"
epubCacheDir      = cacheDir </> "epub"
htmlCacheDir      = cacheDir </> "html"
postsDir          = rootDir </> "posts"
publicDir         = rootDir </> "public"
rootDir           = "."
siteDir           = rootDir </> "_site"
stdlibDir         = rootDir </> "standard-library"
stdlibAgdaLibFile = stdlibDir </> "standard-library.agda-lib"
srcDir            = rootDir </> "src"
texCacheDir       = cacheDir </> "tex"
templateDir       = rootDir </> "templates"

main :: IO ()
main = do

  --------------------------------------------------------------------------------
  -- Gather input files and build routing table
  --------------------------------------------------------------------------------

  staticFiles           <- gather always regularFile [publicDir]
  agdaLibs              <- gatherAgdaLibs [courseDir, srcDir]
  stdlib                <- readStandardLibraryAgdaLib stdlibDir
  mdFiles               <- gatherMdFiles [courseDir, srcDir]
  scssFiles             <- gatherSassFiles [cssDir]
  postMdFiles           <- gatherMdFiles [postsDir]
  lagdaMdFilesByAgdaLib <- gatherLagdaMdFilesForAgdaLibs agdaLibs

  permalinkRoutingTable <- buildPermalinkRoutingTable siteDir mdFiles
  let postsRoutingTable = asRoutingTable (\src -> siteDir </> src -<.> "html") postMdFiles
  let routingTable = permalinkRoutingTable <> postsRoutingTable

  shakeArgs shakeOpts $ do

    --------------------------------------------------------------------------------
    -- Highlighting literate Agda files
    --------------------------------------------------------------------------------

    let agdaLibMap :: Map LibName AgdaLib
        agdaLibMap = M.fromList $
          [ (libName agdaLib, agdaLib) | agdaLib <- (stdlib : agdaLibs) ]

    let resolveDepend :: LibName -> AgdaLib
        resolveDepend name =
          fromMaybe (error $ "Could not find " <> name) (M.lookup name agdaLibMap)

    let resolveDepends :: [LibName] -> [AgdaLib]
        resolveDepends libs = map resolveDepend libs

    let highlightAgdaFor:: FilePath -> [AgdaLib] -> FilePath -> Format -> Action Text
        highlightAgdaFor librariesFile deps src format = do
          resultMap <- highlightAgdaWith def
                       { formats       = [format],
                         librariesFile = Just librariesFile,
                         libraries     = deps,
                         inputFile     = src
                       }
          liftMaybe ("Highlight failed for " <> src) $
            M.lookup format resultMap


    --------------------------------------------------------------------------------
    -- Format conversion with Pandoc
    --------------------------------------------------------------------------------

    getFixLinks <- newCache $ \() -> do
      liftIO $ prepareFixLinks $ [stdlib] <> agdaLibs

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
      readYamlFrontmatter' $ srcDir </> "site.metadata"

    getFileMetadata <- newCache $ \inputFile -> do
      siteMetadata <- getSiteMetadata ()
      frontmatterMetadata <- readYamlFrontmatter' inputFile
      lastModifiedMetadata <- lastModified inputFile "modified_date"
      return $ mconcat
        [ siteMetadata,
          addTitleVariants frontmatterMetadata,
          lastModifiedMetadata,
          sourceFile inputFile "source"
        ]

    getTocMetadata <- newCache $ \() -> do
      metadata     <- readYamlFrontmatter' $ srcDir </> "toc.metadata"
      authors      <- getAuthors ()
      contributors <- getContributors()
      return $
        metadata & "authors"      .~ authors
                 & "contributors" .~ contributors

    getSiteTocMetadata <- newCache $ \() -> do
      toc <- getTocMetadata ()
      resolveIncludes getFileMetadata toc

    getPostMetadata <- newCache $ \() -> do
      posts <-
        forM postMdFiles $ \postMdFile -> do
          (body, metadata) <- readFileWithMetadata' postMdFile
          let bodyField   = mempty & "body" .~ body
          let dateField   = dateFromFilePath postMdFile "date"
          let teaserField = teaser body "teaser"
          let urlField    = mempty & "url" .~ route routingTable postMdFile
          return $ mconcat [metadata, bodyField, dateField, teaserField, urlField]
      return $ mempty & "post" .~ posts

    --------------------------------------------------------------------------------
    -- Static files
    --
    -- All files in '$publicDir' are copied verbatim to '$siteDir', preserving
    -- their relative paths.
    --------------------------------------------------------------------------------

    forM_ staticFiles $ \src -> do
      let out = siteDir </> src
      want [out]
      out %> \_ -> copyFile' src out

    --------------------------------------------------------------------------------
    -- HTML compilation
    --
    -- Literate Agda files are rendered in stages:
    --
    --   Stage 1. Preprocessing. Literate code blocks are marked as raw HTML or
    --            LaTeX by wrapping them in a code block with the appropriate raw
    --            attribute. For the LaTeX backend, the backtick fences are replaced
    --            by a LaTeX code environment.
    --
    --   Stage 2. Highlighting. Literate code blocks are highlighted using Agda.
    --
    --   Stage 3. Templating & Rendering. The relevant templates are applied, and
    --            the Markdown is rendered to HTML and LaTeX using Pandoc.
    --
    -- Markdown files are copied verbatim to Stage 2 and pass through Stage 3.
    --
    --------------------------------------------------------------------------------

    let htmlStage1, htmlStage2, htmlStage3 :: FilePath -> FilePath
        htmlStage1 src = normalise $ htmlCacheDir </> "stage1" </> src
        htmlStage2 src = normalise $ htmlCacheDir </> "stage2" </> replaceExtensions src "md"
        htmlStage3 src = normalise $ route routingTable src

    let htmlStage1Lib :: AgdaLib -> AgdaLib
        htmlStage1Lib agdaLib
          | agdaLib == stdlib = agdaLib
          | otherwise         = agdaLib
            { libFile     = htmlStage1 (libFile agdaLib),
              libIncludes = map htmlStage1 (libIncludes agdaLib)
            }

    want [htmlStage3 src | src <- mdFiles]

    -- Generate an appropriate libraries file
    htmlStage1 ".agda/libraries" %> \out -> do
      let libraries = [ libFile (htmlStage1Lib lib) | lib <- stdlib : agdaLibs ]
      need libraries
      writeFile' out (T.unlines (map T.pack libraries))

    -- Compile .lagda.md files in the context of their .agda-lib file
    forM_ lagdaMdFilesByAgdaLib $ \(agdaLib, lagdaMdFiles) -> do

      -- Copy over .agda-lib file
      libFile (htmlStage1Lib agdaLib) %> \out -> do
        let src = libFile agdaLib
        need [src]
        copyFile' src out

      forM_ lagdaMdFiles $ \src -> do

        -- Stage 1: Preprocess literate Agda files
        htmlStage1 src %> \out -> do
          need [src]
          readFile' src
            <&> preprocessForHtml
            >>= writeFile' out

        -- Stage 2: Highlight literate Agda files
        htmlStage2 src %> \out -> do
          -- Update file paths in library files
          let libraries = [ htmlStage1Lib lib | lib <- agdaLib : resolveDepends (libDepends agdaLib) ]
          -- Need updated libraries file, .agda-lib files, and all .lagda.md files
          need [ htmlStage1 ".agda/libraries" ]
          need [ libFile lib | lib <- libraries]
          need [ htmlStage1 lagdaMdFile | lagdaMdFile <- lagdaMdFiles ]
          -- Highlight Agda as HTML
          markdown <- highlightAgdaFor (htmlStage1 ".agda/libraries") libraries (htmlStage1 src) Markdown
          writeFile' out markdown
          putInfo $ "Checked " <> src

    forM_ mdFiles $ \src -> do

      when (takeExtensions src /= ".lagda.md") $ do

        -- Stage 2: Copy Markdown files verbatim
        htmlStage2 src %> \out -> do
          need [src]
          copyFile' src out

      -- Stage 3: Render the Markdown to HTML
      htmlStage3 src %> \out -> do
        need [htmlStage2 src]
        fileMetadata    <- getFileMetadata src
        siteTocMetadata <- getSiteTocMetadata ()
        postMetadata    <- getPostMetadata ()
        let metadata = mconcat [fileMetadata, siteTocMetadata, postMetadata]
        applyAsTemplate (htmlStage2 src) metadata
          >>= markdownToHTML
          >>= applyTemplate "templates/page.html" metadata
          >>= applyTemplate "templates/default.html" metadata
          <&> withUrls relativizeUrl
          >>= writeFile' out
        putInfo $ "Updated " <> src

    --------------------------------------------------------------------------------
    -- Compile style files
    --
    -- All Sass files in '$cssDir' are compiled into a single minified CSS file,
    -- which is then written to '$styleFile'.
    --------------------------------------------------------------------------------

    let styleFile = siteDir </> publicDir </> cssDir </> "style.css"

    want [styleFile]

    styleFile %> \out -> do
      let src = cssDir </> "style.scss"
      need scssFiles
      css <- compileSassWith def {sassIncludePaths = Just [cssDir]} src
      cssMin <- minifyCSSWith def css
      writeFile' out cssMin
      putInfo $ "Updated " <> out


--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------

shakeOpts = shakeOptions
  { shakeProgress = progressSimple }

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
      , Ext_fenced_divs
      , Ext_bracketed_spans
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
