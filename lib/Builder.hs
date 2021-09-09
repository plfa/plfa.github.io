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
import PLFA.Build.Preprocess
import PLFA.Build.Route
import PLFA.Build.Style.CSS
import PLFA.Build.Style.Sass


--------------------------------------------------------------------------------
-- Directories
--------------------------------------------------------------------------------

authorDir         = "authors"
cacheDir          = "_build"
contributorDir    = "contributors"
courseDir         = "courses"
cssDir            = "css"
epubCacheDir      = cacheDir </> "epub"
htmlCacheDir      = cacheDir </> "html"
postsDir          = "posts"
publicDir         = "public"
siteDir           = "_site"
stdlibDir         = "standard-library"
stdlibAgdaLibFile = stdlibDir </> "standard-library.agda-lib"
srcDir            = "src"
texCacheDir       = cacheDir </> "tex"
templateDir       = "templates"

main :: IO ()
main = do

  --------------------------------------------------------------------------------
  -- Gather input files and build routing table
  --------------------------------------------------------------------------------

  -- Gather files
  staticFiles           <- gather always regularFile [publicDir]
  agdaLibs              <- gatherAgdaLibs [courseDir, srcDir]
  stdlib                <- readStandardLibraryAgdaLib stdlibDir
  mdFiles               <- gatherMdFiles [courseDir, postsDir, srcDir]
  scssFiles             <- gatherSassFiles [cssDir]
  postMdFiles           <- gatherMdFiles [postsDir]
  lagdaMdFilesByAgdaLib <- gatherLagdaMdFilesForAgdaLibs agdaLibs

  -- Build routing table
  permalinkRoutingTable <- buildPermalinkRoutingTable mdFiles
  let postsRoutingTable = asRoutingTable (-<.> "html") postMdFiles
  let errorRoutingTable = asRoutingTable id ["404.html"]
  let routingTable = mconcat [permalinkRoutingTable, postsRoutingTable, errorRoutingTable]

  shakeArgs shakeOpts $ do

    --------------------------------------------------------------------------------
    -- Highlighting literate Agda files
    --------------------------------------------------------------------------------

    -- Create a lookup table of Agda libraries by name.
    --
    -- NOTE: We exclude the standard library from the Agda libraries earlier, so we
    --       can load it using 'readStandardLibraryAgdaLib', which is slightly more
    --       sophisticated, in that it reads the version and constructs the external
    --       URL at which it is hosted. We add it to the lookup table manually here.
    --
    let agdaLibMap :: Map LibName AgdaLib
        agdaLibMap = M.fromList $
          [ (libName agdaLib, agdaLib) | agdaLib <- (stdlib : agdaLibs) ]

    -- Resolve a dependency by name using the Agda library lookup table.
    let resolveDepend :: LibName -> AgdaLib
        resolveDepend name = fromMaybe (error $ "Could not find " <> name) (M.lookup name agdaLibMap)

    -- Highlight Agda code for a given format code with a given 'libraries' file and a
    -- list of libraries, include the library of which the file itself is a part.
    let highlightAgdaFor:: FilePath -> [AgdaLib] -> FilePath -> Format -> Action Text
        highlightAgdaFor librariesFile deps src format = do
          resultMap <- highlightAgdaWith def
            { formats = [format], librariesFile = Just librariesFile, libraries = deps, inputFile = src }
          liftMaybe ("Highlight failed for " <> src) $ M.lookup format resultMap


    --------------------------------------------------------------------------------
    -- Format conversion with Pandoc
    --------------------------------------------------------------------------------

    getFixLinks <- newCache $ \() -> do
      liftIO $ prepareFixLinks $ [stdlib] <> agdaLibs

    -- Render Markdown to HTML5 using Pandoc, applying the code to fix links
    -- to local and external modules.
    --
    -- NOTE: Every Agda file in a local module /must/ have a permalink attribute.
    --
    let markdownToHTML :: Text -> Action Text
        markdownToHTML src = do
          fixLinks <- getFixLinks ()
          runPandocIO $ do
            ast <- Pandoc.readMarkdown readerOpts src
            let ast' = withUrlsPandoc fixLinks ast
            Pandoc.writeHtml5String writerOpts ast'

    -- Render Markdown to XHTML using Pandoc.
    --
    -- NOTE: Currently, all links are left broken.
    --
    let markdownToEPUB :: Text -> Action Text
        markdownToEPUB src = runPandocIO $ do
          ast <- Pandoc.readMarkdown readerOpts src
          Pandoc.writeHtmlStringForEPUB EPUB3 writerOpts ast

    -- Render Markdown to LaTeX using Pandoc.
    --
    -- NOTE: Currently, all links are left broken.
    --
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

    -- Apply a template with some metadata.
    let applyAsTemplate :: FilePath -> Metadata -> Action Text
        applyAsTemplate inputFile metadata = do
          tpl <- getTemplate inputFile
          return $ Pandoc.renderTemplate tpl metadata

    -- Apply a template with metadata to some content.
    let applyTemplate :: FilePath -> Metadata -> Text -> Action Text
        applyTemplate inputFile metadata body =
          applyAsTemplate inputFile (metadata & "body" .~ body)


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
          let urlField    = mempty & "url" .~ ("/" </> postMdFile -<.> "html")
          return $ mconcat [metadata, bodyField, dateField, teaserField, urlField]
      --
      -- NOTE: The posts are read in the order provided by the file system which,
      --       due to the naming convention, is oldest-first. Rather than sorting
      --       by date recent-first, we can therefore simply reverse the list.
      --
      return $ mempty & "post" .~ reverse posts

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
        htmlStage3 src = normalise $ routeFile siteDir routingTable src

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
          let depends = [ resolveDepend dep | dep <- libDepends agdaLib ]
          let libraries = [ htmlStage1Lib lib | lib <- agdaLib : depends ]
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
          >>= applyTemplate (templateDir </> "page.html") metadata
          >>= applyTemplate (templateDir </> "default.html") metadata
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
