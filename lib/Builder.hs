import Control.Monad (forM, forM_, when)
import Data.Function (on)
import Data.Functor ((<&>))
import Data.List (sortBy)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromMaybe)
import Data.Text qualified as T
import Debug.Trace (traceShow)
import PLFA.Build.Agda
import PLFA.Build.Gather
import PLFA.Build.Metadata
import PLFA.Build.Pandoc as Pandoc
import PLFA.Build.Prelude
import PLFA.Build.Preprocess
import PLFA.Build.Route hiding (routeFile, routeUrl)
import PLFA.Build.Route qualified as Route (routeFile, routeUrl)
import PLFA.Build.Style.CSS
import PLFA.Build.Style.Sass


--------------------------------------------------------------------------------
-- Directories
--------------------------------------------------------------------------------

authorDir         = "authors"
bookDir           = "book"
cacheDir          = "_build"
contributorDir    = "contributors"
courseDir         = "courses"
cssDir            = "css"
epubCacheDir      = cacheDir </> "epub"
htmlCacheDir      = cacheDir </> "html"
htmlStage1Dir     = htmlCacheDir </> "stage1"
htmlStage2Dir     = htmlCacheDir </> "stage2"
postsDir          = "posts"
publicDir         = "public"
siteDir           = "_site"
stdlibDir         = "standard-library"
srcDir            = "src"
texCacheDir       = cacheDir </> "tex"
templateDir       = "templates"
fontsDir          = bookDir </> "fonts"
webfontsDir       = publicDir </> "webfonts"

bibtexFile        = "bib" </> "plfa.bib"
stdlibAgdaLibFile = stdlibDir </> "standard-library.agda-lib"

badgeUrl          = ""

main :: IO ()
main = do

  --------------------------------------------------------------------------------
  -- Gather input files and build routing table
  --------------------------------------------------------------------------------

  -- Gather files
  publicFiles           <- gather always regularFile [publicDir]
  coursePdfs            <- gather always (regularFile &&? extension ==? ".pdf") [courseDir]
  let staticFiles        = publicFiles <> coursePdfs
  agdaLibs              <- gatherAgdaLibs [courseDir, srcDir]
  stdlib                <- readStandardLibraryAgdaLib stdlibDir
  mdFiles               <- ("README.md" :) <$> gatherMdFiles [postsDir, srcDir]
  scssFiles             <- gatherSassFiles [cssDir]
  postMdFiles           <- gatherMdFiles [postsDir]
  lagdaMdFilesByAgdaLib <- gatherLagdaMdFilesForAgdaLibs agdaLibs
  webfontFiles          <- gather always (regularFile &&? extension ==? ".woff") [webfontsDir]
  fontFiles             <- gather always (regularFile &&? extension ==? ".ttf") [fontsDir]

  -- Build routing table
  permalinkRoutingTable <- buildPermalinkRoutingTable mdFiles
  let postsRoutingTable = asRoutingTable (-<.> "html") postMdFiles
  let staticRoutingTable = asRoutingTable id (staticFiles <> coursePdfs)
  let routingTable = mconcat [permalinkRoutingTable, postsRoutingTable, staticRoutingTable]
  let routeUrl  src = Route.routeUrl routingTable src
  let routeFile src = Route.routeFile siteDir routingTable src

  shakeArgs shakeOpts $ do

    -- Require Shake builds all targets in the routing table
    wantAllTargets siteDir routingTable

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

    -- Render Markdown to Html5 using Pandoc, applying the code to fix links
    -- to local and external modules.
    --
    -- NOTE: Every Agda file in a local module /must/ have a permalink attribute.
    --
    let markdownToHtml :: Text -> Action Text
        markdownToHtml src = do
          fixLinks <- getFixLinks ()
          runPandocIO $ do
            ast <- Pandoc.readMarkdown readerOpts src
            let ast' = withUrlsPandoc fixLinks ast
            Pandoc.writeHtml5String writerOpts ast'


    -- Render Markdown to LaTeX using Pandoc.
    let markdownToLaTeX :: Text -> Action Text
        markdownToLaTeX src = do
          runPandocIO $ do
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
          applyAsTemplate inputFile (constField "body" body <> metadata)


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
      publishedDate <- currentDateField "today"
      return $ mconcat [ metadata, publishedDate ]

    getFileMetadata <- newCache $ \inputFile -> do
      siteMetadata <- getSiteMetadata ()
      (body, frontmatterMetadata) <- readFileWithMetadata' inputFile
      lastModifiedMetadata <- lastModifiedField inputFile "modified_date"
      return $ mconcat
        [ siteMetadata,
          addTitleVariants frontmatterMetadata,
          lastModifiedMetadata,
          constField "source" inputFile,
          constField "body" body,
          constField "body_with_shifted_headers" (shiftHeaders body)
        ]

    let getTocMetadataWith :: (FilePath -> FilePath) -> Action Metadata
        getTocMetadataWith fileMap = do
          toc             <- readYamlFrontmatter' $ srcDir </> "toc.metadata"
          tocWithIncludes <- resolveIncludes (\inputFile -> getFileMetadata (fileMap inputFile)) toc
          authors         <- getAuthors ()
          contributors    <- getContributors()
          return $ mconcat [
            tocWithIncludes,
            constField "author" authors,
            constField "contributor" contributors
            ]

    getPostMetadata <- newCache $ \() -> do
      need postMdFiles
      posts <-
        forM postMdFiles $ \postMdFile -> do
          (body, metadata) <- readFileWithMetadata' postMdFile
          return $ mconcat [
            metadata,
            constField "body" body,
            constField "url"  ("/" <> routeUrl postMdFile),
            dateFromFileNameField postMdFile "date",
            teaserField body "teaser"
            ]
      --
      -- NOTE: The posts are read in the order provided by the file system which,
      --       due to the naming convention, is oldest-first. Rather than sorting
      --       by date recent-first, we can therefore simply reverse the list.
      --
      return $ constField "post" (reverse posts)

    --------------------------------------------------------------------------------
    -- Static files
    --
    -- All files in '$publicDir' are copied verbatim to '$siteDir', preserving
    -- their relative paths.
    --------------------------------------------------------------------------------

    forM_ staticFiles $ \src -> do
      routeFile src %> \out ->
        copyFile' src out

    --------------------------------------------------------------------------------
    -- Html compilation
    --
    -- Literate Agda files are rendered in stages:
    --
    --   Stage 1. Preprocessing. Literate code blocks are marked as raw Html or
    --            LaTeX by wrapping them in a code block with the appropriate raw
    --            attribute. For the LaTeX backend, the backtick fences are replaced
    --            by a LaTeX code environment.
    --
    --   Stage 2. Highlighting. Literate code blocks are highlighted using Agda.
    --
    --   Stage 3. Templating & Rendering. The relevant templates are applied, and
    --            the Markdown is rendered to Html and LaTeX using Pandoc.
    --
    -- Markdown files are copied verbatim to Stage 2 and pass through Stage 3.
    --
    --------------------------------------------------------------------------------

    let htmlStage1, htmlStage2, htmlStage3 :: FilePath -> FilePath
        htmlStage1 src = normalise $ htmlCacheDir </> "stage1" </> src
        htmlStage2 src = normalise $ htmlCacheDir </> "stage2" </> stripLagda src
        htmlStage3 src = normalise $ routeFile src
        stripLagda src
          | takeExtensions src == ".lagda.md" = replaceExtensions src "md"
          | otherwise                         = src

    -- Generate an appropriate libraries file
    htmlStage1 ".agda/libraries" %> \out -> do
      let libraries = [ libFile (mapAgdaLib htmlStage1 lib) | lib <- stdlib : agdaLibs ]
      need libraries
      writeFile' out (T.unlines (map T.pack libraries))

    getTocMetadataForHtml <- newCache $ \() -> do
      siteMetadata <- getSiteMetadata ()
      tocMetadata <- getTocMetadataWith htmlStage2
      return $ mconcat [siteMetadata, tocMetadata]

    -- Compile .lagda.md files in the context of their .agda-lib file
    forM_ lagdaMdFilesByAgdaLib $ \(agdaLib, lagdaMdFiles) -> do

      -- Copy over .agda-lib file
      libFile (mapAgdaLib htmlStage1 agdaLib) %> \out -> do
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
          let libraries = [ mapAgdaLib htmlStage1 lib | lib <- agdaLib : depends ]
          -- Need updated libraries file, .agda-lib files, and all .lagda.md files
          need [ htmlStage1 ".agda/libraries" ]
          need [ libFile lib | lib <- libraries]
          need [ htmlStage1 lagdaMdFile | lagdaMdFile <- lagdaMdFiles ]
          -- Highlight Agda as Html
          markdown <- highlightAgdaFor (htmlStage1 ".agda/libraries") libraries (htmlStage1 src) Markdown
          writeFile' out markdown
          putInfo $ "Checked " <> src

    forM_ mdFiles $ \src -> do

      when (takeExtensions src /= ".lagda.md") $ do

        -- Stage 2: Copy Markdown files verbatim
        htmlStage2 src %> \out -> do
          need [src]
          copyFile' src out

      -- Stage 3: Render the Markdown to Html
      htmlStage3 src %> \out -> do
        need [htmlStage2 src]
        fileMetadata <- getFileMetadata src
        tocMetadata  <- getTocMetadataForHtml ()
        postMetadata <- getPostMetadata ()
        let metadata = mconcat [fileMetadata, tocMetadata, postMetadata]
        applyAsTemplate (htmlStage2 src) metadata
          >>= markdownToHtml
          >>= applyTemplate (templateDir </> "page.html") metadata
          >>= applyTemplate (templateDir </> "default.html") metadata
          <&> withUrls (relativizeUrl {-w.r.t.-} (routeUrl src))
          <&> postprocessHtml5 -- TODO: Pandoc generates incorrect HTML5
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
    -- Compile EPUB
    --------------------------------------------------------------------------------

    let epubFile     = bookDir </> "epub.md"
    let epubMetaYaml = bookDir </> "epub.meta.yaml"
    let epubMetaXml  = bookDir </> "epub.xml"
    let plfaEpub     = siteDir </> "plfa.epub"

    want [plfaEpub]

    htmlStage2 epubFile %> \out -> do
      tocMetadata <- getTocMetadataForHtml ()
      epub <- applyAsTemplate epubFile tocMetadata
      writeFile' out (sanitizeForEpub epub)

    htmlStage2 epubMetaXml %> \out -> do
      siteMetadata <- getSiteMetadata ()
      epubMeta <- applyAsTemplate epubMetaXml siteMetadata
      writeFile' out epubMeta

    buildEpubMeta <- newCache $ \() -> do
      authors      <- map authorName <$> getAuthors ()
      metadata     <- getSiteMetadata ()
      date         <- metadata ^. "today" :: Action Text
      site         <- metadata ^. "site"  :: Action Metadata
      title        <- site ^. "title"     :: Action Text
      license      <- site ^. "license"   :: Action Metadata
      licenseName  <- license ^. "name"   :: Action Text
      return $ mconcat
        [ constField "pagetitle" title,
          constField "title" title,
          constField "date" date,
          constField "authors" authors,
          constField "rights" licenseName
        ]

    htmlStage2 epubMetaYaml %> \out -> do
      epubMeta <- buildEpubMeta ()
      writeYaml' out epubMeta

    plfaEpub %> \out -> do
      need [htmlStage2 file | file <- [ epubFile, epubMetaXml, epubMetaYaml ] ]
      liftIO $ convertWithOpts defaultOpts
        { optFrom             = Just markdownFormat,
          optTo               = Just "epub2",
          optTableOfContents  = True,
          optMetadataFiles    = [htmlStage2 epubMetaYaml],
          optInputFiles       = Just [htmlStage2 epubFile],
          optOutputFile       = Just out,
          optTopLevelDivision = TopLevelPart,
          optEpubMetadata     = Just (htmlStage2 epubMetaXml),
          optEpubFonts        = webfontFiles,
          optEpubChapterLevel = 2,
          optTOCDepth         = 2,
          optFilters          = [LuaFilter $ bookDir </> "lua" </> "remove-badges.lua",
                                 LuaFilter $ bookDir </> "lua" </> "epub-clean-html.lua",
                                 LuaFilter $ bookDir </> "lua" </> "single-file-links.lua"],
          optCss              = [bookDir </> "epub.css"],
          optStripComments    = True
        }

    --------------------------------------------------------------------------------
    -- Compile PDF
    --------------------------------------------------------------------------------

{-

    let texStage1, texStage2 :: FilePath -> FilePath
        texStage1 src = normalise $ texCacheDir </> "stage1" </> src
        texStage2 src = normalise $ texCacheDir </> "stage2" </> stripLagda src
        texStage3 src = normalise $ texCacheDir </> "stage3" </> src -<.> "tex"

    getTocMetadataForLaTeX <- newCache $ \() -> do
      siteMetadata <- getSiteMetadata ()
      tocMetadata <- getTocMetadataWith texStage3
      putInfo $ show tocMetadata
      return $ mconcat [siteMetadata, tocMetadata]

    -- Generate an appropriate libraries file
    texStage1 ".agda/libraries" %> \out -> do
      let libraries = [ libFile (mapAgdaLib texStage1 lib) | lib <- stdlib : agdaLibs ]
      need libraries
      writeFile' out (T.unlines (map T.pack libraries))

    -- Compile .lagda.md files in the context of their .agda-lib file
    forM_ lagdaMdFilesByAgdaLib $ \(agdaLib, lagdaMdFiles) -> do

      -- Copy over .agda-lib file
      libFile (mapAgdaLib texStage1 agdaLib) %> \out -> do
        let src = libFile agdaLib
        need [src]
        copyFile' src out

      forM_ lagdaMdFiles $ \src -> do

        -- Stage 1: Preprocess literate Agda files
        texStage1 src %> \out -> do
          need [src]
          readFile' src
            <&> preprocessForLaTeX
            >>= writeFile' out

        -- Stage 2: Highlight literate Agda files
        texStage2 src %> \out -> do
          -- Update file paths in library files
          let depends = [ resolveDepend dep | dep <- libDepends agdaLib ]
          let libraries = [ mapAgdaLib texStage1 lib | lib <- agdaLib : depends ]
          -- Need updated libraries file, .agda-lib files, and all .lagda.md files
          need [ texStage1 ".agda/libraries" ]
          need [ libFile lib | lib <- libraries]
          need [ texStage1 lagdaMdFile | lagdaMdFile <- lagdaMdFiles ]
          -- Highlight Agda as LaTeX
          markdown <- highlightAgdaFor (htmlStage1 ".agda/libraries") libraries (htmlStage1 src) LaTeX
          writeFile' out markdown
          putInfo $ "Checked " <> src

    forM_ mdFiles $ \src -> do

      when (takeExtensions src /= ".lagda.md") $ do

        -- Stage 2: Copy Markdown files verbatim
        texStage2 src %> \out -> do
          need [src]
          copyFile' src out

      -- Stage 3: Render Markdown as LaTeX
      texStage3 src %> \out -> do
        need [texStage2 src]
        fileMetadata <- getFileMetadata src
        tocMetadata  <- getTocMetadataForLaTeX ()
        let metadata = mconcat [fileMetadata, tocMetadata]
        applyAsTemplate (texStage2 src) metadata
          <&> sanitizeForEpub
          >>= markdownToLaTeX
          >>= writeFile' out
        putInfo $ "Updated " <> src

    let pdfFile = bookDir </> "pdf.tex"
    let plfaPdf = siteDir </> "plfa.pdf"

    want [ texStage3 pdfFile ]
    want [ texStage3 mdFile | mdFile <- mdFiles ]

    texStage3 pdfFile %> \out -> do
      tocMetadata <- getTocMetadataForLaTeX ()
      tex <- applyAsTemplate pdfFile tocMetadata
      writeFile' out tex

-- -}

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
      , Ext_auto_identifiers
      , Ext_backtick_code_blocks
      , Ext_citations
      , Ext_footnotes
      , Ext_header_attributes
      , Ext_intraword_underscores
      , Ext_markdown_in_html_blocks
      , Ext_shortcut_reference_links
      , Ext_smart
      , Ext_superscript
      , Ext_subscript
      , Ext_task_lists
      , Ext_yaml_metadata_block
      , Ext_raw_html
      , Ext_raw_attribute
      , Ext_fenced_code_blocks
      , Ext_backtick_code_blocks
      ]
  }

-- TODO: there must be some way to recover this from the 'readerExtensions' above
markdownFormat :: Text
markdownFormat = "markdown_strict+all_symbols_escapable+auto_identifiers+backtick_code_blocks+citations+footnotes+header_attributes+intraword_underscores+markdown_in_html_blocks+shortcut_reference_links+smart+superscript+subscript+task_lists+yaml_metadata_block+raw_html+raw_attribute+fenced_code_blocks+backtick_code_blocks"

writerOpts :: WriterOptions
writerOpts = def
