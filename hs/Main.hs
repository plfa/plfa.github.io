{-# LANGUAGE OverloadedStrings #-}

import           Control.Monad ((<=<), forM_)
import qualified Data.ByteString.Lazy as BL
import           Data.Functor ((<&>))
import qualified Data.Text as T
import           Hakyll
import           Hakyll.Web.Agda
import           Hakyll.Web.Routes.Permalink
import           Hakyll.Web.Template.Numeric
import           Hakyll.Web.Template.Context.Metadata
import           Hakyll.Web.Template.Context.Title
import           Hakyll.Web.Sass
import           System.FilePath ((</>), takeDirectory)
import qualified Text.CSL as CSL
import qualified Text.CSL.Pandoc as CSL (processCites)
import           Text.Pandoc (Pandoc(..), ReaderOptions(..), WriterOptions(..), Extension(..))
import qualified Text.Pandoc as Pandoc
import qualified Text.Pandoc.Filter as Pandoc (Filter(..),  applyFilters)

--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------

siteReaderOptions :: ReaderOptions
siteReaderOptions = defaultHakyllReaderOptions
  { readerExtensions = Pandoc.extensionsFromList
    [ Ext_all_symbols_escapable
    , Ext_auto_identifiers
    , Ext_backtick_code_blocks
    , Ext_citations
    , Ext_footnotes
    , Ext_header_attributes
    , Ext_implicit_header_references
    , Ext_intraword_underscores
    , Ext_markdown_in_html_blocks
    , Ext_raw_html
    , Ext_shortcut_reference_links
    , Ext_smart
    , Ext_superscript
    , Ext_subscript
    , Ext_task_lists
    , Ext_yaml_metadata_block
    ]
  }

siteWriterOptions :: WriterOptions
siteWriterOptions = defaultHakyllWriterOptions

siteContext :: Context String
siteContext = mconcat
  [ constField "pagetitle" "Programming Language Foundations in Agda"
  , constField "pageurl" "https://plfa.github.io"
  , constField "description" "An introduction to programming language theory using the proof assistant Agda."
  , constField "language" "en-US"
  , constField "rights" "Creative Commons Attribution 4.0 International License"
  , constField "rights_url" "https://creativecommons.org/licenses/by/4.0/"
  , constField "repository" "plfa/plfa.github.io"
  , constField "branch" "dev"
  , modificationTimeField "modified" "%0Y-%m-%dT%H:%M:%SZ"
  , field "source" (return . toFilePath . itemIdentifier)
  , listField "authors" defaultContext $ mapM load
      [ "authors/wadler.metadata"
      , "authors/wenkokke.metadata"
      , "authors/jsiek.metadata"
      ]
  , constField "google_analytics" "UA-125055580-1"
  , defaultContext
  ]

siteSectionContext :: Context String
siteSectionContext = mconcat
  [ titlerunningField
  , subtitleField
  , siteContext
  ]

tableOfContentsContext :: Context String -> Context String
tableOfContentsContext ctx = Context $ \k a _ -> do
  m <- makeItem <=< getMetadata $ "src/plfa/toc.metadata"
  unContext (objectContext ctx) k a m

acknowledgementsContext :: Context String
acknowledgementsContext = mconcat
  [ listField "contributors" defaultContext $
      byNumericFieldDesc "count" =<< loadAll "contributors/*.metadata"
  , siteContext
  ]

postContext :: Context String
postContext = mconcat
  [ dateField "date" "%B %e, %Y"
  , siteContext
  ]

postListContext :: Context String
postListContext = mconcat
  [ listField "posts" postItemContext $
      recentFirst =<< loadAll "posts/*"
  , siteContext
  ]
  where
    postItemContext :: Context String
    postItemContext = mconcat
      [ teaserField "teaser" "content"
      , contentField "content" "content"
      , postContext
      ]

agdaStdlibPath :: FilePath
agdaStdlibPath = "standard-library"

agdaOptions :: CommandLineOptions
agdaOptions = defaultAgdaOptions
  { optUseLibs       = False
  , optIncludePaths  = [agdaStdlibPath </> "src", "src"]
  , optPragmaOptions = defaultAgdaPragmaOptions
    { optVerbose     = agdaVerbosityQuiet
    }
  }

sassOptions :: SassOptions
sassOptions = defaultSassOptions
  { sassIncludePaths = Just ["css"]
  }

epubSectionContext :: Context String
epubSectionContext = mconcat
  [ contentField "content" "content"
  , titlerunningField
  , subtitleField
  ]

epubReaderOptions :: ReaderOptions
epubReaderOptions = siteReaderOptions
  { readerStandalone    = True
  , readerStripComments = True
  }

epubWriterOptions :: WriterOptions
epubWriterOptions = siteWriterOptions
  { writerTableOfContents  = True
  , writerTOCDepth         = 2
  , writerEpubFonts        = [ "public/webfonts/DejaVuSansMono.woff"
                             , "public/webfonts/FreeMono.woff"
                             , "public/webfonts/mononoki.woff"
                             ]
  , writerEpubChapterLevel = 2
  }

--------------------------------------------------------------------------------
-- Build site
--------------------------------------------------------------------------------

main :: IO ()
main = do

  let cslFileName = "csl/iso690-author-date-en.csl"
  let bibFileName = "bib/plfa.bib"

  -- Build function to fix standard library URLs
  fixStdlibLink <- mkFixStdlibLink agdaStdlibPath

  -- Build function to fix local URLs
  fixLocalLink <- mkFixLocalLink "src"

  -- Build compiler for Markdown pages
  let pageCompiler :: Compiler (Item String)
      pageCompiler = do
        csl <- load cslFileName
        bib <- load bibFileName
        getResourceBody
          >>= readMarkdownWith siteReaderOptions
          >>= processCites csl bib
          <&> writeHTML5With siteWriterOptions
          >>= saveSnapshot "content"
          >>= loadAndApplyTemplate "templates/page.html"    siteSectionContext
          >>= loadAndApplyTemplate "templates/default.html" siteSectionContext
          >>= prettifyUrls

  -- Build compiler for literate Agda pages
  let pageWithAgdaCompiler :: CommandLineOptions -> Compiler (Item String)
      pageWithAgdaCompiler opts = do
        csl <- load cslFileName
        bib <- load bibFileName
        agdaCompilerWith opts
          >>= withItemBody (return . withUrls fixStdlibLink)
          >>= withItemBody (return . withUrls fixLocalLink)
          >>= readMarkdownWith siteReaderOptions
          >>= processCites csl bib
          <&> writeHTML5With siteWriterOptions
          >>= saveSnapshot "content"
          >>= loadAndApplyTemplate "templates/page.html"    siteSectionContext
          >>= loadAndApplyTemplate "templates/default.html" siteSectionContext
          >>= prettifyUrls

  -- Run Hakyll
  --
  -- NOTE: The order of the various match expressions is important:
  --       Special-case compilation instructions for files such as
  --       "src/plfa/epub.md" and "src/plfa/index.md" would be overwritten
  --       by the general purpose compilers for "src/**.md", which would
  --       cause them to render incorrectly. It is possible to explicitly
  --       exclude such files using `complement` patterns, but this vastly
  --       complicates the match patterns.
  --
  hakyll $ do

    -- Compile EPUB
    match "src/plfa/epub.md" $ do
      route $ constRoute "plfa.epub"
      compile $ do
        epubTemplate <- load "templates/epub.html"
            >>= compilePandocTemplate
        epubMetadata <- load "src/plfa/epub.xml"
        let ropt = epubReaderOptions
        let wopt = epubWriterOptions
              { writerTemplate     = Just . itemBody $ epubTemplate
              , writerEpubMetadata = Just . T.pack . itemBody $ epubMetadata
              }
        getResourceBody
          >>= applyAsTemplate (tableOfContentsContext epubSectionContext)
          >>= readPandocWith ropt
          >>= applyPandocFilters ropt [] "epub3"
          >>= writeEPUB3With wopt

    match "templates/epub.html" $
      compile $ getResourceBody
        >>= applyAsTemplate siteContext

    match "src/plfa/epub.xml" $
      compile $ getResourceBody
        >>= applyAsTemplate siteContext

    -- Compile Table of Contents
    match "src/plfa/index.md" $ do
      route permalinkRoute
      compile $ getResourceBody
        >>= applyAsTemplate (tableOfContentsContext siteSectionContext)
        >>= readMarkdownWith siteReaderOptions
        <&> writeHTML5With siteWriterOptions
        >>= loadAndApplyTemplate "templates/page.html"    siteContext
        >>= loadAndApplyTemplate "templates/default.html" siteContext
        >>= prettifyUrls

    match "src/**.metadata" $
      compile getResourceBody

    -- Compile Acknowledgements
    match "src/plfa/backmatter/acknowledgements.md" $ do
      route permalinkRoute
      compile $ getResourceBody
        >>= applyAsTemplate acknowledgementsContext
        >>= readMarkdownWith siteReaderOptions
        <&> writeHTML5With siteWriterOptions
        >>= saveSnapshot "content"
        >>= loadAndApplyTemplate "templates/page.html"    siteContext
        >>= loadAndApplyTemplate "templates/default.html" siteContext
        >>= prettifyUrls
    
    match "src/plfa/backmatter/acknowledgements.md" $ version "raw" $ do
      route $ constRoute "acknowledgements.md"
      compile $ getResourceBody
        >>= applyAsTemplate acknowledgementsContext

    match "authors/*.metadata" $
      compile getResourceBody

    match "contributors/*.metadata" $
      compile getResourceBody

    -- Compile Announcements
    match "src/pages/announcements.html" $ do
      route permalinkRoute
      compile $ getResourceBody
        >>= applyAsTemplate postListContext
        >>= loadAndApplyTemplate "templates/page.html"      siteContext
        >>= loadAndApplyTemplate "templates/default.html"   siteContext
        >>= prettifyUrls

    match "posts/*" $ do
      route $ setExtension "html"
      compile $ do
        csl <- load cslFileName
        bib <- load bibFileName
        getResourceBody
          >>= readMarkdownWith siteReaderOptions
          >>= processCites csl bib
          <&> writeHTML5With siteWriterOptions
          >>= saveSnapshot "content"
          >>= loadAndApplyTemplate "templates/post.html"    postContext
          >>= loadAndApplyTemplate "templates/default.html" siteContext
          >>= prettifyUrls

    -- Compile sections using literate Agda
    match "src/**.lagda.md" $ do
      route permalinkRoute
      compile $ pageWithAgdaCompiler agdaOptions

    -- Compile other sections and pages
    match ("README.md" .||. "src/**.md" .&&. complement "src/plfa/epub.md") $ do
      route permalinkRoute
      compile pageCompiler

    -- Compile course pages
    match "courses/**.lagda.md" $ do
      route permalinkRoute
      compile $ do
        courseDir <- takeDirectory . toFilePath <$> getUnderlying
        let courseOptions = agdaOptions
              { optIncludePaths = courseDir : optIncludePaths agdaOptions
              }
        pageWithAgdaCompiler courseOptions

    match "courses/**.md" $ do
      route permalinkRoute
      compile pageCompiler

    match "courses/**.pdf" $ do
      route idRoute
      compile copyFileCompiler

    -- Compile 404 page
    match "404.html" $ do
      route idRoute
      compile $ getResourceBody
        >>= loadAndApplyTemplate "templates/default.html" siteContext

    -- Compile templates
    match "templates/*" $ compile templateBodyCompiler

    -- Compile CSL and BibTeX files
    match "csl/*.csl" $ compile cslCompiler
    match "bib/*.bib" $ compile biblioCompiler

    -- Copy resources
    match "public/**" $ do
      route idRoute
      compile copyFileCompiler

    -- Compile CSS
    match "css/*.css" $ compile compressCssCompiler

    scss <- makePatternDependency "css/minima/**.scss"
    rulesExtraDependencies [scss] $
      match "css/minima.scss" $
        compile $ sassCompilerWith sassOptions

    create ["public/css/style.css"] $ do
      route idRoute
      compile $ do
        csses <- loadAll ("css/*.css" .||. "css/*.scss" .&&. complement "css/epub.css")
        makeItem $ unlines $ map itemBody csses

    -- Copy versions
    let versions = ["19.08", "20.07"]
    forM_ versions $ \v -> do

      -- Relativise URLs in HTML files
      match (fromGlob $ "versions" </> v </> "**.html") $ do
        route $ gsubRoute "versions/" (const "")
        compile $ getResourceBody
          >>= prettifyUrls

      -- Copy other files
      match (fromGlob $ "versions" </> v </> "**") $ do
        route $ gsubRoute "versions/" (const "")
        compile copyFileCompiler


--------------------------------------------------------------------------------
-- Custom readers and writers
--------------------------------------------------------------------------------

-- | Read a Markdown string using Pandoc, with the supplied options.
readMarkdownWith :: ReaderOptions           -- ^ Parser options
                 -> Item String             -- ^ String to read
                 -> Compiler (Item Pandoc)  -- ^ Resulting document
readMarkdownWith ropt item =
  case Pandoc.runPure $ traverse (Pandoc.readMarkdown ropt) (fmap T.pack item) of
    Left err    -> fail $
      "Hakyll.Web.Pandoc.readPandocWith: parse failed: " ++ show err
    Right item' -> return item'

-- | Process citations in a Pandoc document.
processCites :: Item CSL -> Item Biblio -> Item Pandoc -> Compiler (Item Pandoc)
processCites csl bib item = do
    -- Parse CSL file, if given
    style <- unsafeCompiler $ CSL.readCSLFile Nothing . toFilePath . itemIdentifier $ csl

    -- We need to know the citation keys, add then *before* actually parsing the
    -- actual page. If we don't do this, pandoc won't even consider them
    -- citations!
    let Biblio refs = itemBody bib
    withItemBody (return . CSL.processCites style refs) item

-- | Write a document as HTML using Pandoc, with the supplied options.
writeHTML5With :: WriterOptions  -- ^ Writer options for pandoc
               -> Item Pandoc    -- ^ Document to write
               -> Item String    -- ^ Resulting HTML
writeHTML5With wopt (Item itemi doc) =
  case Pandoc.runPure $ Pandoc.writeHtml5String wopt doc of
    Left err    -> error $ "Hakyll.Web.Pandoc.writePandocWith: " ++ show err
    Right item' -> Item itemi $ T.unpack item'

-- | Write a document as EPUB3 using Pandoc, with the supplied options.
writeEPUB3With :: WriterOptions -> Item Pandoc -> Compiler (Item BL.ByteString)
writeEPUB3With wopt (Item itemi doc) =
  return $ case Pandoc.runPure $ Pandoc.writeEPUB3 wopt doc of
    Left  err  -> error $ "Hakyll.Web.Pandoc.writeEPUB3With: " ++ show err
    Right doc' -> Item itemi doc'

-- | Apply a filter to a Pandoc document.
applyPandocFilters :: ReaderOptions -> [Pandoc.Filter] -> String -> Item Pandoc -> Compiler (Item Pandoc)
applyPandocFilters ropt filters fmt = withItemBody $
  unsafeCompiler . Pandoc.runIOorExplode . Pandoc.applyFilters ropt filters [fmt]

-- | Compile a Pandoc template (as opposed to a Hakyll template).
compilePandocTemplate :: Item String -> Compiler (Item (Pandoc.Template T.Text))
compilePandocTemplate i = do
  let templatePath = toFilePath $ itemIdentifier i
  let templateBody = T.pack $ itemBody i
  templateOrError <- unsafeCompiler $ Pandoc.compileTemplate templatePath templateBody
  template <- either fail return templateOrError
  makeItem template


--------------------------------------------------------------------------------
-- Supply snapshot as a field to the template
--------------------------------------------------------------------------------

contentField :: String -> Snapshot -> Context String
contentField key snapshot = field key $ \item ->
  itemBody <$> loadSnapshot (itemIdentifier item) snapshot

--------------------------------------------------------------------------------
-- Relativise URLs and strip "index.html" suffixes
--------------------------------------------------------------------------------

prettifyUrls :: Item String -> Compiler (Item String)
prettifyUrls = relativizeUrls <=< withItemBody (return . stripIndexFile)
