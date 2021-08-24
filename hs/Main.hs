{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}

import           Control.Monad ((<=<), forM_)
import qualified Data.ByteString.Char8 as BS
import           Data.Char (toLower)
import           Data.Functor ((<&>))
import           Data.List (isPrefixOf, stripPrefix)
import qualified Data.Text as T
import qualified Data.Yaml as Y
import           Hakyll
import           Hakyll.Web.Agda
import           Hakyll.Web.Routes.Permalink
import           Hakyll.Web.Template.Numeric
import           Hakyll.Web.Template.Context.Derived
import           Hakyll.Web.Template.Context.Metadata
import           Hakyll.Web.Template.Context.Title
import           Hakyll.Web.Sass
import           System.FilePath ((</>), takeDirectory, replaceExtensions, splitPath, joinPath)
import qualified Text.CSL as CSL
import qualified Text.CSL.Pandoc as CSL (processCites)
import           Text.Pandoc (Pandoc(..), ReaderOptions(..), WriterOptions(..), Extension(..))
import qualified Text.Pandoc as Pandoc
import           Text.Pandoc.Definition (Block(..))
import           Text.Pandoc.Walk (walk)
import           Text.Printf

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
  , addAnchor defaultContext
  ]

siteSectionContext :: Context String
siteSectionContext = mconcat
  [ titlerunningField
  , subtitleField
  , siteContext
  ]

tableOfContentsContext :: Context String -> Context String
tableOfContentsContext ctx = Context $ \k a _ ->
  unContext (objectContext ctx) k a
    =<< makeItem
    =<< getMetadata "src/plfa/toc.metadata"

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


-- Convert MD_DIR/%.md to LAGDA_TEX_DIR/%.lagda.tex or TEX_DIR/%.tex
--
-- NOTE: This logic is partially duplicated in book/pdf.mk:TEX_PATH.
--
-- NOTE: This function assumes pdf.tex will be at TEX_DIR/.
--
addTexPath :: Context a -> Context a
addTexPath = addDerivedField "tex_path" deriveTexPath
  where
    deriveTexPath :: Context a -> [String] -> Item a -> Compiler ContextField
    deriveTexPath ctx a i = do
      fld <- unContext ctx "include" a i
      case fld of
        StringField includePath -> return $ StringField (texPath includePath)
        _ -> fail "Key 'include' does not return a String"

    texPath :: FilePath -> FilePath
    texPath fnDotMd
      | fnDotMd == "README.md"                         = "plfa/frontmatter/README.tex"
      | any (`isPrefixOf` fnDotMd) ["src/", "book/"] = dropTopDirectory (replaceExtensions fnDotMd ".tex")
      | otherwise                                      = error ("textPath: cannot map " <> fnDotMd)

    dropTopDirectory :: FilePath -> FilePath
    dropTopDirectory = joinPath . tail . splitPath

-- Add an anchor based on the permalink, to be used as the header id.
addAnchor :: Context a -> Context a
addAnchor = addDerivedField "anchor" deriveAnchor
  where
    deriveAnchor :: Context a -> [String] -> Item a -> Compiler ContextField
    deriveAnchor ctx a i = do
      fld <- unContext ctx "permalink" a i
      case fld of
        StringField permalink -> StringField <$> anchor permalink
        _ -> fail "Key 'permalink' does not return a String"

    anchor :: String -> Compiler String
    anchor permalink =
      let maybeAnchor = map toLower <$> (stripSuffix "/" <=< stripPrefix "/") permalink
      in maybe (fail $ printf "Key 'permalink' malformed '%s'" permalink) return maybeAnchor

    stripSuffix :: String -> String -> Maybe String
    stripSuffix suf str = reverse <$> stripPrefix (reverse suf) (reverse str)

-- Add the metadata back to the file as a Yaml header.
addMetadata :: Item String -> Compiler (Item String)
addMetadata item = do
  metadata <- getMetadata (itemIdentifier item)
  let yaml = "---\n" <> BS.unpack (Y.encode metadata) <> "---\n\n"
  withItemBody (\body -> return (yaml <> body)) item



-- Shift all headers by a given value.
shiftHeadersBy :: Int -> Pandoc -> Pandoc
shiftHeadersBy n = walk shiftHeader
  where
    shiftHeader :: Block -> Block
    shiftHeader (Header level attr inlines) = Header (level + n) attr inlines
    shiftHeader block = block

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
          >>= loadAndApplyTemplate "templates/page.html" siteSectionContext
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
          >>= loadAndApplyTemplate "templates/page.html" siteSectionContext
          >>= loadAndApplyTemplate "templates/default.html" siteSectionContext
          >>= prettifyUrls

  -- Run Hakyll
  --
  -- NOTE: The order of the various match expressions is important:
  --       Special-case compilation instructions for files such as
  --       "src/plfa/index.md" would be overwritten by the general
  --       purpose compilers for "src/**.md", which would
  --       cause them to render incorrectly. It is possible to explicitly
  --       exclude such files using `complement` patterns, but this vastly
  --       complicates the match patterns.
  --
  hakyll $ do

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
        >>= loadAndApplyTemplate "templates/page.html"    siteContext
        >>= loadAndApplyTemplate "templates/default.html" siteContext
        >>= prettifyUrls

    -- Compile raw version of acknowledgements used in constructing the PDF and EPUB
    match "src/plfa/backmatter/acknowledgements.md" $ version "raw" $ do
      route $ gsubRoute "src/" (const "raw/")
      compile $ getResourceBody
        >>= applyAsTemplate acknowledgementsContext
        >>= addMetadata

    -- Compile raw version of index used in constructing the PDF
    match "book/pdf.tex" $ do
      route $ gsubRoute "book/" (const "raw/")
      compile $ getResourceBody
        >>= applyAsTemplate (addTexPath (tableOfContentsContext siteSectionContext))

    -- Compile raw version of index used in constructing the EPUB
    match "book/epub.md" $ do
      route $ gsubRoute "book/" (const "raw/")
      compile $ getResourceBody
        >>= applyAsTemplate (tableOfContentsContext siteSectionContext)

    -- Compile metadata XML used in constructing the EPUB
    match "book/epub.xml" $ version "raw" $ do
      route   $ constRoute "raw/epub.xml"
      compile $ getResourceBody
        >>= applyAsTemplate siteContext

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
    match ("README.md" .||. "src/**.md") $ do
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
        csses <- loadAll ("css/*.css" .||. "css/*.scss")
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
writeHTML5With :: WriterOptions  -- ^ Writer options for Pandoc
               -> Item Pandoc    -- ^ Document to write
               -> Item String    -- ^ Resulting HTML
writeHTML5With wopt (Item itemi doc) =
  case Pandoc.runPure $ Pandoc.writeHtml5String wopt doc of
    Left err    -> error $ "Hakyll.Web.Pandoc.writePandocWith: " ++ show err
    Right item' -> Item itemi $ T.unpack item'


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
