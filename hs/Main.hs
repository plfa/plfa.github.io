{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

import           Control.Monad ((<=<), forM, forM_)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import           Data.Frontmatter (parseYamlFrontmatterEither)
import           Data.Functor ((<&>))
import           Data.List.Extra (stripInfix)
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)
import           Data.Yaml (FromJSON(..), ToJSON(..), (.:), (.=))
import qualified Data.Yaml as Y
import           Hakyll
import           Hakyll.Web.Agda
import           Hakyll.Web.Template.Context.Metadata
import           Hakyll.Web.Sass
import           Hakyll.Web.Routes.Permalink
import           System.Exit (exitFailure)
import           System.FilePath ((</>), takeDirectory)
import           System.FilePath.Find ((~~?), always, fileName, find)
import           Text.Pandoc
import           Text.Pandoc.Filter
import           Text.Printf (printf)

--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------

tocContext :: Context String
tocContext = Context $ \k a _ -> do
  unContext (objectContext defaultContext) k a <=< makeItem <=< getMetadata $ "toc.metadata"

siteContext :: Context String
siteContext = mconcat
  [ constField "site_title" "Programming Foundations in Agda"
  , constField "site_url" "https://plfa.github.io"
  , constField "license" "Creative Commons Attribution 4.0 International License"
  , constField "license_url" "https://creativecommons.org/licenses/by/4.0/"
  , constField "repository" "plfa/plfa.github.io"
  , constField "branch" "dev"
  , field "source" (return . toFilePath . itemIdentifier)
  , listField "authors" defaultContext (loadAll "authors/*.metadata")
  , constField "google_analytics" "UA-125055580-1"
  , defaultContext
  ]

acknowledgementsContext :: Context String
acknowledgementsContext = mconcat
  [ listField "contributors" defaultContext (loadAll "contributors/*.metadata")
  , siteContext
  ]

postContext :: Context String
postContext = mconcat
  [ dateField "date" "%B %e, %Y"
  , siteContext
  ]

postListContext :: Context String
postListContext = mconcat
  [ listField "posts" postItemContext (recentFirst =<< loadAll "posts/*")
  , siteContext
  ]
  where
    postItemContext :: Context String
    postItemContext = mconcat
      [ teaserField "teaser" "content"
      , contentField "content" "content"
      , postContext
      ]
    contentField :: String -> Snapshot -> Context String
    contentField key snapshot = field key $ \item ->
      itemBody <$> loadSnapshot (itemIdentifier item) snapshot

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

epubReaderOptions :: ReaderOptions
epubReaderOptions = defaultHakyllReaderOptions
  { readerStandalone    = True
  , readerStripComments = True
  }

epubWriterOptions :: WriterOptions
epubWriterOptions = def
  { writerTableOfContents  = True
  , writerTOCDepth         = 2
  , writerEpubFonts        = [ "public/webfonts/mononoki.woff" ]
  , writerEpubChapterLevel = 2
  }

epubFilters :: [Filter]
epubFilters =
  [ LuaFilter "epub/include-files.lua"
  , LuaFilter "epub/rewrite-links.lua"
  , LuaFilter "epub/rewrite-html-ul.lua"
  , LuaFilter "epub/default-code-class.lua"
  ]

applyPandocFilters :: ReaderOptions -> [Filter] -> [String] -> Item Pandoc -> Compiler (Item Pandoc)
applyPandocFilters ropt filters args = withItemBody $ \doc ->
  unsafeCompiler $ runIOorExplode $ applyFilters ropt filters args doc

writeEPUB3With :: WriterOptions -> Item Pandoc -> Item BL.ByteString
writeEPUB3With wopt (Item itemi doc) =
  case runPure $ writeEPUB3 wopt doc of
    Left  err  -> error $ "Hakyll.Web.Pandoc.writeEPUB3With: " ++ show err
    Right doc' -> Item itemi doc'

--------------------------------------------------------------------------------
-- Build site
--------------------------------------------------------------------------------

main :: IO ()
main = do

  -- Build function to fix standard library URLs
  fixStdlibLink <- mkFixStdlibLink agdaStdlibPath

  -- Build function to fix local URLs
  fixLocalLink <- mkFixLocalLink "src"

  let pageCompiler :: Compiler (Item String)
      pageCompiler = pandocCompiler
        >>= saveSnapshot "content"
        >>= loadAndApplyTemplate "templates/page.html"    siteContext
        >>= loadAndApplyTemplate "templates/default.html" siteContext
        >>= relativizeUrls

  let pageWithAgdaCompiler :: CommandLineOptions -> Compiler (Item String)
      pageWithAgdaCompiler opts = agdaCompilerWith opts
        >>= withItemBody (return . withUrls fixStdlibLink)
        >>= withItemBody (return . withUrls fixLocalLink)
        >>= renderPandoc
        >>= saveSnapshot "content"
        >>= loadAndApplyTemplate "templates/page.html"    siteContext
        >>= loadAndApplyTemplate "templates/default.html" siteContext
        >>= relativizeUrls

  -- Run Hakyll
  hakyll $ do

    -- Compile Announcements
    match "pages/announcements.html" $ do
      route permalinkRoute
      compile $ getResourceBody
          >>= applyAsTemplate postListContext
          >>= loadAndApplyTemplate "templates/page.html"      siteContext
          >>= loadAndApplyTemplate "templates/default.html"   siteContext
          >>= relativizeUrls

    match "posts/*" $ do
        route $ setExtension "html"
        compile $ pandocCompiler
            >>= saveSnapshot "content"
            >>= loadAndApplyTemplate "templates/post.html"    postContext
            >>= loadAndApplyTemplate "templates/default.html" siteContext
            >>= relativizeUrls

    -- Compile Acknowledgements
    match "pages/acknowledgements.md" $ do
      route permalinkRoute
      compile $ getResourceBody
          >>= applyAsTemplate acknowledgementsContext
          >>= renderPandoc
          >>= saveSnapshot "content"
          >>= loadAndApplyTemplate "templates/page.html"    siteContext
          >>= loadAndApplyTemplate "templates/default.html" siteContext
          >>= relativizeUrls

    match "authors/*.metadata" $
      compile getResourceBody

    match "contributors/*.metadata" $
      compile getResourceBody

    -- Compile other pages
    let include = "README.md" .||. "pages/*.md"
    let exclude = "pages/index.md" .||. "pages/acknowledgements.md"
    match (include .&&. complement exclude) $ do
      route permalinkRoute
      compile pageCompiler

    -- Compile chapters (using literate Agda)
    match "src/**.lagda.md" $ do
      route permalinkRoute
      compile $ pageWithAgdaCompiler agdaOptions

    -- Compile Table of Contents
    match "pages/index.md" $ do
      route permalinkRoute
      compile $ getResourceBody
        >>= applyAsTemplate tocContext
        >>= renderPandoc
        >>= loadAndApplyTemplate "templates/page.html"    siteContext
        >>= loadAndApplyTemplate "templates/default.html" siteContext
        >>= relativizeUrls

    match "pages/*.metadata" $
      compile getResourceBody

    -- Compile course pages
    match ("courses/**.md" .&&. complement "courses/**.lagda.md") $ do
      route permalinkRoute
      compile pageCompiler

    match "courses/**.lagda.md" $ do
      route permalinkRoute
      compile $ do
        courseDir <- takeDirectory . toFilePath <$> getUnderlying
        let courseOptions = agdaOptions
              { optIncludePaths = courseDir : optIncludePaths agdaOptions
              }
        pageWithAgdaCompiler courseOptions

    match "courses/**.pdf" $ do
      route idRoute
      compile copyFileCompiler

    -- Compile 404 page
    match "404.html" $ do
      route idRoute
      compile $ pandocCompiler
          >>= loadAndApplyTemplate "templates/default.html" siteContext

    -- Compile templates
    match "templates/*" $ compile templateBodyCompiler

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

    -- Compile EPUB
    match "epub/index.md" $ do
      route $ constRoute "plfa.epub"
      compile $ getResourceBody
        >>= readPandocWith epubReaderOptions
        >>= applyPandocFilters epubReaderOptions epubFilters ["epub3"]
        <&> writeEPUB3With epubWriterOptions

    -- Copy versions
    let versions = ["19.08", "20.07"]
    forM_ versions $ \v ->
      match (fromGlob $ "versions" </> v </> "**") $ do
        route $ gsubRoute ".versions/" (const "")
        compile copyFileCompiler



--------------------------------------------------------------------------------
-- Fix references to local Agda modules
--------------------------------------------------------------------------------

newtype Frontmatter = Frontmatter
  { frontmatterPermalink :: FilePath
  }

instance FromJSON Frontmatter where
  parseJSON = Y.withObject "Frontmatter" $ \v -> Frontmatter
    <$> v .: "permalink"

instance ToJSON Frontmatter where
  toJSON Frontmatter{..} =
    Y.object [ "permalink" .= frontmatterPermalink
             ]

-- |Create a function to fix URL references output by Agda HTML highlighter.
mkFixLocalLink :: FilePath -> IO (String -> String)
mkFixLocalLink rootDir = do
  -- Get all Agda files in `rootDir`.
  agdaFiles <- find always (fileName ~~? "*.lagda.md") rootDir

  -- Get all permalinks and Agda module names from these files.
  localLinkList <- forM agdaFiles $ \agdaFile -> do
    frontmatterOrError <- parseYamlFrontmatterEither <$> B.readFile agdaFile
    case frontmatterOrError of
      Left errmsg -> do
        printf "Parse error in '%s': %s\n" agdaFile errmsg
        exitFailure
      Right Frontmatter{..} ->
        return (agdaModuleFromPath rootDir agdaFile, frontmatterPermalink)

  -- Construct a Map from the local link list.
  let localLinkMap = M.fromList localLinkList

  -- Construct a function which looks up the URL in the map.
  return $ \url -> fromMaybe url $ do
    (oldPath, anchor) <- stripInfix ".html" url
    newPath <- M.lookup oldPath localLinkMap
    return $ newPath <> anchor
