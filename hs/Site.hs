{-# LANGUAGE OverloadedStrings #-}

import Hakyll
import Hakyll.Web.Agda
import Hakyll.Web.Sass
import Hakyll.Web.Routes.Permalink
import System.FilePath (takeDirectory)


--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------

siteContext :: Context String
siteContext = mconcat
  [ constField "site_title" "Programming Foundations in Agda"
  , constField "site_url" "https://plfa.github.io"
  , constField "license" "Creative Commons Attribution 4.0 International License"
  , constField "license_url" "https://creativecommons.org/licenses/by/4.0/"
  , constField "repository" "plfa/plfa.github.io"
  , constField "branch" "dev"
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

agdaOptions :: AgdaOptions
agdaOptions = defaultAgdaOptions
  { agdaCommandLineOptions = defaultAgdaCommandLineOptions
    { optUseLibs       = False
    , optIncludePaths  = ["standard-library/src", "src"]
    , optPragmaOptions = defaultAgdaPragmaOptions
      { optVerbose     = agdaVerbosityQuiet
      }
    }
  , agdaStandardLibraryDir = Just "standard-library"
  }

sassOptions :: SassOptions
sassOptions = defaultSassOptions
  { sassIncludePaths = Just ["css"]
  }


--------------------------------------------------------------------------------
-- Build site
--------------------------------------------------------------------------------

main :: IO ()
main = hakyll $ do

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

    -- Compile author and contributor metadata
    match "authors/*.metadata" $ compile getResourceBody
    match "contributors/*.metadata" $ compile getResourceBody

    -- Compile Acknowledgements
    match "pages/acknowledgements.html" $ do
      route permalinkRoute
      compile $ getResourceBody
          >>= applyAsTemplate acknowledgementsContext
          >>= loadAndApplyTemplate "templates/page.html"    siteContext
          >>= loadAndApplyTemplate "templates/default.html" siteContext
          >>= relativizeUrls

    -- Compile Announcements
    match "posts/*" $ do
        route $ setExtension "html"
        compile $ pandocCompiler
            >>= saveSnapshot "content"
            >>= loadAndApplyTemplate "templates/post.html"    postContext
            >>= loadAndApplyTemplate "templates/default.html" siteContext
            >>= relativizeUrls

    match "pages/announcements.html" $ do
      route permalinkRoute
      compile $ getResourceBody
          >>= applyAsTemplate postListContext
          >>= loadAndApplyTemplate "templates/page.html"      siteContext
          >>= loadAndApplyTemplate "templates/default.html"   siteContext
          >>= relativizeUrls

    -- Compile other pages
    match ("README.md" .||. "pages/*.md") $ do
      route permalinkRoute
      compile pageCompiler

    -- Compile chapters (using literate Agda)
    match "src/**.lagda.md" $ do
      route permalinkRoute
      compile $ pageWithAgdaCompiler agdaOptions

    -- Compile course pages
    match ("courses/**.md" .&&. complement "courses/**.lagda.md") $ do
      route permalinkRoute
      compile pageCompiler

    match "courses/**.lagda.md" $ do
      route permalinkRoute
      compile $ do
        courseDir <- takeDirectory . toFilePath <$> getUnderlying
        -- We need lenses :'(
        let commandLineOptions = agdaCommandLineOptions agdaOptions
        let includePaths = optIncludePaths commandLineOptions
        let courseOptions = agdaOptions
              { agdaCommandLineOptions = commandLineOptions
                { optIncludePaths = courseDir : includePaths
                }
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

    match "templates/*" $ compile templateBodyCompiler


--------------------------------------------------------------------------------
pageCompiler :: Compiler (Item String)
pageCompiler = pandocCompiler
  >>= loadAndApplyTemplate "templates/page.html"    siteContext
  >>= loadAndApplyTemplate "templates/default.html" siteContext
  >>= relativizeUrls

pageWithAgdaCompiler :: AgdaOptions -> Compiler (Item String)
pageWithAgdaCompiler opts = agdaCompilerWith opts
  >>= renderPandoc
  >>= loadAndApplyTemplate "templates/page.html"    siteContext
  >>= loadAndApplyTemplate "templates/default.html" siteContext
  >>= relativizeUrls

