{-# LANGUAGE OverloadedStrings #-}

import Hakyll
import Hakyll.Web.Agda
import Hakyll.Web.Sass
import Hakyll.Web.Routes.Permalink

--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------
siteContext :: Context String
siteContext = mconcat
  [ listField "authors" defaultContext (loadAll "authors/*.metadata")
  , constField "site_title" "Programming Foundations in Agda"
  , defaultContext
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

--------------------------------------------------------------------------------
agdaOptions :: CommandLineOptions
agdaOptions = defaultAgdaOptions
  { optUseLibs       = False
  , optIncludePaths  = ["standard-library/src", "src"]
  , optPragmaOptions = defaultAgdaPragmaOptions
    { optVerbose     = agdaVerbosityQuiet
    }
  }

--------------------------------------------------------------------------------
sassOptions :: SassOptions
sassOptions = defaultSassOptions
  { sassIncludePaths = Just ["css"]
  }

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

    -- Compile authors
    match "authors/*.metadata" $ compile getResourceBody

    -- Compile Announcements
    match "posts/*" $ do
        route $ setExtension "html"
        compile $ pandocCompiler
            >>= saveSnapshot "content"
            >>= loadAndApplyTemplate "templates/post.html"    postContext
            >>= loadAndApplyTemplate "templates/default.html" siteContext
            >>= relativizeUrls

    match "announcements.md" $ do
      route $ permalinkRoute (setExtension "html")
      compile $ pandocCompiler
          >>= loadAndApplyTemplate "templates/post-list.html" postListContext
          >>= loadAndApplyTemplate "templates/default.html"   siteContext
          >>= relativizeUrls

    -- Compile Book
    match ("index.md" .||. "README.md" .||. "src/**.md" .&&. complement "**.lagda.md") $ do
      route $ permalinkRoute (setExtension "html")
      compile $ pandocCompiler
          >>= loadAndApplyTemplate "templates/page.html"    siteContext
          >>= loadAndApplyTemplate "templates/default.html" siteContext
          >>= relativizeUrls

    match "src/**.lagda.md" $ do
      route $ permalinkRoute (setExtension "html")
      compile $ agdaCompilerWith agdaOptions
          >>= renderPandoc
          >>= loadAndApplyTemplate "templates/page.html"    siteContext
          >>= loadAndApplyTemplate "templates/default.html" siteContext
          >>= relativizeUrls

    -- Compile 404 page
    match "404.html" $ do
      route idRoute
      compile $ pandocCompiler
          >>= loadAndApplyTemplate "templates/default.html" siteContext

    match "templates/*" $ compile templateBodyCompiler

