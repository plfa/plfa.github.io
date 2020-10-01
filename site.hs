{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

import qualified Agda.Main as Agda
import qualified Agda.Interaction.Options as Agda
import qualified Agda.Interaction.Highlighting.HTML as Agda (generateHTML)
import qualified Agda.Utils.Trie as Trie (singleton)
import           Control.Exception (catchJust)
import           Control.Monad (void)
import           Data.List (stripPrefix)
import           Data.Maybe (fromMaybe)
import           Hakyll
import           Text.Pandoc.Options (WriterOptions(..), HTMLMathMethod(..))
import           Text.Regex.TDFA ((=~))
import           Text.Sass (SassOptions(..), defaultSassOptions)
import qualified Text.Sass as Sass
import           System.Exit (ExitCode(..))
import           System.Directory (createDirectoryIfMissing)
import           System.FilePath ((</>), (<.>), dropExtension)

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
        compile (sassCompiler sassOptions)

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
      compile $ agdaCompiler
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
-- Create a route based on the 'permalink' metadata field
--------------------------------------------------------------------------------
permalinkRoute :: Routes -> Routes
permalinkRoute def = metadataRoute $ \metadata ->
  maybe def (constRoute . conv) (lookupString "permalink" metadata)
  where
    -- By a quirk of history, permalinks for PLFA are written as, e.g., "/DeBruijn/".
    -- We convert these to links by stripping the "/" prefix, and adding "index.html".
    conv :: FilePath -> FilePath
    conv permalink = fromMaybe permalink (stripPrefix "/" permalink) </> "index.html"


--------------------------------------------------------------------------------
-- Compile Literate Agda
--------------------------------------------------------------------------------
agdaCompiler :: Compiler (Item String)
agdaCompiler = do
  item <- getResourceBody
  let agdaPath = toFilePath (itemIdentifier item)
  let moduleName = agdaModuleName (itemBody item)
  TmpFile tmpPath <- newTmpFile ".lock"
  let tmpDir = init (dropExtension tmpPath)
  let mdPath = tmpDir </> moduleName <.> "md"
  md <- unsafeCompiler $ do
    createDirectoryIfMissing True tmpDir
    agdaGenerateHTML agdaPath tmpDir
    md <- readFile mdPath
    removeDirectory tmpDir
    return md
  return $ itemSetBody md item

agdaModuleName :: String -> String
agdaModuleName code = case regexResult of
  (_, _, _, [moduleName]) -> moduleName
  _                       -> "Main"
  where
    moduleRegex = "module ([^ ]*) where" :: String
    regexResult = code =~ moduleRegex :: (String, String, String, [String])

-- |Generate HTML using Agda
agdaGenerateHTML :: FilePath -> FilePath -> IO ()
agdaGenerateHTML inputFile htmlDir = do
  let opts = agdaOptions inputFile htmlDir
  let tcm = void $ Agda.runAgdaWithOptions [] Agda.generateHTML (Agda.defaultInteraction opts) "agda" opts
  catchJust
    (\case {e@ExitSuccess -> Just e; _ -> Nothing})
    (Agda.runTCMPrettyErrors tcm)
    (\_ -> return ())

agdaOptions :: FilePath -> FilePath -> Agda.CommandLineOptions
agdaOptions inputFile htmlDir = Agda.defaultOptions
  { Agda.optInputFile     = Just inputFile
  , Agda.optUseLibs       = False
  , Agda.optIncludePaths  = ["standard-library/src", "src"]
  , Agda.optGenerateHTML  = True
  , Agda.optHTMLHighlight = Agda.HighlightCode
  , Agda.optHTMLDir       = htmlDir
  , Agda.optPragmaOptions = Agda.defaultPragmaOptions
    { Agda.optVerbose     = Trie.singleton [] 0
    }
  }

--------------------------------------------------------------------------------
-- Compile SASS and SCSS
--------------------------------------------------------------------------------
sassCompiler :: SassOptions -> Compiler (Item String)
sassCompiler opts = cached "sass" $ getResourceBody >>= withItemBody renderSass
  where
    renderSass :: String -> Compiler String
    renderSass sass = unsafeCompiler $ do
      cssOrErr <- Sass.compileString sass opts
      case cssOrErr of
        Left  err -> Sass.errorMessage err
        Right css -> return (compressCss css)

--------------------------------------------------------------------------------
sassOptions :: SassOptions
sassOptions = defaultSassOptions
  { sassIncludePaths = Just ["css"]
  }
