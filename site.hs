{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

import qualified Agda.Main as Agda
import qualified Agda.Interaction.Options as Agda
import qualified Agda.Interaction.Highlighting.HTML as Agda (generateHTML)
import qualified Agda.Utils.Trie as Trie (singleton)
import           Control.Exception (catchJust)
import           Data.List (stripPrefix)
import           Data.Maybe (fromMaybe)
import           Hakyll
import           Text.Regex.TDFA ((=~))
import           Text.Sass (SassOptions(..), defaultSassOptions)
import qualified Text.Sass as Sass
import           System.Exit (ExitCode(..))
import           System.Directory (createDirectoryIfMissing)
import           System.FilePath ((</>), (<.>), dropExtension)

--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------
siteCtx :: Context String
siteCtx = constField "site_title" "Programming Foundations in Agda"
       <> defaultContext

--------------------------------------------------------------------------------
pageCtx :: Context String
pageCtx = siteCtx

--------------------------------------------------------------------------------
postCtx :: Context String
postCtx = dateField "date" "%B %e, %Y"
       <> siteCtx

--------------------------------------------------------------------------------
permalinkRoute :: Routes
permalinkRoute = metadataRoute $ \metadata ->
  maybe idRoute (constRoute . mk) (lookupString "permalink" metadata)
  where
    -- By a quirk of history, permalinks for PLFA are written as, e.g., /DeBruijn/.
    -- We convert these to links by:
    --
    --   1. stripping the / prefix
    --   2. adding the index.html suffix
    --
    mk :: FilePath -> FilePath
    mk permalink = fromMaybe permalink (stripPrefix "/" permalink) </> "index.html"

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do

    -- Copy resources
    match "public/**" $ do
      route idRoute
      compile copyFileCompiler

    -- Compile CSS
    match "css/*.css" $ compile compressCssCompiler
    match "css/*.scss" $ compile $ sassCompiler sassOptions
    create ["public/css/style.css"] $ do
      route idRoute
      compile $ do
        csses <- loadAll ("css/*.css" .||. "css/*.scss")
        makeItem $ unlines $ map itemBody csses

    -- Compile Table of Contents
    match "index.md" $ do
      route $ setExtension "html"
      compile $ pandocCompiler
          >>= loadAndApplyTemplate "templates/page.html"    pageCtx
          >>= loadAndApplyTemplate "templates/default.html" siteCtx
          >>= relativizeUrls

    -- Compile Book
    match ("src/**.md" .&&. complement "**.lagda.md") $ do
      route permalinkRoute
      compile $ pandocCompiler
        >>= loadAndApplyTemplate "templates/page.html"    pageCtx
        >>= loadAndApplyTemplate "templates/default.html" siteCtx
        >>= relativizeUrls

    match "src/**.lagda.md" $ do
      route permalinkRoute
      compile $ agdaCompiler
        >>= renderPandoc
        >>= loadAndApplyTemplate "templates/page.html"    pageCtx
        >>= loadAndApplyTemplate "templates/default.html" siteCtx
        >>= relativizeUrls

    -- Compile 404 page
    match "404.html" $ do
      route idRoute
      compile $ pandocCompiler
        >>= loadAndApplyTemplate "templates/default.html" siteCtx

    match "templates/*" $ compile templateBodyCompiler



--------------------------------------------------------------------------------
-- Compile Literate Agda
--------------------------------------------------------------------------------
agdaCompiler :: Compiler (Item String)
agdaCompiler = cached "agda" $ do

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

agdaGenerateHTML :: FilePath -> FilePath -> IO ()
agdaGenerateHTML inputFile htmlDir = do
  let opts = agdaOptions inputFile htmlDir
  let tcm = do
        _ <- Agda.runAgdaWithOptions [] Agda.generateHTML (Agda.defaultInteraction opts) "agda" opts
        return ()
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
