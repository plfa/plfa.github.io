{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Hakyll.Web.Agda
  ( agdaCompilerWith
  , agdaVerbosityQuiet
  , CommandLineOptions(..)
  , PragmaOptions(..)
  , defaultAgdaOptions
  , defaultAgdaPragmaOptions
  , mkFixStdlibLink
  , mkFixLocalLink
  , agdaModule
  , agdaModuleFromPath
  ) where

import qualified Agda.Main as Agda
import           Agda.Interaction.Options
import qualified Agda.Interaction.Highlighting.HTML as Agda (generateHTML)
import qualified Agda.Utils.Trie as Trie (singleton)
import           Control.Exception (catchJust)
import           Control.Monad (forM, void)
import qualified Data.ByteString as B
import           Data.Frontmatter (parseYamlFrontmatterEither)
import qualified Data.List.Extra as L
import           Data.Maybe (fromMaybe)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.ICU as ICU
import qualified Data.Text.ICU.Replace as ICU
import           Data.Yaml (FromJSON(..), ToJSON(..), (.:), (.=))
import qualified Data.Yaml as Y
import           Hakyll
import           Text.Printf (printf)
import           Text.Regex.TDFA ((=~))
import           System.Directory (createDirectoryIfMissing)
import           System.Exit (ExitCode(..), exitFailure)
import           System.FilePath.Find ((~~?), (==?), always, extension, fileName, find)
import           System.FilePath ((</>), (<.>), dropExtension, dropExtensions, makeRelative, pathSeparator)

-- |Default Agda command-line options. Rename of `defaultOptions`.
defaultAgdaOptions :: CommandLineOptions
defaultAgdaOptions = defaultOptions

-- |Default Agda pragma options. Rename of `defaultPragmaOptions`.
defaultAgdaPragmaOptions :: PragmaOptions
defaultAgdaPragmaOptions = defaultPragmaOptions

-- |Compile literate Agda to HTML
agdaCompilerWith :: CommandLineOptions -> Compiler (Item String)
agdaCompilerWith agdaOptions = cached "Hakyll.Web.Agda.agdaCompilerWith" $ do
  item <- getResourceBody
  let agdaPath = toFilePath (itemIdentifier item)
  let moduleName = agdaModule (itemBody item)
  TmpFile tmpPath <- newTmpFile ".lock"
  let tmpDir = init (dropExtension tmpPath)
  let mdPath = tmpDir </> moduleName <.> "md"

  md <- unsafeCompiler $ do
    createDirectoryIfMissing True tmpDir

    -- Add input file and HTML options
    let opts = agdaOptions
          { optInputFile     = Just agdaPath
          , optHTMLDir       = tmpDir
          , optGenerateHTML  = True
          , optHTMLHighlight = HighlightCode
          }

    -- Run Agda
    let tcm = void $
          Agda.runAgdaWithOptions [] Agda.generateHTML (Agda.defaultInteraction opts) "agda" opts

    catchJust
      (\case {e@ExitSuccess -> Just e; _ -> Nothing})
      (Agda.runTCMPrettyErrors tcm)
      (\_ -> return ())

    -- Read output Markdown file
    md <- readFile mdPath
    removeDirectory tmpDir
    return md

  return $ itemSetBody md item

-- |Get Agda module name from code
agdaModule :: String -> String
agdaModule code = case regexResult of
  (_, _, _, [moduleName]) -> moduleName
  _                       -> "Main"
  where
    moduleRegex = "module ([^ ]*) where" :: String
    regexResult = code =~ moduleRegex :: (String, String, String, [String])

-- |Get Agda module from a path and a root directory
agdaModuleFromPath :: FilePath -> FilePath -> String
agdaModuleFromPath rootDir = map slashToDot . makeRelative rootDir . dropExtensions
  where
    slashToDot c = if c == '/' then '.' else c


-- |Suppress non-error output
agdaVerbosityQuiet :: Verbosity
agdaVerbosityQuiet = Trie.singleton [] 0


--------------------------------------------------------------------------------
-- Fix references to Agda standard library
--------------------------------------------------------------------------------

-- |Default URL for the Agda standard library.
defaultStdlibUrl :: String
defaultStdlibUrl = "https://agda.github.io/agda-stdlib"

readStdlibVersion :: FilePath -> IO String
readStdlibVersion stdlibPath = do
  let changelogPath = stdlibPath </> "CHANGELOG.md"
  changelog <- T.readFile changelogPath
  let versionLine = head (T.lines changelog)
  case T.stripPrefix "Version " versionLine of
    Just versionStr -> return . T.unpack $ "v" <> T.strip versionStr
    Nothing -> error $ printf "Could not read version from '%s'" changelogPath

-- |Fix references to the Agda standard library.
mkFixStdlibLink :: FilePath -> IO (String -> String)
mkFixStdlibLink stdlibPath = do
  stdlibVersion <- readStdlibVersion stdlibPath
  let stdlibUrl = defaultStdlibUrl </> stdlibVersion
  re <- stdlibRegex stdlibPath
  let replacement = ICU.rstring stdlibUrl <> "/$1.html$2"
  return $ T.unpack . ICU.replaceAll re replacement . T.pack

-- |An ICU regular expression which matches links to the Agda standard library.
stdlibRegex :: FilePath -> IO ICU.Regex
stdlibRegex stdlibPath = do
  modNames <- map T.pack <$> stdlibModules stdlibPath
  let builtin  = "Agda\\.[A-Za-z\\.]+"
  let modPatns = T.replace "." "\\." <$> modNames
  let modPatn  = T.concat . L.intersperse "|" $ builtin : modPatns
  let hrefPatn = "(" `T.append` modPatn `T.append` ")\\.html(#[^\"^']+)?"
  return (ICU.regex [] hrefPatn)

-- |Gather all standard library modules given a path.
stdlibModules :: FilePath -> IO [String]
stdlibModules stdlibPath = do
  let stdlibPathSrc = stdlibPath </> "src"
  agdaFiles <- find always (extension ==? ".agda") stdlibPathSrc
  let sepToDot c = if c == pathSeparator then '.' else c
  let fileToMod  = map sepToDot . dropExtension . makeRelative stdlibPathSrc
  return . map fileToMod $ agdaFiles



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
    (oldPath, anchor) <- L.stripInfix ".html" url
    newPath <- M.lookup oldPath localLinkMap
    return $ newPath <> anchor
