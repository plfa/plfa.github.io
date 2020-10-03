{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Hakyll.Web.Agda
  ( agdaCompilerWith
  , agdaVerbosityQuiet
  , AgdaOptions(..)
  , CommandLineOptions(..)
  , PragmaOptions(..)
  , defaultAgdaOptions
  , defaultAgdaCommandLineOptions
  , defaultAgdaPragmaOptions
  ) where

import qualified Agda.Main as Agda
import           Agda.Interaction.Options
import qualified Agda.Interaction.Highlighting.HTML as Agda (generateHTML)
import qualified Agda.Utils.Trie as Trie (singleton)
import           Control.Exception (catchJust)
import           Control.Monad (void)
import           Data.Maybe (fromMaybe)
import qualified Data.List as L
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.ICU as ICU
import qualified Data.Text.ICU.Replace as ICU
import           Hakyll
import           Text.Printf (printf)
import           Text.Regex.TDFA ((=~))
import           System.Directory (createDirectoryIfMissing)
import           System.Exit (ExitCode(..))
import           System.FilePath ((</>), (<.>), dropExtension, makeRelative, pathSeparator)
import           System.FilePath.Glob (glob)


data AgdaOptions = AgdaOptions
  { agdaCommandLineOptions :: CommandLineOptions
  , agdaStandardLibraryDir :: Maybe FilePath
  }

-- |Default Agda options.
defaultAgdaOptions :: AgdaOptions
defaultAgdaOptions = AgdaOptions
  { agdaCommandLineOptions = defaultAgdaCommandLineOptions
  , agdaStandardLibraryDir = Nothing
  }

-- |Default Agda command-line options. Rename of `defaultOptions`.
defaultAgdaCommandLineOptions :: CommandLineOptions
defaultAgdaCommandLineOptions = defaultOptions

-- |Default Agda pragma options. Rename of `defaultPragmaOptions`.
defaultAgdaPragmaOptions :: PragmaOptions
defaultAgdaPragmaOptions = defaultPragmaOptions

-- |Compile literate Agda to HTML
agdaCompilerWith :: AgdaOptions -> Compiler (Item String)
agdaCompilerWith AgdaOptions{..} = do
  item <- getResourceBody
  let agdaPath = toFilePath (itemIdentifier item)
  let moduleName = agdaModuleName (itemBody item)
  TmpFile tmpPath <- newTmpFile ".lock"
  let tmpDir = init (dropExtension tmpPath)
  let mdPath = tmpDir </> moduleName <.> "md"

  md <- unsafeCompiler $ do
    createDirectoryIfMissing True tmpDir

    -- Add input file and HTML options
    let opts = agdaCommandLineOptions
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

    -- Fix references to the Agda standard library
    --
    -- TODO: should be replace with a Pandoc URL filter
    --
    md' <-
      case agdaStandardLibraryDir of
        Nothing         -> return md
        Just stdlibPath -> do
          stdlibVersion <- readStdlibVersion stdlibPath
          let stdlibUrl = defaultStdlibUrl <> stdlibVersion
          fix <- fixStdlibLink stdlibPath stdlibUrl
          return . T.unpack . fix . T.pack $ md

    return md'

  return $ itemSetBody md item

-- |Get Agda module name from code
agdaModuleName :: String -> String
agdaModuleName code = case regexResult of
  (_, _, _, [moduleName]) -> moduleName
  _                       -> "Main"
  where
    moduleRegex = "module ([^ ]*) where" :: String
    regexResult = code =~ moduleRegex :: (String, String, String, [String])

-- |Suppress non-error output
agdaVerbosityQuiet :: Verbosity
agdaVerbosityQuiet = Trie.singleton [] 0


-- * Fix references to Agda standard library

-- |Default URL for the Agda standard library.
defaultStdlibUrl :: Text
defaultStdlibUrl = "https://agda.github.io/agda-stdlib/"

readStdlibVersion :: FilePath -> IO Text
readStdlibVersion stdlibPath = do
  let changelogPath = stdlibPath </> "CHANGELOG.md"
  changelog <- T.readFile changelogPath
  let versionLine = head (T.lines changelog)
  case T.stripPrefix "Version " versionLine of
    Just versionStr -> return $ "v" <> T.strip versionStr
    Nothing -> error $ printf "Could not read version from '%s'" changelogPath

-- |Fix references to the Agda standard library.
fixStdlibLink :: FilePath -> Text -> IO (Text -> Text)
fixStdlibLink stdlibPath stdlibUrl = do
  re <- stdlibRegex stdlibPath
  let replacement = "\"" <> ICU.rtext (dropTrailingSlash stdlibUrl) <> "/$1.html$2\""
  return $ ICU.replaceAll re replacement

-- |Drop the trailing slash from a string.
dropTrailingSlash :: Text -> Text
dropTrailingSlash t = fromMaybe t (T.stripSuffix "/" t)

-- |An ICU regular expression which matches links to the Agda standard library.
stdlibRegex :: FilePath -> IO ICU.Regex
stdlibRegex stdlibPath = do
  modNames <- map T.pack <$> stdlibModules stdlibPath
  let builtin  = "Agda\\.[A-Za-z\\.]+"
  let modPatns = T.replace "." "\\." <$> modNames
  let modPatn  = T.concat . L.intersperse "|" $ builtin : modPatns
  let hrefPatn = "[\"'](" `T.append` modPatn `T.append` ")\\.html(#[^\"^']+)?[\"']"
  return (ICU.regex [] hrefPatn)

-- |Gather all standard library modules given a path.
stdlibModules :: FilePath -> IO [String]
stdlibModules stdlibPath = do
  let stdlibPathSrc = stdlibPath </> "src"
  agdaFiles <- glob (stdlibPathSrc </> "**.agda")
  let sepToDot c = if c == pathSeparator then '.' else c
  let fileToMod  = map sepToDot . dropExtension . makeRelative stdlibPathSrc
  return $ map fileToMod agdaFiles
