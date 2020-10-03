{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Hakyll.Web.Agda
  ( agdaCompilerWith
  , agdaVerbosityQuiet
  , CommandLineOptions(..)
  , PragmaOptions(..)
  , defaultAgdaOptions
  , defaultAgdaPragmaOptions
  ) where

import qualified Agda.Main as Agda
import           Agda.Interaction.Options
import qualified Agda.Interaction.Highlighting.HTML as Agda (generateHTML)
import qualified Agda.Utils.Trie as Trie (singleton)
import           Control.Exception (catchJust)
import           Control.Monad (void)
import qualified Data.List as L
import qualified Data.Text as T
import           Data.Text.ICU as RE (Regex, MatchOption(..), regex, find, group)
import           Data.Text.ICU.Replace as RE (Replace, rtext, replaceAll)
import           Hakyll
import           Text.Regex.TDFA ((=~))
import           System.Directory (createDirectoryIfMissing)
import           System.Exit (ExitCode(..))
import           System.FilePath ((</>), (<.>), dropExtension, makeRelative, pathSeparator)
import           System.FilePath.Glob (glob)

-- |Default Agda pragma options. Rename of `defaultOptions`.
defaultAgdaOptions :: CommandLineOptions
defaultAgdaOptions = defaultOptions

-- |Default Agda pragma options. Rename of `defaultPragmaOptions`.
defaultAgdaPragmaOptions :: PragmaOptions
defaultAgdaPragmaOptions = defaultPragmaOptions

-- |Compile literate Agda to HTML
agdaCompilerWith :: CommandLineOptions -> Compiler (Item String)
agdaCompilerWith agdaOptions = do
  item <- getResourceBody
  let agdaPath = toFilePath (itemIdentifier item)
  let moduleName = agdaModuleName (itemBody item)
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


-- * Correct standard library URLs

-- |Default URL for the Agda stdlib.
defaultStdLibHref :: T.Text
defaultStdLibHref = "https://agda.github.io/agda-stdlib/"

-- |An ICU regular expression which matches links to the Agda stdlib.
reStdlibHref :: FilePath -> IO Regex
reStdlibHref stdlibPath = do
  modNames <- map T.pack <$> stdlibModules stdlibPath
  let builtin  = "Agda\\.[A-Za-z\\.]+"
  let modPatns = T.replace "." "\\." <$> modNames
  let modPatn  = T.concat . L.intersperse "|" $ builtin : modPatns
  let hrefPatn = "[\"'](" `T.append` modPatn `T.append` ")\\.html(#[^\"^']+)?[\"']"
  return (regex [] hrefPatn)

-- |Gather all standard library modules given a path.
stdlibModules :: FilePath -> IO [String]
stdlibModules stdlibPath = do
  agdaFiles <- glob (stdlibPath </> "**.agda")
  let sepToDot c = if c == pathSeparator then '.' else c
  let fileToMod  = map sepToDot . dropExtension . makeRelative stdlibPath
  return $ map fileToMod agdaFiles
