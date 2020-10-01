--------------------------------------------------------------------------------
-- Compiler literate Agda
--------------------------------------------------------------------------------

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module PLFA.Agda (agdaCompiler, agdaCompilerWith, defaultAgdaOptions) where

import qualified Agda.Main as Agda
import qualified Agda.Interaction.Options as Agda
import qualified Agda.Interaction.Highlighting.HTML as Agda (generateHTML)
import qualified Agda.Utils.Trie as Trie (singleton)
import           Control.Exception (catchJust)
import           Control.Monad (void)
import           Hakyll
import           Text.Regex.TDFA ((=~))
import           System.Directory (createDirectoryIfMissing)
import           System.Exit (ExitCode(..))
import           System.FilePath ((</>), (<.>), dropExtension)


-- |Compile literate Agda
agdaCompiler :: Compiler (Item String)
agdaCompiler = agdaCompilerWith defaultAgdaOptions

-- |Compile literate Agda (with options)
agdaCompilerWith :: Agda.CommandLineOptions -> Compiler (Item String)
agdaCompilerWith agdaOptions = do
  item <- getResourceBody
  let agdaPath = toFilePath (itemIdentifier item)
  let moduleName = agdaModuleName (itemBody item)
  TmpFile tmpPath <- newTmpFile ".lock"
  let tmpDir = init (dropExtension tmpPath)
  let mdPath = tmpDir </> moduleName <.> "md"
  md <- unsafeCompiler $ do
    createDirectoryIfMissing True tmpDir
    agdaGenerateHTML agdaOptions agdaPath tmpDir
    md <- readFile mdPath
    removeDirectory tmpDir
    return md
  return $ itemSetBody md item

-- |Get Agda module name from body
agdaModuleName :: String -> String
agdaModuleName code = case regexResult of
  (_, _, _, [moduleName]) -> moduleName
  _                       -> "Main"
  where
    moduleRegex = "module ([^ ]*) where" :: String
    regexResult = code =~ moduleRegex :: (String, String, String, [String])

-- |Generate HTML using Agda
agdaGenerateHTML :: Agda.CommandLineOptions -> FilePath -> FilePath -> IO ()
agdaGenerateHTML agdaOptions inputFile htmlDir = do
  let opts = agdaOptions
        { Agda.optInputFile = Just inputFile
        , Agda.optHTMLDir   = htmlDir
        }
  let tcm = void $ Agda.runAgdaWithOptions [] Agda.generateHTML (Agda.defaultInteraction opts) "agda" opts
  catchJust
    (\case {e@ExitSuccess -> Just e; _ -> Nothing})
    (Agda.runTCMPrettyErrors tcm)
    (\_ -> return ())

-- |Default Agda options
defaultAgdaOptions :: Agda.CommandLineOptions
defaultAgdaOptions = Agda.defaultOptions
  { Agda.optUseLibs       = False
  , Agda.optIncludePaths  = ["standard-library/src", "src"]
  , Agda.optGenerateHTML  = True
  , Agda.optHTMLHighlight = Agda.HighlightCode
  , Agda.optPragmaOptions = Agda.defaultPragmaOptions
    { Agda.optVerbose     = Trie.singleton [] 0
    }
  }

