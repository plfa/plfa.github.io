module PLFA.Agda
  ( Format (..)
  , AgdaOpts (..)
  , callAgdaWith
  ) where

import Agda.Main
import Agda.Compiler.Backend (Backend, parseBackendOptions, backendInteraction)
import Agda.Interaction.Options (defaultOptions)
import Agda.Interaction.Highlighting.HTML (htmlBackend)
import Agda.Interaction.Highlighting.LaTeX (latexBackend)
import Agda.Utils.FileName (absolute)
import Control.Exception (throwIO, handle)
import Control.Monad.Except (Except, runExcept)
import Data.List qualified as L
import Data.Maybe (listToMaybe, catMaybes)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Development.Shake
import Development.Shake.FilePath
import System.Exit (ExitCode (..))

data Format
  = Markdown
  | LaTeX

data AgdaOpts = AgdaOpts
  { format       :: Format
  , tmpDir       :: FilePath
  , includePaths :: [FilePath]
  , inputFile    :: FilePath
  }

callAgdaWith :: AgdaOpts -> Action Text
callAgdaWith opts@AgdaOpts{..} = liftIO $ do
  -- Call Agda
  let backends = [getBackend format]
  (backends, agdaOpts) <- liftExcept $ parseBackendOptions backends (mkOpts opts) defaultOptions
  absInputFile <- absolute inputFile
  let interactor = backendInteraction absInputFile backends
  swallowExitSuccess $
    runTCMPrettyErrors $
      runAgdaWithOptions interactor "agda" agdaOpts
  -- Guess the output path and read the output file
  out <- outputPath opts
  T.readFile out


-- * Helper functions

-- | Guess the path to which Agda writes the relevant output file.
outputPath :: AgdaOpts -> IO FilePath
outputPath opts@(AgdaOpts Markdown tmpDir includePaths inputFile) = do
  moduleName <-
    liftMaybe ("Could not guess module name for " <> inputFile) $
      guessModuleName includePaths inputFile
  return $ tmpDir </> moduleName <.> "md"
outputPath opts@(AgdaOpts LaTeX tmpDir includePaths inputFile) = do
  modulePath <-
    liftMaybe ("Could not guess module name for " <> inputFile) $
      guessModulePath includePaths inputFile
  return $ tmpDir </> replaceExtensions modulePath "tex"

-- | Guess the module name based on the filename and the include path.
guessModuleName :: [FilePath] -> FilePath -> Maybe FilePath
guessModuleName includePaths inputFile =
  pathToModule <$> guessModulePath includePaths inputFile
  where
    pathToModule fp = map (\c -> if c == '/' then '.' else c) (dropExtensions fp)

-- | Guess the module path based on the filename and the include path.
guessModulePath :: [FilePath] -> FilePath -> Maybe FilePath
guessModulePath includePaths inputFile =
  listToMaybe $
    catMaybes $
      [ stripPrefix includePath inputFile | includePath <- includePaths ]
  where
    stripPrefix fp1 fp2 =
      joinPath <$> L.stripPrefix (splitDirectories fp1) (splitDirectories fp2)

mkOpts :: AgdaOpts -> [String]
mkOpts AgdaOpts{..} = formatOpts format <> includeOpts
  where
    -- | Construct the Agda command-line options for rendering Agda to a particular format.
    formatOpts :: Format -> [String]
    formatOpts Markdown = [ "--html" , "--html-dir=" <> tmpDir , "--html-highlight=code" ]
    formatOpts LaTeX = [ "--latex" , "--latex-dir=" <> tmpDir ]

    -- | Construct the Agda command-line options for an explicit include path.
    includeOpts :: [String]
    includeOpts =
      [ "--no-libraries" ] <> [ "--include-path=" <> includePath | includePath <- includePaths ]

-- | Get the correct backend for the given format.
getBackend :: Format -> Backend
getBackend Markdown = htmlBackend
getBackend LaTeX = latexBackend

liftExcept :: MonadFail m => Except String a -> m a
liftExcept m = liftEither (runExcept m)

liftEither :: MonadFail m => Either String a -> m a
liftEither (Left e) = fail e
liftEither (Right a) = return a

liftMaybe :: MonadFail m => String -> Maybe a -> m a
liftMaybe msg Nothing = fail msg
liftMaybe _ (Just a) = return a

swallowExitSuccess :: IO () -> IO ()
swallowExitSuccess = handle handler
  where
    handler :: ExitCode -> IO ()
    handler ExitSuccess = return ()
    handler exitCode    = throwIO exitCode
