{-# LANGUAGE OverloadedStrings #-}

module Development.Shake.Agda
  ( Format (..)
  , AgdaOpts (..)
  , AgdaLib (..)
  , highlightAgdaWith
  , standardLibraryAgdaLib
  , prepareFixLinks
  , prepareFixExternalLinks
  , prepareFixLocalLinksWithPermalink
  ) where

import Agda.Main
import Agda.Compiler.Backend (Backend, parseBackendOptions, backendInteraction)
import Agda.Interaction.Options (defaultOptions)
import Agda.Interaction.Highlighting.HTML (htmlBackend)
import Agda.Interaction.Highlighting.LaTeX (latexBackend)
import Agda.Utils.FileName (absolute)
import Control.Exception (throwIO, handle)
import Control.Monad (forM, forM_)
import Data.ByteString qualified as B
import Data.Default.Class (Default (..))
import Data.Frontmatter (parseYamlFrontmatterEither)
import Data.IORef (newIORef, readIORef, modifyIORef')
import Data.List qualified as L
import Data.List.Extra qualified as L
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (listToMaybe, catMaybes, fromMaybe)
import Data.Monoid (Endo(..))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Text.ICU qualified as ICU
import Data.Text.ICU.Replace qualified as ICU
import Data.Yaml (FromJSON(..), ToJSON(..), (.:), (.=))
import Data.Yaml qualified as Y
import Development.Shake (Action, liftIO)
import Development.Shake.FilePath
import General.Extra (liftExcept, liftEither, liftMaybe)
import System.Exit
import System.Directory (doesFileExist, copyFile)
import System.FilePath.Find ((~~?), (==?), always, extension, fileName, find)
import Text.Printf


--------------------------------------------------------------------------------
-- Compile literate Agda to Markdown/HTML or LaTeX
--------------------------------------------------------------------------------

data Format
  = Markdown
  | LaTeX
  deriving (Eq, Ord)

type Url = String

data AgdaLib
  = AgdaLib
  { -- | The source directory.
    --
    --   NOTE: We don't parse .agda-lib files, and simply expect to be pointed
    --         to the correct source directory. For instance, for the standard
    --         library, 'libDir' should refer to 'standard-library/src'.
    --
    libDir :: FilePath
    -- | If 'libUrl' is set, generated links for this library are rebased to the given URL.
    --   Otherwise, the library is assumed to be local, and links are rebased using a different procedure.
  , libUrl :: Maybe Url
  }

instance Default AgdaLib where
  def = AgdaLib
    { libDir = error "AgdaLib: please specify libDir"
    , libUrl = Nothing
    }

data AgdaOpts = AgdaOpts
  { formats     :: [Format]
  , tmpDir      :: FilePath
  , libraries   :: [AgdaLib]
  , inputFile   :: FilePath
  , outputFiles :: Map Format FilePath
  }

instance Default AgdaOpts where
  def = AgdaOpts
        { formats     = error "AgdaOpts: please specify at least one format",
          tmpDir      = error "AgdaOpts: please specify tmpDir",
          libraries   = [],
          inputFile   = error "AgdaOpts: please specify input file",
          outputFiles = M.empty
        }


-- | Highlight Agda code embedded in Markdown or LaTeX.
highlightAgdaWith :: AgdaOpts -> Action (Map Format Text)
highlightAgdaWith opts@AgdaOpts{..} = liftIO $ do

  -- Call Agda with the appropriate options and backend
  let backends = map getBackend formats
  (configuredBackends, agdaOpts) <- liftExcept id $
    parseBackendOptions backends (mkArgs opts) defaultOptions
  absInputFile <- absolute inputFile
  let interactor = backendInteraction absInputFile configuredBackends
  swallowExitSuccess $
    runTCMPrettyErrors $
      runAgdaWithOptions interactor "agda" agdaOpts

  -- For each format, check if an output file was provided:
  -- * If so, simply copy the file.
  -- * Otherwise, read the file and return it as part of the output map.
  outputMapRef <- newIORef M.empty
  forM_ formats $ \format -> do
    out <- guessOutputPath format opts
    case M.lookup format outputFiles of
      Nothing -> do
        content <- T.readFile out
        modifyIORef' outputMapRef (M.insert format content)
      Just outputFile -> copyFile out outputFile

  readIORef outputMapRef


mkArgs :: AgdaOpts -> [String]
mkArgs AgdaOpts{..} = mconcat [verboseOpts, libraryOpts, foldMap formatOpts formats]
  where
    verboseOpts :: [String]
    verboseOpts = ["--verbose=0"]

    formatOpts :: Format -> [String]
    formatOpts Markdown = [ "--html" , "--html-dir=" <> tmpDir , "--html-highlight=code" ]
    formatOpts LaTeX    = [ "--latex" , "--latex-dir=" <> tmpDir ]

    libraryOpts :: [String]
    libraryOpts = [ "--no-libraries" ] <> [ "--include-path=" <> libDir | AgdaLib{..} <- libraries ]

-- | Get the correct backend for the given format.
getBackend :: Format -> Backend
getBackend Markdown = htmlBackend
getBackend LaTeX    = latexBackend


-- | If the passed action throws an 'ExitSuccess', catch it and swallow it.
swallowExitSuccess :: IO () -> IO ()
swallowExitSuccess action = handle handler action
  where
    handler :: ExitCode -> IO ()
    handler ExitSuccess = return ()
    handler exitCode    = throwIO exitCode


--------------------------------------------------------------------------------
-- Fix links to local or external libraries based on their AgdaLib
--------------------------------------------------------------------------------

prepareFixLinks :: [AgdaLib] -> IO (Url -> Url)
prepareFixLinks agdaLibs = appEndo <$> foldMap prepareFixLinks1 agdaLibs
  where
    prepareFixLinks1 :: AgdaLib -> IO (Endo Url)
    prepareFixLinks1 (AgdaLib libDir Nothing) =
      Endo <$> prepareFixLocalLinksWithPermalink libDir
    prepareFixLinks1 (AgdaLib libDir (Just libUrl)) =
      Endo <$> prepareFixExternalLinks libDir libUrl

--------------------------------------------------------------------------------
-- Fix references to external Agda modules using a canonical URL
--------------------------------------------------------------------------------

-- | Prepare a function which fixes references to the standard library,
--   given the include path.
prepareFixExternalLinks :: FilePath -> Url -> IO (Url -> Url)
prepareFixExternalLinks libDir libUrl = do
  regex <- reLinkToExternal libDir
  let replace = ICU.rstring libUrl <> "/$1.html$2"
  let fixExternalLink :: Url -> Url
      fixExternalLink url = T.unpack $ ICU.replaceAll regex replace $ T.pack url
  return fixExternalLink

-- | An ICU regular expression which matches links to the Agda standard library.
reLinkToExternal :: FilePath -> IO ICU.Regex
reLinkToExternal libDir = do
  modNames <- map T.pack <$> allModules libDir
  let builtin  = "Agda\\.[A-Za-z\\.]+"
  let modPatns = T.replace "." "\\." <$> modNames
  let modPatn  = T.concat . L.intersperse "|" $ builtin : modPatns
  let hrefPatn = "(" <> modPatn <> ")\\.html(#[^\"^']+)?"
  return (ICU.regex [] hrefPatn)

-- | Gather all modules given a path.
allModules :: FilePath -> IO [String]
allModules dir = do
  inputFiles <- find always (extension ==? ".agda") dir
  modules <- traverse (guessModuleName_ [dir]) inputFiles
  return modules


--------------------------------------------------------------------------------
-- Fix references to local Agda modules using YAML frontmatter
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

-- | Create a function to fix URL references to local modules
prepareFixLocalLinksWithPermalink :: FilePath -> IO (Url -> Url)
prepareFixLocalLinksWithPermalink libDir = do

  -- Get all literate Agda files in 'libDir'
  inputFiles <- find always (fileName ~~? "*.lagda.md") libDir

  -- Get all permalinks and Agda module names from these files
  localLinkList <- forM inputFiles $ \inputFile -> do
    permalink <- getPermalink inputFile
    moduleName <- guessModuleName_ [libDir] inputFile
    return (moduleName, permalink)

  let localLinks = M.fromList localLinkList

  -- Construct a function which looks up the URL in the map.
  let fixLocalLinkWithPermalink :: Url -> Url
      fixLocalLinkWithPermalink url = fromMaybe url $ do
        (oldPath, anchor) <- L.stripInfix ".html" url
        newPath <- M.lookup oldPath localLinks
        return $ newPath <> anchor

  return fixLocalLinkWithPermalink


-- | Read the permalink field from the YAML frontmatter.
getPermalink :: FilePath -> IO Url
getPermalink inputFile = do
  frontmatterOrError <- parseYamlFrontmatterEither <$> B.readFile inputFile
  Frontmatter{..} <- liftEither (printf "Parse error in '%s': %s\n" inputFile) frontmatterOrError
  return frontmatterPermalink


--------------------------------------------------------------------------------
-- Construct an 'AgdaLib' value for the standard library
--------------------------------------------------------------------------------

-- | Check whether or not a given 'FilePath' is a copy of the standard library.
isStandardLibrary :: FilePath -> IO Bool
isStandardLibrary dir = doesFileExist $ dir </> "standard-library.agda-lib"

-- | The default file used to obtain the current Agda standard library version.
changelogName :: FilePath
changelogName = "CHANGELOG.md"

-- | Read the version information from the first line of 'CHANGELOG.md'.
getStandardLibraryVersion :: FilePath -> IO String
getStandardLibraryVersion dir = do
  let pathToChangelog = dir </> changelogName
  correct <- doesFileExist pathToChangelog
  if not correct then
    error $ "Could not find " <> changelogName <> " in " <> dir
  else do
    changelog <- T.readFile pathToChangelog
    let verLine = head (T.lines changelog)
    ver <- liftMaybe ("Cannot read version from " <> pathToChangelog) $
      T.stripPrefix "Version " verLine
    return $ T.unpack $ "v" <> T.strip ver

-- | Construct an 'AgdaLib' value from the path to the standard library.
--
--   NOTE: We do not read the .agda-lib file. We /assume/ that the source
--         is located in the 'src' subdirectory. If that ever changes, or
--         it becomes easy to read .agda-lib files, this should be fixed.
--
standardLibraryAgdaLib :: FilePath -> IO AgdaLib
standardLibraryAgdaLib dir = do
  correct <- isStandardLibrary dir
  if not correct then
    error $ "Could not find standard library at " <> dir
  else do
    ver <- getStandardLibraryVersion dir
    printf "Found standard-library version %s at %s\n" ver dir
    let stdlibUrl = "https://agda.github.io/agda-stdlib" </> ver
    return AgdaLib
      { libDir    = dir </> "src"
      , libUrl = Just stdlibUrl
      }

--------------------------------------------------------------------------------
-- Guess to which file Agda writes HTML and LaTeX output
--------------------------------------------------------------------------------

-- | Guess the path to which Agda writes the relevant output file.
guessOutputPath :: Format -> AgdaOpts -> IO FilePath
guessOutputPath Markdown opts@AgdaOpts{..} = do
  moduleName <- guessModuleName_ (map libDir libraries) inputFile
  return $ tmpDir </> moduleName <.> "md"
guessOutputPath LaTeX opts@AgdaOpts{..} = do
  modulePath <- guessModulePath_ (map libDir libraries) inputFile
  return $ tmpDir </> replaceExtensions modulePath "tex"

-- | Guess the module name based on the filename and the include path.
guessModuleName :: [FilePath] -> FilePath -> Maybe FilePath
guessModuleName includePaths inputFile = pathToModule <$> guessModulePath includePaths inputFile
  where
    pathToModule fp = map sepToDot (dropExtensions fp)
      where
        sepToDot c = if c == '/' then '.' else c

-- | Variant of 'guessModuleName' which throws an error.
guessModuleName_ :: [FilePath] -> FilePath -> IO FilePath
guessModuleName_ includePaths inputFile =
  liftMaybe ("Could not guess module name for " <> inputFile) $
    guessModuleName includePaths inputFile

-- | Guess the module path based on the filename and the include path.
guessModulePath :: [FilePath] -> FilePath -> Maybe FilePath
guessModulePath includePaths inputFile =
  listToMaybe $
    catMaybes $
      [ stripPrefix includePath inputFile | includePath <- includePaths ]
  where
    stripPrefix fp1 fp2 =
      joinPath <$> L.stripPrefix (splitDirectories fp1) (splitDirectories fp2)

-- | Variant of 'guessModulePath' which throws an error.
guessModulePath_ :: [FilePath] -> FilePath -> IO FilePath
guessModulePath_ includePaths inputFile =
  liftMaybe ("Could not guess module path for " <> inputFile) $
    guessModulePath includePaths inputFile
