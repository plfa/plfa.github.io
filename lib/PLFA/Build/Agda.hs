{-# LANGUAGE FlexibleContexts #-}

module PLFA.Build.Agda
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
import Control.Monad (forM)
import Data.Default.Class (Default (..))
import Data.List qualified as L
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (listToMaybe, catMaybes, fromMaybe)
import Data.Monoid (Endo(..))
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Text.ICU qualified as ICU
import Data.Text.ICU.Replace qualified as ICU
import System.Exit
import System.Directory qualified as System (doesFileExist)
import System.FilePath.Find ((~~?), (==?), always, extension, fileName, find)
import System.IO.Temp (withTempDirectory, getCanonicalTemporaryDirectory)
import Text.Printf

import PLFA.Build.Metadata (readYamlFrontmatter, (^.))
import PLFA.Build.Prelude

--------------------------------------------------------------------------------
-- Compile literate Agda to Markdown/HTML or LaTeX
--------------------------------------------------------------------------------

data Format
  = Markdown
  | LaTeX
  deriving (Eq, Ord)

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
  }

instance Default AgdaOpts where
  def = AgdaOpts
        { formats   = error "AgdaOpts: please specify at least one format",
          tmpDir    = "",
          libraries = [],
          inputFile = error "AgdaOpts: please specify input file"
        }

getTemporaryDirectory :: AgdaOpts -> IO FilePath
getTemporaryDirectory AgdaOpts{..}
  | null tmpDir = getCanonicalTemporaryDirectory
  | otherwise   = return tmpDir

-- | Highlight Agda code embedded in Markdown or LaTeX.
highlightAgdaWith :: AgdaOpts -> Action (Map Format Text)
highlightAgdaWith opts@AgdaOpts{..} = liftIO $ do

  -- Create a temporary directory
  tmpParent <- getTemporaryDirectory opts
  withTempDirectory tmpParent "agda" $ \tmpDir' -> do
    let opts' = opts { tmpDir = tmpDir' }

    -- Call Agda with the appropriate options and backend
    let backends = map getBackend formats
    (configuredBackends, agdaOpts) <- liftExcept id $
      parseBackendOptions backends (mkArgs opts') defaultOptions
    absInputFile <- absolute inputFile
    let interactor = backendInteraction absInputFile configuredBackends
    swallowExitSuccess $
      runTCMPrettyErrors $
        runAgdaWithOptions interactor "agda" agdaOpts

    -- Create a map with the outputs for all formats
    contents <-
      forM formats $ \format -> do
        out <- guessOutputPath format opts'
        content <- T.readFile out
        return (format, content)

    return $ M.fromList contents


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
swallowExitSuccess act = handle handler act
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
  let replace = ICU.rtext libUrl <> "/$1.html$2"
  let fixExternalLink :: Url -> Url
      fixExternalLink url = ICU.replaceAll regex replace url
  return fixExternalLink

-- | An ICU regular expression which matches links to the Agda standard library.
reLinkToExternal :: FilePath -> IO ICU.Regex
reLinkToExternal libDir = do
  modNames <- allModules libDir
  let builtin  = "Agda\\.[A-Za-z\\.]+"
  let modPatns = T.replace "." "\\." <$> modNames
  let modPatn  = T.concat . L.intersperse "|" $ builtin : modPatns
  let hrefPatn = "(" <> modPatn <> ")\\.html(#[^\"^']+)?"
  return (ICU.regex [] hrefPatn)

-- | Gather all modules given a path.
allModules :: FilePath -> IO [Text]
allModules dir = do
  inputFiles <- find always (extension ==? ".agda") dir
  modules <- traverse (guessModuleName_ [dir]) inputFiles
  return modules


--------------------------------------------------------------------------------
-- Fix references to local Agda modules using YAML frontmatter
--------------------------------------------------------------------------------

-- | Create a function to fix URL references to local modules
prepareFixLocalLinksWithPermalink :: FilePath -> IO (Url -> Url)
prepareFixLocalLinksWithPermalink libDir = do

  -- Get all literate Agda files in 'libDir'
  inputFiles <- find always (fileName ~~? "*.lagda.md") libDir

  -- Get all permalinks and Agda module names from these files
  localLinkList <- forM inputFiles $ \inputFile -> do
    metadata <- readYamlFrontmatter inputFile
    permalink <- metadata ^. "permalink"
    moduleName <- guessModuleName_ [libDir] inputFile
    return (moduleName, permalink)

  let localLinks = M.fromList localLinkList

  -- Construct a function which looks up the URL in the map.
  let fixLocalLinkWithPermalink :: Url -> Url
      fixLocalLinkWithPermalink url = fromMaybe url $ do
        let (oldUrl, anchor) = T.breakOn "#" url
        let moduleName = T.replace ".html" "" oldUrl
        newUrl <- M.lookup moduleName localLinks
        return $ newUrl <> anchor

  return fixLocalLinkWithPermalink

--------------------------------------------------------------------------------
-- Construct an 'AgdaLib' value for the standard library
--------------------------------------------------------------------------------

-- | Check whether or not a given 'FilePath' is a copy of the standard library.
isStandardLibrary :: FilePath -> IO Bool
isStandardLibrary dir = System.doesFileExist $ dir </> "standard-library.agda-lib"

-- | The default file used to obtain the current Agda standard library version.
changelogName :: FilePath
changelogName = "CHANGELOG.md"

-- | Read the version information from the first line of 'CHANGELOG.md'.
getStandardLibraryVersion :: FilePath -> IO Text
getStandardLibraryVersion dir = do
  let pathToChangelog = dir </> changelogName
  correct <- System.doesFileExist pathToChangelog
  if not correct then
    error $ "Could not find " <> changelogName <> " in " <> dir
  else do
    changelog <- T.readFile pathToChangelog
    let verLine = head (T.lines changelog)
    ver <- liftMaybe ("Cannot read version from " <> pathToChangelog) $
      T.stripPrefix "Version " verLine
    return $ "v" <> T.strip ver

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
    printf "Found standard-library version %s\n" ver
    let stdlibUrl = "https://agda.github.io/agda-stdlib/" <> ver
    return AgdaLib
      { libDir = dir </> "src"
      , libUrl = Just stdlibUrl
      }

--------------------------------------------------------------------------------
-- Guess to which file Agda writes HTML and LaTeX output
--------------------------------------------------------------------------------

-- | Guess the path to which Agda writes the relevant output file.
guessOutputPath :: Format -> AgdaOpts -> IO FilePath
guessOutputPath Markdown AgdaOpts{..} = do
  moduleName <- guessModuleName_ (map libDir libraries) inputFile
  return $ tmpDir </> T.unpack moduleName <.> "md"
guessOutputPath LaTeX AgdaOpts{..} = do
  modulePath <- guessModulePath_ (map libDir libraries) inputFile
  return $ tmpDir </> replaceExtensions modulePath "tex"

-- | Guess the module name based on the filename and the include path.
guessModuleName :: [FilePath] -> FilePath -> Maybe Text
guessModuleName includePaths inputFile = pathToModule <$> guessModulePath includePaths inputFile
  where
    pathToModule fp = T.map sepToDot (T.pack $ dropExtensions fp)
      where
        sepToDot c = if c == '/' then '.' else c

-- | Variant of 'guessModuleName' which throws an error.
guessModuleName_ :: [FilePath] -> FilePath -> IO Text
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
