{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

module PLFA.Build.Agda
  ( Format (..)
  , AgdaOpts (..)
  , LibName
  , AgdaLib (..)
  , pattern AgdaLib
  , libIncludes
  , libName
  , libFile
  , libDepends
  , libPragmas
  , libUrl
  , readAgdaLib'
  , readAgdaLib
  , highlightAgdaWith
  , standardLibraryAgdaLib
  , prepareFixLinks
  , prepareFixExternalLinks
  , prepareFixLocalLinksWithPermalink
  ) where

import Agda.Main
import Agda.Compiler.Backend (Backend, parseBackendOptions, backendInteraction)
import Agda.Interaction.Options as Agda (defaultOptions)
import Agda.Interaction.Library.Base (LibName, AgdaLibFile (..))
import Agda.Interaction.Library.Parse (runP, parseLibFile)
import Agda.Interaction.Highlighting.HTML (htmlBackend)
import Agda.Interaction.Highlighting.LaTeX (latexBackend)
import Agda.Utils.FileName (absolute)
import Control.Exception (throwIO, handle)
import Control.Monad (forM)
import Data.Aeson.Types
import Data.Default.Class (Default (..))
import Data.List qualified as L
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe
import Data.Monoid (Endo(..))
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Text.ICU qualified as ICU
import Data.Text.ICU.Replace qualified as ICU
import System.Exit
import System.Directory qualified as System (doesFileExist)
import System.IO.Temp (withTempDirectory, getCanonicalTemporaryDirectory)

import PLFA.Build.Metadata (readYamlFrontmatter, (^.))
import PLFA.Build.Prelude

--------------------------------------------------------------------------------
-- Compile literate Agda to Markdown/HTML or LaTeX
--------------------------------------------------------------------------------

data Format
  = Markdown
  | LaTeX
  deriving (Eq, Ord)

-- | Extend Agda's 'AgdaLibFile' with optional URLs.
data AgdaLib = AgdaLibExt AgdaLibFile (Maybe Url)

-- | A record pattern synonym for Agda library files.
pattern AgdaLib ::  LibName -> FilePath -> [FilePath] -> [LibName] -> [String] -> Maybe Url -> AgdaLib
pattern AgdaLib{libName, libFile, libIncludes, libDepends, libPragmas, libUrl} =
  AgdaLibExt (AgdaLibFile libName libFile libIncludes libDepends libPragmas) libUrl

data AgdaOpts = AgdaOpts
  { formats       :: [Format],
    tmpDir        :: FilePath,
    librariesFile :: Maybe FilePath,
    libraries     :: [AgdaLib],
    inputFile     :: FilePath
  }

instance Default AgdaOpts where
  def = AgdaOpts
        { formats       = error "AgdaOpts: please specify at least one format",
          tmpDir        = "",
          librariesFile = Nothing,
          libraries     = [],
          inputFile     = error "AgdaOpts: please specify input file"
        }

-- | Highlight Agda code embedded in Markdown or LaTeX.
highlightAgdaWith :: AgdaOpts -> Action (Map Format Text)
highlightAgdaWith opts@AgdaOpts{..} = liftIO $ do

  -- Create a temporary directory
  tmpParent <- getTemporaryDirectory opts
  withTempDirectory tmpParent "agda" $ \tmpDir' -> do
    let optsWithTmpDir = opts { tmpDir = tmpDir' }

    -- Call Agda with the appropriate options and backend
    let backends = map getBackend formats
    (configuredBackends, agdaOpts) <- liftExcept id $
      parseBackendOptions backends (buildArgs optsWithTmpDir) Agda.defaultOptions
    absInputFile <- absolute inputFile
    let interactor = backendInteraction absInputFile configuredBackends
    swallowExitSuccess $
      runTCMPrettyErrors $
        runAgdaWithOptions interactor "agda" agdaOpts

    -- Create a map with the outputs for all formats
    contents <-
      forM formats $ \format -> do
        out <- guessOutputPath format optsWithTmpDir
        content <- T.readFile out
        return (format, content)

    return $ M.fromList contents


-- | Construct the arguments for Agda based on the options passed.
buildArgs :: AgdaOpts -> [String]
buildArgs AgdaOpts{..} = mconcat
  [ [ "--verbose=0" ],
    mconcat [ formatArgs format | format <- formats ],
    [ "--no-default-libraries" ],
    [ "--library-file=" <> file | file <- maybeToList librariesFile ],
    [ "--library=" <> libName lib | lib <- libraries ]
  ]
  where
    formatArgs :: Format -> [String]
    formatArgs Markdown = [ "--html" , "--html-dir=" <> tmpDir , "--html-highlight=code" ]
    formatArgs LaTeX    = [ "--latex" , "--latex-dir=" <> tmpDir ]


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
prepareFixLinks agdaLibs = do
  fixLinkFuns <- sequence
    [ prepareFixLinks1 agdaLib libDir
    | agdaLib <- agdaLibs,
      libDir <- libIncludes agdaLib
    ]
  return $ appEndo $ mconcat fixLinkFuns
  where
    prepareFixLinks1 :: AgdaLib -> FilePath -> IO (Endo Url)
    prepareFixLinks1 AgdaLib{..} libDir =
      case libUrl of
        Nothing     -> Endo <$> prepareFixLocalLinksWithPermalink libDir
        Just libUrl -> Endo <$> prepareFixExternalLinks libUrl libDir


--------------------------------------------------------------------------------
-- Fix references to external Agda modules using a canonical URL
--------------------------------------------------------------------------------

-- | Prepare a function which fixes references to the standard library,
--   given the include path.
prepareFixExternalLinks :: Url -> FilePath -> IO (Url -> Url)
prepareFixExternalLinks libUrl libDir = do
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

  -- Get all literate Agda files in '$libDir'
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

-- | Read the version information from the first line of 'CHANGELOG.md'.
getStandardLibraryVersion :: FilePath -> IO Text
getStandardLibraryVersion dir = do
  --
  -- NOTE: Version detection depends on the fact that the standard library
  --       maintains a CHANGELOG.md file which always opens with its version.
  --
  let changelog = dir </> "CHANGELOG.md"
  correct <- System.doesFileExist changelog
  if not correct then
    error $ "Could not find " <> changelog
  else do
    changelogContents <- T.readFile changelog
    let verLine = head (T.lines changelogContents)
    ver <- liftMaybe ("Cannot read version from " <> changelog) $
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
  let agdaLibFile = dir </> "standard-library.agda-lib"
  correct <- System.doesFileExist agdaLibFile
  if not correct then
    error $ "Could not find standard library at " <> dir
  else do
    ver <- getStandardLibraryVersion dir
    putStrLn $ "Found standard-library version " <> T.unpack ver
    agdaLib <- readAgdaLib agdaLibFile
    let stdlibUrl = "https://agda.github.io/agda-stdlib/" <> ver
    return agdaLib { libUrl = Just stdlibUrl }


--------------------------------------------------------------------------------
-- Guess to which file Agda writes HTML and LaTeX output
--------------------------------------------------------------------------------

-- | Guess the path to which Agda writes the relevant output file.
guessOutputPath :: Format -> AgdaOpts -> IO FilePath
guessOutputPath Markdown AgdaOpts{..} = do
  moduleName <- guessModuleName_ (concatMap libIncludes libraries) inputFile
  return $ tmpDir </> T.unpack moduleName <.> "md"
guessOutputPath LaTeX AgdaOpts{..} = do
  modulePath <- guessModulePath_ (concatMap libIncludes libraries) inputFile
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
  listToMaybe $ catMaybes $ [ stripPrefix includePath inputFile | includePath <- includePaths ]
  where
    stripPrefix fp1 fp2 =
      joinPath <$> L.stripPrefix (splitDirectories fp1) (splitDirectories fp2)

-- | Variant of 'guessModulePath' which throws an error.
guessModulePath_ :: [FilePath] -> FilePath -> IO FilePath
guessModulePath_ includePaths inputFile =
  liftMaybe ("Could not guess module path for " <> inputFile) $
    guessModulePath includePaths inputFile

--------------------------------------------------------------------------------
-- Read .agda-lib files
--------------------------------------------------------------------------------

readAgdaLib' :: FilePath -> Action AgdaLib
readAgdaLib' inputFile = liftIO $ readAgdaLib inputFile

readAgdaLib :: FilePath -> IO AgdaLib
readAgdaLib inputFile = do
  agdaLibFileP <- parseLibFile inputFile
  let (agdaLibOrError, _warnings) = runP agdaLibFileP
  agdaLibFile <- liftEither id agdaLibOrError
  return $ AgdaLibExt agdaLibFile
    { _libFile     = normalise (_libFile agdaLibFile),
      _libIncludes = map normalise (_libIncludes agdaLibFile)
    } Nothing

instance Eq AgdaLib where
  lib1 == lib2 = libName lib1 == libName lib2

instance ToJSON AgdaLib where
  toJSON agdaLib =
    object [ "name"    .= libName agdaLib
           , "file"    .= libFile agdaLib
           , "depend"  .= libDepends agdaLib
           , "include" .= libIncludes agdaLib
           , "pragmas" .= libPragmas agdaLib
           , "url"     .= libUrl agdaLib
           ]

--------------------------------------------------------------------------------
-- Temporary directories
--------------------------------------------------------------------------------

getTemporaryDirectory :: AgdaOpts -> IO FilePath
getTemporaryDirectory AgdaOpts{..}
  | null tmpDir = getCanonicalTemporaryDirectory
  | otherwise   = return tmpDir
