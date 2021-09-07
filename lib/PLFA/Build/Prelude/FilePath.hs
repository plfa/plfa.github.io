module PLFA.Build.Prelude.FilePath
  ( removeFile_
  , dropPrefix
  , module Shake
  ) where

import Control.Exception (IOException, catch, handle)
import Control.Monad (when)
import Data.List (stripPrefix)
import Development.Shake.FilePath qualified as Shake
import System.FilePath
import System.Directory (Permissions(..), getPermissions, setPermissions, removeFile)
import System.IO.Error (isPermissionError)
import Text.Printf
import PLFA.Build.Prelude.Error

dropPrefix :: MonadFail m => FilePath -> FilePath -> m FilePath
dropPrefix prefixPath filePath = do
  path <- liftMaybe (printf "Cannot strip prefix '%s' from '%s'" prefixPath filePath) $
    splitDirectories prefixPath `stripPrefix` splitDirectories filePath
  return (joinPath path)

-- Taken from shake General.Extra

removeFile_ :: FilePath -> IO ()
removeFile_ fp =
  removeFile fp `catchIO` \e ->
      when (isPermissionError e) $ handleIO (\_ -> return ()) $ do
          perms <- getPermissions fp
          setPermissions fp perms{readable = True, searchable = True, writable = True}
          removeFile fp

catchIO :: IO a -> (IOException -> IO a) -> IO a
catchIO = catch

handleIO :: (IOException -> IO a) -> IO a -> IO a
handleIO = handle
