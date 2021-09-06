module PLFA.Util
  ( Url
  , removeFile_
  , liftExcept
  , liftEither
  , liftMaybe
  , dropPrefix
  ) where

import Control.Exception (IOException, catch, handle)
import Control.Monad (when)
import Control.Monad.Except (Except, runExcept)
import Data.List qualified as L
import Development.Shake.FilePath
import System.Directory (Permissions(..), getPermissions, setPermissions, removeFile)
import System.IO.Error (isPermissionError)
import Text.Printf

type Url = String

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

liftExcept :: MonadFail m => (e -> String) -> Except e a -> m a
liftExcept pretty m = liftEither pretty (runExcept m)

liftEither :: MonadFail m => (e -> String) -> Either e a -> m a
liftEither pretty (Left e) = fail (pretty e)
liftEither _      (Right a) = return a

liftMaybe :: MonadFail m => String -> Maybe a -> m a
liftMaybe errorMessage Nothing  = fail errorMessage
liftMaybe _            (Just a) = return a

dropPrefix :: MonadFail m => FilePath -> FilePath -> m FilePath
dropPrefix prefixPath filePath = do
  path <- liftMaybe (printf "Cannot strip prefix '%s' from '%s'" prefixPath filePath) $
    L.stripPrefix (splitDirectories prefixPath) (splitDirectories filePath)
  return (joinPath path)
