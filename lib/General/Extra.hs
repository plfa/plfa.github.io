module General.Extra
  ( removeFile_
  ) where

import Control.Exception (IOException, catch, handle)
import Control.Monad (when)
import System.Directory (Permissions(..), getPermissions, setPermissions, removeFile)
import System.IO.Error (isPermissionError)

-- Taken from shake hidden module General.Extra

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
