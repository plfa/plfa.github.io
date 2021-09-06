module Development.Shake.Text
  ( T.Text
  , writeFile'
  ) where

import Data.Text qualified as T
import Data.Text.IO qualified as T
import Development.Shake (Action, liftIO)
import Development.Shake.FilePath (takeDirectory)
import General.Extra
import System.Directory

writeFile' :: FilePath -> T.Text -> Action ()
writeFile' fp content = liftIO $ do
  createDirectoryIfMissing True (takeDirectory fp)
  removeFile_ fp
  T.writeFile fp content
