module PLFA.Data.Text
  ( T.Text
  , writeFile
  ) where

import Prelude hiding (writeFile)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Development.Shake
import Development.Shake.FilePath
import General.Extra
import System.Directory

writeFile :: FilePath -> T.Text -> Action ()
writeFile fp content = liftIO $ do
  createDirectoryIfMissing True (takeDirectory fp)
  removeFile_ fp
  T.writeFile fp content
