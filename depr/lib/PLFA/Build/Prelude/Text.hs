module PLFA.Build.Prelude.Text
  ( T.Text
  , readFile'
  , writeFile'
  ) where

import Data.Text qualified as T
import Data.Text.IO qualified as T
import Development.Shake (Action, liftIO, need)
import PLFA.Build.Prelude.FilePath
import System.Directory

readFile' :: FilePath -> Action T.Text
readFile' fp = need [fp] >> liftIO (T.readFile fp)

writeFile' :: FilePath -> T.Text -> Action ()
writeFile' fp content = liftIO $ do
  createDirectoryIfMissing True (takeDirectory fp)
  removeFile_ fp
  T.writeFile fp content
