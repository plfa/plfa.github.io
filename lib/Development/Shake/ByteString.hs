module Development.Shake.ByteString
  ( BS.ByteString
  , writeFile'
  ) where

import Data.ByteString qualified as BS
import Development.Shake (Action, liftIO)
import Development.Shake.FilePath (takeDirectory)
import General.Extra
import System.Directory

writeFile' :: FilePath -> BS.ByteString -> Action ()
writeFile' fp content = liftIO $ do
  createDirectoryIfMissing True (takeDirectory fp)
  removeFile_ fp
  BS.writeFile fp content
