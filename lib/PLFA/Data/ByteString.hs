module PLFA.Data.ByteString
  ( BS.ByteString
  , writeFile
  ) where

import Prelude hiding (writeFile)
import Data.ByteString qualified as BS
import Development.Shake
import Development.Shake.FilePath
import General.Extra
import System.Directory

writeFile :: FilePath -> BS.ByteString -> Action ()
writeFile fp content = liftIO $ do
  createDirectoryIfMissing True (takeDirectory fp)
  removeFile_ fp
  BS.writeFile fp content
