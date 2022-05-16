module PLFA.Build.Prelude.ByteString
  ( toText
  , toTextLazy
  ) where

import Codec.Text.Detect qualified as Codec
import Data.ByteString qualified as B
import Data.ByteString.Lazy qualified as BL
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text.ICU.Convert qualified as Convert

toText :: B.ByteString -> IO Text
toText bs = toTextLazy (BL.fromStrict bs)

toTextLazy :: BL.ByteString -> IO Text
toTextLazy lbs = do
  let maybeEncoding = Codec.detectEncodingName lbs
  let encoding = fromMaybe "" maybeEncoding
  converter <- Convert.open encoding (Just True)
  return $ Convert.toUnicode converter (BL.toStrict lbs)
