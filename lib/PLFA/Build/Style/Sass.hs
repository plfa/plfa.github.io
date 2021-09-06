module PLFA.Build.Style.Sass
  ( -- * Compile Sass with hsass
    compileSass
  , compileSassWith
  , SassOptions (..)
  ) where

import Codec.Text.Detect qualified as Codec
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as LBS
import Data.Default.Class (Default(..))
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text.ICU.Convert qualified as Convert
import Development.Shake
import Text.Sass (SassError, SassOptions(..))
import Text.Sass qualified as Sass


-- * Sass

-- | Compile Sass.
compileSass :: FilePath -> Action Text
compileSass = compileSassWith def

-- | Compile Sass with options.
compileSassWith :: SassOptions -> FilePath -> Action Text
compileSassWith opts filePath = do

  -- Compile `filePath` from Sass/SCSS to CSS
  resultOrError <- liftIO $ Sass.compileFile filePath opts
  result <- liftIO (liftEither resultOrError)

  -- Inform Shake of the dependencies used during compilation
  --
  -- NOTE: not sure if informing Shake post-fact is of any use?
  --
  includes <- liftIO $ Sass.resultIncludes result
  need includes

  -- Convert the resulting ByteString to Text
  liftIO $ toText (Sass.resultString result)


-- * Helper functions

liftEither :: Either SassError a -> IO a
liftEither (Left  e) = fail =<< Sass.errorMessage e
liftEither (Right a) = return a

toText :: BS.ByteString -> IO Text
toText bs = do
  let lbs = LBS.fromChunks [bs]
  let maybeEncoding = Codec.detectEncodingName lbs
  let encoding = fromMaybe "" maybeEncoding
  converter <- Convert.open encoding (Just True)
  return $ Convert.toUnicode converter bs
