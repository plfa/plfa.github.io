{-# OPTIONS_GHC -fno-warn-orphans #-}

module PLFA.CSS
  ( -- * Compile Sass with hsass
    compileSass
  , compileSassWith
  , SassOptions (..)
    -- * Minify CSS with hasmin
  , minifyCSS
  , minifyCSSWith
  , Hasmin.Config (..)
  , Hasmin.ColorSettings (..)
  , Hasmin.DimensionSettings (..)
  , Hasmin.GradientSettings (..)
  , Hasmin.FontWeightSettings (..)
  , Hasmin.LetterCase (..)
  , Hasmin.SortingMethod (..)
  , Hasmin.RulesMergeSettings (..)
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
import Hasmin qualified


-- * Sass

-- | Compile Sass.
compileSass :: FilePath -> Action Text
compileSass = compileSassWith def

-- | Compile Sass with options.
compileSassWith :: SassOptions -> FilePath -> Action Text
compileSassWith opts filePath = do

  -- Compile `filePath` from Sass/SCSS to CSS
  resultOrError <- liftIO $ Sass.compileFile filePath opts
  result <- liftEither showSassError resultOrError

  -- Inform Shake of the dependencies used during compilation
  --
  -- NOTE: not sure if informing Shake post-fact is of any use?
  --
  includes <- liftIO $ Sass.resultIncludes result
  need includes

  -- Convert the resulting ByteString to Text
  liftIO $ toText (Sass.resultString result)


-- * CSS

-- | Minify CSS using 'Hasmin'.
minifyCSS :: Text -> Action Text
minifyCSS = minifyCSSWith def

-- | Minify CSS with options.
minifyCSSWith :: Hasmin.Config -> Text -> Action Text
minifyCSSWith opts css =
  liftEither return (Hasmin.minifyCSSWith opts css)

instance Default Hasmin.Config where
  def = Hasmin.defaultConfig



-- * Helper functions

showSassError :: SassError -> Action String
showSassError e = liftIO $ Sass.errorMessage e

liftEither :: MonadFail m => (e -> m String) -> Either e a -> m a
liftEither pretty (Left  e) = fail =<< pretty e
liftEither _      (Right a) = return a

toText :: BS.ByteString -> IO Text
toText bs = do
  let lbs = LBS.fromChunks [bs]
  let maybeEncoding = Codec.detectEncodingName lbs
  let encoding = fromMaybe "" maybeEncoding
  converter <- Convert.open encoding (Just True)
  return $ Convert.toUnicode converter bs
