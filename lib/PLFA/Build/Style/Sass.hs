module PLFA.Build.Style.Sass
  ( -- * Compile Sass with hsass
    compileSass
  , compileSassWith
  , SassOptions (..)
  ) where

import Data.Bitraversable (Bitraversable (..))
import Data.Default.Class (Default(..))
import Development.Shake
import Text.Sass (SassOptions(..))
import Text.Sass qualified as Sass
import PLFA.Build.Prelude

-- * Sass

-- | Compile Sass.
compileSass :: FilePath -> Action Text
compileSass = compileSassWith def

-- | Compile Sass with options.
compileSassWith :: SassOptions -> FilePath -> Action Text
compileSassWith opts filePath = do

  -- Compile `filePath` from Sass/SCSS to CSS
  resultOrError <- liftIO $ Sass.compileFile filePath opts
  resultOrErrorMsg <- liftIO $ bitraverse Sass.errorMessage return resultOrError
  result <- liftIO (liftEither id resultOrErrorMsg)

  -- Inform Shake of the dependencies used during compilation
  --
  -- NOTE: not sure if informing Shake post-fact is of any use?
  --
  includes <- liftIO $ Sass.resultIncludes result
  need includes

  -- Convert the resulting ByteString to Text
  liftIO $ toText (Sass.resultString result)
