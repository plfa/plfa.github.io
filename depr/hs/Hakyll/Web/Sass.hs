--------------------------------------------------------------------------------
-- Compile SASS and SCSS
--------------------------------------------------------------------------------

module Hakyll.Web.Sass
  ( sassCompilerWith
  , SassOptions(..)
  , defaultSassOptions
  ) where

import           Hakyll
import           Text.Sass (SassOptions(..), defaultSassOptions)
import qualified Text.Sass as Sass

sassCompilerWith :: SassOptions -> Compiler (Item String)
sassCompilerWith opts = getResourceBody >>= withItemBody renderSass
  where
    renderSass :: String -> Compiler String
    renderSass sass = unsafeCompiler $ do
      cssOrErr <- Sass.compileString sass opts
      case cssOrErr of
        Left  err -> Sass.errorMessage err
        Right css -> return (compressCss css)

