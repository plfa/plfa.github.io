--------------------------------------------------------------------------------
-- Compile SASS and SCSS
--------------------------------------------------------------------------------

module PLFA.Sass (sassCompiler, sassCompilerWith, defaultSassOptions) where

import           Hakyll
import           Text.Sass (SassOptions(..))
import qualified Text.Sass as Sass

sassCompiler :: Compiler (Item String)
sassCompiler = sassCompilerWith defaultSassOptions

sassCompilerWith :: SassOptions -> Compiler (Item String)
sassCompilerWith opts = cached "sass" $ getResourceBody >>= withItemBody renderSass
  where
    renderSass :: String -> Compiler String
    renderSass sass = unsafeCompiler $ do
      cssOrErr <- Sass.compileString sass opts
      case cssOrErr of
        Left  err -> Sass.errorMessage err
        Right css -> return (compressCss css)

defaultSassOptions :: SassOptions
defaultSassOptions = Sass.defaultSassOptions
  { sassIncludePaths = Just ["css"]
  }
