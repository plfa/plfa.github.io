{-# LANGUAGE FlexibleContexts #-}

module PLFA.Build.Pandoc
  ( module Export,
    Template,
    runPandocIO,
    compileTemplate,
    renderTemplate
  ) where

import Control.Exception (displayException)
import Data.Aeson.Types (Value (..))
import PLFA.Build.Prelude
import PLFA.Build.Metadata
import Text.DocLayout qualified as Doc (render)
import Text.Pandoc as Export hiding (Format, Template, getTemplate, compileTemplate, renderTemplate)
import Text.Pandoc.Writers.HTML as Export (writeHtmlStringForEPUB)
import Text.Pandoc.Templates qualified as Template

type Template = Template.Template Text

runPandocIO :: PandocIO a -> Action a
runPandocIO act = do
  resultOrError <- liftIO (Export.runIO act)
  liftEither displayException resultOrError

compileTemplate :: FilePath -> Action Template
compileTemplate fp = do
  content <- runPandocIO (Template.getTemplate fp)
  tplOrError <- liftIO (Template.compileTemplate fp content)
  liftEither id tplOrError

renderTemplate :: Template -> Metadata -> Text
renderTemplate template (Metadata obj) =
  Doc.render Nothing (Template.renderTemplate template (Object obj))
