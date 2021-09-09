module PLFA.Build.Preprocess
  ( preprocessForHtml
  , preprocessForLaTeX
  ) where

import Data.Text.ICU qualified as ICU
import Data.Text.ICU.Replace qualified as ICU
import PLFA.Build.Prelude

--------------------------------------------------------------------------------
-- Preprocessing literate Agda files
--------------------------------------------------------------------------------

-- | Wrap literate Agda blocks in a raw HTML block.
preprocessForHtml :: Text -> Text
preprocessForHtml = ICU.replaceAll reCodeBlock "\n\n~~~{=html}\n```agda$1```\n\n~~~\n\n"

-- | Wrap literate Agda blocks in a raw LaTeX block.
preprocessForLaTeX :: Text -> Text
preprocessForLaTeX = ICU.replaceAll reCodeBlock "\n\n~~~{=latex}\n\\begin{code}$1\\end{code}\n\n~~~\n\n"

-- | Match a literate Agda block.
--
--   NOTE: This function assumes literate Agda is written using backtick code
--         blocks, as Agda does not supported tilde code blocks, and that the
--         code blocks are /tagged as Agda code/.
--
reCodeBlock :: ICU.Regex
reCodeBlock = ICU.regex [ICU.DotAll, ICU.Multiline] "^```\\s*agda\\s*$(.*?)^```\\s*$"
