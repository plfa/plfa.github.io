module PLFA.Build.Preprocess
  ( preprocessForHtml
  , preprocessForLaTeX
  , postprocessHtml5
  ) where

import Data.String (IsString (fromString))
import Data.Text.ICU qualified as ICU
import Data.Text.ICU.Replace qualified as ICU
import PLFA.Build.Prelude
import Text.Printf (printf)

--------------------------------------------------------------------------------
-- Preprocessing literate Agda files
--------------------------------------------------------------------------------

-- | Removes closing tags for '<img>' and '<input>' tags.
postprocessHtml5 :: Text -> Text
postprocessHtml5 = ICU.replaceAll reSelfClosing "/>"
  where
    reSelfClosing :: ICU.Regex
    reSelfClosing =
      fromString $ foldr1 (>|<) $ map (printf "(></%s>)") selfClosingTags

    (>|<) :: String -> String -> String
    s1 >|< s2 = s1 <> "|" <> s2

    selfClosingTags :: [String]
    selfClosingTags =
      ["area", "base", "br", "col", "embed", "hr", "img", "input", "link",
       "meta", "param", "source", "track", "wbr", "command", "keygen", "menuitem"]


-- | Wrap literate Agda blocks in a raw Html block.
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
