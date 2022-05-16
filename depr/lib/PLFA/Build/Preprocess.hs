module PLFA.Build.Preprocess
  ( preprocessForHtml
  , preprocessForLaTeX
  , postprocessHtml5
  , sanitizeForEpub
  , shiftHeaders
  ) where

import Data.String (IsString (fromString))
import Data.Text.ICU qualified as ICU
import Data.Text.ICU.Replace qualified as ICU
import PLFA.Build.Prelude
import Text.HTML.TagSoup qualified as TS
import Text.Printf (printf)


-- | Shift all Markdown headers by one.
shiftHeaders :: Text -> Text
shiftHeaders body = ICU.replaceAll reHeader "#$1" body
  where
    reHeader = ICU.regex [ICU.Multiline] "^(#+)"

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


sanitizeForEpub :: Text -> Text
sanitizeForEpub = ICU.replaceAll reRawBlock (ICU.rtfn replace)
  where
    replace :: ICU.Match -> Text
    replace m = case ICU.group 1 m of
      Nothing -> error "You got it wrong you silly"
      Just cb -> "\n\n~~~{=html}\n" <> sanitizeRawBlock cb <> "\n\n~~~\n\n"

-- | Remove everything except for classes from Html.
sanitizeRawBlock :: Text -> Text
sanitizeRawBlock = TS.renderTags . map tag . TS.parseTags
  where
    tag (TS.TagOpen s a) = TS.TagOpen s $ filter (\(k,_) -> k == "class") a
    tag x                = x

-- | Match a raw Html block.
reRawBlock :: ICU.Regex
reRawBlock = ICU.regex [ICU.DotAll, ICU.Multiline] "^~~~\\{=html\\}\\s*$(.*?)^~~~\\s*$"
