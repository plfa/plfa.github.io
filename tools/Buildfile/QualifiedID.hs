module Buildfile.QualifiedID where

import Text.HTML.TagSoup
import Data.Text (Text)

-- TODO: prefix all id attributes in Agda code with "agda:<modulename>:"
-- TODO: unless the id is numeric

isAgdaOpen :: Tag Text -> Bool
isAgdaOpen (TagOpen tag attr) = tag == "pre" && ("class", "agda") `elem` attr
isAgdaOpen _ = False

isAgdaClose :: Tag Text -> Bool
isAgdaClose = isTagCloseName "pre"

