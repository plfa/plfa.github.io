--- include-files.lua – filter to include Markdown files
---
--- Copyright: © 2019–2020 Albert Krewinkel
--- Copyright: ©      2020 Michael Reed
--- License:   MIT – see LICENSE file for details
---
--- Created by Albert Krewinkel. Slightly modified by Michael Reed for use in
--- generating the EPUB for "Programming Language Foundations in Agda".
---
--- For documentation, see: https://github.com/pandoc/lua-filters/tree/master/include-files

-- pandoc's List type
local List = require 'pandoc.List'

--- Filter function for code blocks
function CodeBlock(cb)

  -- Ignore code blocks which are not of class "include".
  if not cb.classes:includes 'include' then
    return
  end

  -- Markdown is used if this is nil.
  local format = cb.attributes['format']
  local shift_heading_level_by =
    tonumber(cb.attributes['shift-heading-level-by'])

  local blocks = List:new()
  for line in cb.text:gmatch('[^\n]+') do
    if line:sub(1,2) ~= '//' then
      -- Read in the document at the file path specified by `line`.
      local fh = io.open(line)
      local doc = pandoc.read(fh:read '*a', format)
      blocks:extend(document.blocks)
      fh:close()
    end
  end
  return blocks
end

-- Apply a filter to a document.
function apply_filter(doc, filters)
  div = pandoc.Div(doc.blocks)
  for _, filter in pairs(filters) do
    if filter.Meta then
      filter.Meta(doc.meta)
    end
    div = pandoc.walk_block(div, filter)
  end
  return pandoc.Pandoc(div.content, doc.meta)
end
