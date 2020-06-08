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

--- Shift headings in block list by given number
function shift_headings(blocks, shift_by)
  if not shift_by then
    return blocks
  end

  local shift_headings_filter = {
    Header = function (header)
      header.level = header.level + shift_by
      return header
    end
  }

  return pandoc.walk_block(pandoc.Div(blocks), shift_headings_filter).content
end

--- Filter function for code blocks
function CodeBlock(cb)
  -- ignore code blocks which are not of class "include".
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
      local document = pandoc.read(fh:read '*a', format)
      -- Before shifting headings, add a title heading at the beginning of the chapter.
      local heading = pandoc.Header(1, pandoc.Str(pandoc.utils.stringify(document.meta.title)))
      document.blocks:insert(1, heading)
      -- Shift all headings by the user-specified amount, which is 0 by default.
      local chapter = shift_headings(document.blocks, shift_heading_level_by)
      -- Concatenate the chapter blocks (discarding the metadata) to the current document.
      blocks:extend(chapter)
      fh:close()
    end
  end
  return blocks
end
