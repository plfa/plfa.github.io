local function typeset_codeblock(cb)
  -- If a code block has class Agda or its class is omitted, format it as...
  --
  --   \begin{agda}\begin{code} .. \end{agda}\end{code}
  --
  -- ...otherwise, format it as...
  --
  --   \begin{pre} .. \end{pre}
  --
  -- Any file which is not checked by Agda must have its code blocks typeset in the latter style.
  -- Specify these files via the UNCHECKED_FILES environment variable.
  if is_checked() then
    if #(cb.classes) == 0 or cb.classes[1] == 'agda' then
      return pandoc.RawBlock('tex', '\\begin{agda}\n\\begin{code}\n' .. cb.text .. '\n\\end{code}\n\\end{agda}')
    end
  end
  return pandoc.RawBlock('tex', '\\begin{pre}\n' .. cb.text .. '\n\\end{pre}')
end

-- Set of unchecked files, where the names of unchecked files are stored in the table keys.
local UNCHECKED_FILES = nil

-- Return whether the current file is checked by Agda, given by the UNCHECKED_FILES environment variable.
function is_checked()

  -- Initialise the table.
  if UNCHECKED_FILES == nil then
    UNCHECKED_FILES = {}
    for unchecked_file in string.gmatch(pandoc.system.environment().UNCHECKED_FILES, "([^ ]+)") do
      UNCHECKED_FILES[unchecked_file] = true
    end
  end

  -- Check if any of our input files is an unchecked file.
  for _, input_file in pairs(PANDOC_STATE.input_files) do
    if UNCHECKED_FILES[input_file] then
      if #PANDOC_STATE.input_files > 1 then
        error("Cannot handle multiple unchecked input files.")
      else
        return false
      end
    end
  end
  return true
end

return {
  { CodeBlock = typeset_codeblock }
}
