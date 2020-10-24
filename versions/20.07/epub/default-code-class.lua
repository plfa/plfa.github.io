-- Source:
-- https://github.com/jgm/pandoc/issues/2104#issuecomment-595878750
--
-- Assign a code class to all code blocks lacking one.  Unlike the
-- command-line flag "--indented-code-classes", which only applies
-- to indented code blocks, this lua filter applies to all inline
-- code elements, including fenced code blocks.

local default_code_classes = {}

function add_default_code_class(el)
  if #(el.classes) == 0 then
    el.classes = default_code_classes
    return el
  end
end

function get_default_code_class(meta)
  if meta['default-code-class'] then
    default_code_classes = {pandoc.utils.stringify(meta['default-code-class'])}
  end
end

return {{Meta = get_default_code_class},
        {Code = add_default_code_class},
        {CodeBlock = add_default_code_class}}
