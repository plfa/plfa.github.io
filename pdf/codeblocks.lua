-- tested on pandoc 2.2.3.2
-- from agda doc:
-- Code blocks start with ``` or ```agda on its own line, and end with ```, also on its own line
function CodeBlock(elem)
  if #(elem.classes)==0 or elem.classes[1]=='agda' then 
    return pandoc.RawBlock('tex', '\\begin{fence}\n\\begin{code}\n' .. elem.text .. '\n\\end{code}\n\\end{fence}')
  else 
    return pandoc.RawBlock('tex', '\\begin{myDisplay}\n' .. elem.text .. '\n\\end{myDisplay}')
  end
end

