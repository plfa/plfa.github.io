local yaml = require 'tinyyaml'
local liquid = require 'liquid'

if #arg ~= 2 then
    print('usage: ' .. arg[0] .. ' [yaml_file] [markdown_file]')
    os.exit(1)
end

-- 1. Read YAML metadata from file, which we nest under the key 'site'.
local metadata = { ['site'] = yaml.parse(io.open(arg[1]):read('a')) }

-- 2. Read markdown document from file.
local document = io.open(arg[2]):read('a')

-- 3. Render the markdown document with the YAML metadata as context.
local template = liquid.Template:parse(document)
local result = template:render(liquid.InterpreterContext:new(metadata))

print(result)