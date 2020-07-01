local yaml = require 'tinyyaml'
local liquid = require 'liquid'

-- Given a file name, return its file descriptor.
-- Throws an error on failure.
local function errOpen (fname, mode)
    local fd = io.open(fname, mode)
    if fd == nil then
        error('could not open file: ' .. fname)
    end
    return fd
end

-- Given a file name and some data, overwrite the file with the data.
-- Throws an error on failure.
local function errWrite (fname, data)
    local fd = errOpen(fname, 'w')
    local status, errstr = fd:write(data)
    if status == nil then
        error(fname .. ': ' .. errstr)
    end
end

-- Given a file name, return that file's entire contents.
-- Throws an error on failure.
local function errReadAll (fname)
    local data = errOpen(fname, 'r'):read('a')
    if data == nil then
        error('could not read from open file: ' .. fname)
    end
    return data
end


-- We must have exactly three arguments.
if #arg ~= 3 then
    print('usage: ' .. arg[0] .. ' [yaml_file] [markdown_in_file] [markdown_out_file]')
    os.exit(1)
end

-- 1. Read YAML metadata from file, which we nest under the key 'site'.
local metadata = { ['site'] = yaml.parse(errReadAll(arg[1])) }

-- 2. Read markdown document from file.
local document = errReadAll(arg[2])

-- 3. Render the markdown document with the YAML metadata as context.
local template = liquid.Template:parse(document)
local result = template:render(liquid.InterpreterContext:new(metadata))

-- 4. Write rendered document to output file.
errWrite(arg[3], result)