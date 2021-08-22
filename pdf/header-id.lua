-- Performs the following transformations on Header identifiers:
--
--     Case 1:
--         /title/: "Some Title"
--         /permalink/: /Title/ -> # Some Title {#Title}
--     Case 2:
--         ## Subsection Title {name=more-stuff} -> ## Subsection Title {#Title-more-stuff}

local identifier = nil
local title = nil

function get_identifier(meta)
	-- get title identifier from permalinks
	for k,v in pairs(meta) do 
		if k == "title" then
			title = {table.unpack(v)}
		end
		if k == "permalink" then
			-- print(k,type(v[1].c))
			-- set lower case permalink as identifier
			identifier = v[1].c:match("^/(%w+)/$")
		end
	end
end

function insert_title(doc)
	-- insert title in front of the blocks
	-- print(doc.blocks)
	header = pandoc.Header(1,title)
	header.identifier = identifier
	-- print("header:" ,header.content)
	table.insert(doc.blocks,1,header)
	return doc
end	

function change_identifier(elem)
	-- change header identifier based on metadata
		
	local name = elem.attributes["name"]
	if elem.t == "Header" and name then 
		-- can get labels
		-- print(name, elem.identifier)
		elem.identifier = identifier .. "-" .. name
		-- print(elem.identifier)
	end
	return elem
end

return {{Meta=get_identifier}, {Header=change_identifier}, {Pandoc = insert_title}}