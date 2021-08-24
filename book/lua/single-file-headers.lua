-- Performs the following transformations on Header identifiers:
--
--     Case 1:
--         /title/: "Some Title"
--         /permalink/: /Title/ -> # Some Title {#Title}
--
--     Case 2:
--         ## Subsection Title {name=more-stuff} -> ## Subsection Title {#Title-more-stuff}
--

local identifier = nil
local title = nil

local function get_meta_info(meta)

	-- Get the title.
  if meta['title'] then
    title = meta['title']
  elseif meta['default-title'] then
    title = meta['default-title']
  end
  title = pandoc.utils.stringify(title)

  -- Get the identifier.
  if meta['permalink'] then
    identifier = meta['permalink'][1].c:match("^/(%w+)/$")
  elseif meta['title'] then
    identifier = meta['title']
  elseif meta['default-title'] then
    identifier = meta['default-title']
  end
  identifier = string.lower(pandoc.utils.stringify(identifier))
end

local function insert_title(doc)
	-- Insert title in front of the blocks
  if title then
    header = pandoc.Header(1,title)
    header.identifier = identifier
    table.insert(doc.blocks,1,header)
  end
	return doc
end

local function change_identifier(elem)
	-- Change header identifier based on metadata
	if elem.t == "Header" and elem.attributes.name then
		elem.identifier = identifier .. "-" .. elem.attributes.name
	end
	return elem
end

return {
  {Meta = get_meta_info},
  {Header = change_identifier},
  {Pandoc = insert_title}
}
