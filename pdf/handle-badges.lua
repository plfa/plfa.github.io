function Link(el)
	if el.content[1].t == "Image" then
		return pandoc.RawInline('markdown','')
	end
end