function Link(ln)
  -- Remove link elements if their first child is a badge.
	if #ln.content > 0 and ln.content[1].t == "Image" then
    if string.find(ln.content[1].src, "https://img.shields.io/badge/", 1, true) then
      return pandoc.Null()
    end
	end
end
