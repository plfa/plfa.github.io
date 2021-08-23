function remove_badges(ln)
  -- Remove link elements if their first child is a badge.
	if #ln.content > 0 and ln.content[1].t == "Image" then
    if string.match(ln.content[1].src, 'https://img%.shields%.io/badge/') then
      return pandoc.Null()
    end
	end
end

return {
  { Link = remove_badges }
}
