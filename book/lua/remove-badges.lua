local badge_url = nil

local function remove_badges(ln)
  -- Remove link elements if their first child is a badge.
	if #ln.content > 0 and ln.content[1].t == "Image" then
    if string.find(ln.content[1].src, badge_url, 1, true) then
      return pandoc.Null()
    end
	end
end

local function get_badge_url(meta)
  if meta['badge-url'] then
    badge_url = pandoc.utils.stringify(meta['badge-url'])
  end
end


return {
  { Meta = get_badge_url },
  { Link = remove_badges }
}
