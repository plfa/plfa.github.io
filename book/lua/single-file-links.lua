-- from https://github.com/plfa/plfa.github.io/blob/dev/epub/rewrite-links.lua
-- Performs the following transformations on Link targets:
--
--     Case 1:
--         [text](/chapter/#more-stuff) -> [text](#chapter-more-stuff)
--
--     Case 2:
--         [text](/chapter/)            -> [text](#chapter)
--
-- All other Links are ignored.
function Link(el)
	local n
	-- Case 1:
	el.target, n = el.target:gsub("^/(%w+)/#([%w-]+)$", "#%1-%2")
  -- Case 2:
  if n == 0 then
	  el.target, n = el.target:gsub("^/(%w+)/$", "#%1")
  end
  -- If either Case 1 or Case 2, lowercase target:
  if n ~= 0 then
    el.target = string.lower(el.target)
  end
	return el
end
