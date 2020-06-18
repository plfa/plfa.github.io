local currentChapter = nil

-- Reassigns identifiers for all all Headers level 2 and higher. Level 2 Headers
-- correspond to chapters, and are identified by the first word in their content
-- field. Headers of level more than 2 are identified by "#<chapter>-<anchor>",
-- where "<chapter>" is the identifier of the chapter this header is nested in,
-- and "<anchor>" is this Header's existing identifier.
function Header (el)
    if el.level == 2 then
        local title = pandoc.utils.stringify(el.content[1])
        currentChapter = title:match("%w+")
        el.identifier = currentChapter
    elseif el.level > 2 then
        el.identifier = currentChapter .. '-' .. el.identifier
    end
    return el
end



-- Performs the following transformations on Link targets:
--
--     Case 1:
--         [text]({{ site.baseurl }}/chapter/#more-stuff) -> [text](#chapter-more-stuff)
--
--     Case 2:
--         [text]({{ site.baseurl }}/chapter/)            -> [text](#chapter)
--
-- All other Links are ignored.
function Link (el)
    local n
    -- When parsing a markdown link such as "[stuff]({{ site.baseurl }}/Naturals",
    -- pandoc encodes the link's URL with percent-encoding, resulting in the
    -- link "[stuff](%7B%7B%20site.baseurl%20%7D%7D/Naturals)".
    local baseurl = "%%7B%%7B%%20site%.baseurl%%20%%7D%%7D"
    el.target, n = el.target:gsub("^" .. baseurl .. "/(%w+)/#([%w-]+)$",  -- case 1
                                  "#%1-%2")
    if n == 0 then
        el.target = el.target:gsub("^" .. baseurl .. "/(%w+)/$",          -- case 2
                                "#%1")
    end
    return el
end
