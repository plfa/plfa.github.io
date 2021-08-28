local chapter = nil

function Header(el)
  if el.level == 2 then
    chapter = el.attr.identifier
  end
  if el.level >= 3 then
    if el.attr.attributes.name then
      el.attr.identifier = chapter .. '-' .. el.attr.attributes.name
      el.attr.attributes.name = nil
    else
      el.attr.identifier = chapter .. '-' .. el.attr.identifier
    end
  end
end

function show(t)
  local str = ''
  str = str .. '{'
  for k,v in pairs(t) do
    str = str .. k
    str = str .. ':'
    if type(v) == 'table' then
      str = str .. show(v)
    else
      str = str .. v
    end
  end
  str = str .. '}'
  return str
end
