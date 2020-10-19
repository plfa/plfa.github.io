-- Transforms '<ul class={something}>' into '<ul>'.
function RawBlock (el)
    el.text = el.text:gsub('%s*<%s*ul%s*class=%s*"?[%w-]+"?%s*>%s*', '<ul>')
    return el
end