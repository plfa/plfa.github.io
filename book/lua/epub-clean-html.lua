function RawBlock(el)
  -- Transforms '<ul class={something}>' into '<ul>'.
  el.text = el.text:gsub('%s*<%s*ul%s*class=%s*"?[%w-]+"?%s*>%s*', '<ul>')
  return el
end
