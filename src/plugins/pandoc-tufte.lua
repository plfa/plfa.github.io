function Div(div)
    -- Handle epigraph directive.
    -- Renders as `<div class="epigraph">`
    -- Handle fullwidth directive.
    if div.classes:includes("fullwidth") then
        div = div:walk({
            CodeBlock = function (codeBlock)
                codeBlock.attr.classes:insert("fullwidth")
                return codeBlock
            end,
            Figure = function (figure)
                figure.attr.classes:insert("fullwidth")
                return figure
            end,
        })
        return div.content
    end
    -- Handle iframe directive.
    -- Renders as warning:
    if div.classes:find_if(function (class)
        return class:match "^iframe.*"
    end) then
        return pandoc.Para({
            pandoc.Span({
                pandoc.Str("Warning:"),
                pandoc.Space(),
                pandoc.Code(":::iframe"),
                pandoc.Space(),
                pandoc.Str("is not supported in EPUB"),
            }, {
                class = "warning",
            })
        })
    end
end

function Span(span)
    -- Handle newthought span.
    -- Renders as `<span class="newthought">`
    -- Handle cite span.
    -- Renders as `<span class="cite">`
    -- Handle footer span.
    -- Renders as `<span class="footer">`
    -- Handle margin span.
    if span.classes:includes("margin") then
        -- If the margin span is a margin figure...
        local figure = nil
        span:walk({ Image = function(image) figure = image end })
        if figure ~= nil then
            -- ...then simply return its contents.
            return pandoc.Inlines({
                table.unpack(span.content),
                pandoc.Str(figure.title),
            })
        end
        -- If the margin span is a margin note...
        local id = span.identifier
        local label = span.attributes.label
        -- ...rewrite it to a footnote
        return pandoc.Inlines({
            pandoc.Str(label),
            pandoc.Note({pandoc.Para(span.content)}),
        })
    end
end
