EPUB_DIR          := book
EPUB_TEMPLATE_DIR := $(EPUB_DIR)/templates
EPUB_LUA_DIR      := $(EPUB_DIR)/lua
EPUB_LUA_SCRIPTS  := $(wildcard $(EPUB_LUA_DIR)/*.lua)
MD_DIR            := src
MD_FILES          := README.md $(wildcard $(MD_DIR)/plfa/**/*.md)


# Compile PLFA to an EPUB
.PHONY: epub
epub: $(SITE_DIR)/plfa.epub

$(SITE_DIR)/plfa.epub: book/epub.md book/epub.css $(MD_FILES) $(EPUB_LUA_SCRIPTS) | setup-install-pandoc
	@$(PANDOC) \
		--strip-comments \
		--css=epub/epub.css \
		--epub-embed-font='public/webfonts/DejaVu-mononoki-Symbola-Droid.woff' \
		--lua-filter=$(EPUB_LUA_DIR)/include-files.lua \
		--lua-filter=$(EPUB_LUA_DIR)/single-file-links.lua \
		--lua-filter=$(EPUB_LUA_DIR)/epub-clean-html.lua \
		--lua-filter=$(EPUB_LUA_DIR)/set-default-code-class.lua -M default-code-class=agda \
		--standalone \
		--fail-if-warnings \
		--toc --toc-depth=2 \
		--epub-chapter-level=2 \
		$< -o $@


# Test EPUB with EPUBCheck
.PHONY: epub-test
epub-test: $(SITE_DIR)/plfa.epub | setup-check-epubcheck
	epubcheck $(SITE_DIR)/plfa.epub


# Clean generated files
.PHONY: epub-clean
epub-clean:
	rm $(SITE_DIR)/plfa.epub
