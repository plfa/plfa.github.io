SHELL := /usr/bin/env bash
AGDA_FILES := $(shell find . -type f -and \( -path '*/src/*' -or -path '*/courses/*' \) -and -name '*.lagda.md')
AGDAI_FILES := $(shell find . -type f -and \( -path '*/src/*' -or -path '*/courses/*' \) -and -name '*.agdai')
MARKDOWN_FILES := $(subst courses/,out/,$(subst src/,out/,$(subst .lagda.md,.md,$(AGDA_FILES))))
PLFA_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))

RUBY := ruby
GEM := $(RUBY) -S gem
BUNDLE := $(RUBY) -S bundle
JEKYLL := $(BUNDLE) exec jekyll
HTML_PROOFER := $(BUNDLE) exec htmlproofer

LUA_FILES := $(shell find . -type f -and -path '*/epub/*' -and -name '*.lua')
LUA := lua
LUAROCKS := luarocks --lua-version=$(LUA_VERSION)
LUA_MODULES := lua_modules
PANDOC := /usr/bin/pandoc

ifneq ($(wildcard $(LUA_MODULES)),)
	LUA_FLAGS += -l epub/set_paths
endif

ifeq ($(AGDA_STDLIB_VERSION),)
AGDA_STDLIB_URL := https://agda.github.io/agda-stdlib/
else
AGDA_STDLIB_URL := https://agda.github.io/agda-stdlib/v$(AGDA_STDLIB_VERSION)/
endif


# Build PLFA and test hyperlinks
test: build
	$(HTMLPROOFER) '_site'


# Build PLFA and test hyperlinks offline
test-offline: build
	$(HTMLPROOFER) '_site' --disable-external


# Build PLFA and test hyperlinks for stable
test-stable-offline: $(MARKDOWN_FILES)
	$(JEKYLL) clean
	$(JEKYLL) build --destination '_site/stable' --baseurl '/stable'
	$(HTMLPROOFER) '_site' --disable-external


out/:
	mkdir -p out/

# EPUB generation notes
#
# - The "Apple Books" app on Mac does not show syntax highlighting.
#   The Thorium app on Mac, however, does.
#
# - Regarding --epub-chapter-level, from the docs (https://pandoc.org/MANUAL.html):
#
#       "Specify the heading level at which to split the EPUB into separate “chapter”
#       files. The default is to split into chapters at level-1 headings. This option
#       only affects the internal composition of the EPUB, not the way chapters and
#       sections are displayed to users. Some readers may be slow if the chapter
#       files are too large, so for large documents with few level-1 headings, one
#       might want to use a chapter level of 2 or 3."

epub: out/epub/plfa.epub

out/epub/:
	mkdir -p out/epub/

out/epub/plfa.epub: out/epub/ | $(AGDA_FILES) $(LUA_FILES) epub/main.css out/epub/acknowledgements.md
	$(PANDOC) --strip-comments \
		--css=epub/main.css \
		--epub-embed-font='assets/fonts/mononoki.woff' \
		--epub-embed-font='assets/fonts/FreeMono.woff' \
		--epub-embed-font='assets/fonts/DejaVuSansMono.woff' \
		--lua-filter epub/include-files.lua \
		--lua-filter epub/rewrite-links.lua \
		--lua-filter epub/rewrite-html-ul.lua \
		--lua-filter epub/default-code-class.lua -M default-code-class=agda \
		--standalone \
		--fail-if-warnings \
		--toc --toc-depth=2 \
		--epub-chapter-level=2 \
		-o "$@" \
		epub/index.md

out/epub/acknowledgements.md: src/plfa/acknowledgements.md _config.yml
	 $(LUA) $(LUA_FLAGS) epub/render-liquid-template.lua _config.yml $< $@


# Convert literal Agda to Markdown
define AGDA_template
in := $(1)
out := $(subst courses/,out/,$(subst src/,out/,$(subst .lagda.md,.md,$(1))))
$$(out) : in  = $(1)
$$(out) : out = $(subst courses/,out/,$(subst src/,out/,$(subst .lagda.md,.md,$(1))))
$$(out) : $$(in) | out/
	@echo "Processing $$(subst ./,,$$(in))"
ifeq (,$$(findstring courses/,$$(in)))
	./highlight.sh $$(subst ./,,$$(in)) --include-path=src/
else
# Fix links to the file itself (out/<filename> to out/<filepath>)
	./highlight.sh $$(subst ./,,$$(in)) --include-path=src/ --include-path=$$(subst ./,,$$(dir $$(in)))
endif
endef

$(foreach agda,$(AGDA_FILES),$(eval $(call AGDA_template,$(agda))))


# Start server
serve:
	$(JEKYLL) serve --incremental


# Start background server
server-start:
	$(JEKYLL) serve --no-watch --detach


# Stop background server
server-stop:
	pkill -f jekyll


# Build website using jekyll
build: $(MARKDOWN_FILES)
	$(JEKYLL) build


# Build website using jekyll incrementally
build-incremental: $(MARKDOWN_FILES)
	$(JEKYLL) build --incremental


# Remove all auxiliary files
clean:
	rm -f .agda-stdlib.sed .links-*.sed out/epub/acknowledgements.md
ifneq ($(strip $(AGDAI_FILES)),)
	rm $(AGDAI_FILES)
endif


# Remove all generated files
clobber: clean
	$(JEKYLL) clean
	rm -rf out/

.phony: clobber


# List all .lagda files
ls:
	@echo $(AGDA_FILES)

.phony: ls


# MacOS Setup (install Bundler)
macos-setup:
	brew install libxml2
	$(GEM) install bundler --no-ri --no-rdoc
	$(GEM) install pkg-config --no-ri --no-rdoc -v "~> 1.1"
	$(BUNDLE) config build.nokogiri --use-system-libraries
	$(BUNDLE) install

.phony: macos-setup


# Travis Setup (install Agda, the Agda standard library, acknowledgements, etc.)
travis-setup:\
	$(HOME)/.local/bin/agda\
	$(HOME)/.local/bin/acknowledgements\
	$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src\
	$(HOME)/.agda/defaults\
	$(HOME)/.agda/libraries\
	$(LUA_MODULES)/share/lua/$(LUA_VERSION)/cjson\
	$(LUA_MODULES)/share/lua/$(LUA_VERSION)/tinyyaml.lua\
	$(LUA_MODULES)/share/lua/$(LUA_VERSION)/liquid.lua

.phony: travis-setup


# Agda

travis-install-agda:\
	$(HOME)/.local/bin/agda\
	$(HOME)/.agda/defaults\
	$(HOME)/.agda/libraries

$(HOME)/.agda/defaults:
	echo "standard-library" >> $(HOME)/.agda/defaults
	echo "plfa" >> $(HOME)/.agda/defaults

$(HOME)/.agda/libraries:
	echo "$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/standard-library.agda-lib" >> $(HOME)/.agda/libraries
	echo "$(PLFA_DIR)/plfa.agda-lib" >> $(HOME)/.agda/libraries

$(HOME)/.local/bin/agda:
	travis_retry curl -L https://github.com/agda/agda/archive/v$(AGDA_VERSION).zip\
	                  -o $(HOME)/agda-$(AGDA_VERSION).zip
	unzip -qq $(HOME)/agda-$(AGDA_VERSION).zip -d $(HOME)
	cd $(HOME)/agda-$(AGDA_VERSION);\
		stack install --stack-yaml=stack-8.0.2.yaml

travis-uninstall-agda:
	rm -rf $(HOME)/agda-$(AGDA_VERSION)/
	rm -f $(HOME)/.local/bin/agda
	rm -f $(HOME)/.local/bin/agda-mode

travis-reinstall-agda: travis-uninstall-agda travis-install-agda

.phony: travis-install-agda travis-uninstall-agda travis-reinstall-agda


# Agda Standard Library

travis-install-agda-stdlib: $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src

$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src:
	travis_retry curl -L https://github.com/agda/agda-stdlib/archive/v$(AGDA_STDLIB_VERSION).zip\
	                  -o $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION).zip
	unzip -qq $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION).zip -d $(HOME)
	mkdir -p $(HOME)/.agda

travis-uninstall-agda-stdlib:
	rm $(HOME)/.agda/defaults
	rm $(HOME)/.agda/libraries
	rm -rf $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/

travis-reinstall-agda-stdlib: travis-uninstall-agda-stdlib travis-install-agda-stdlib

.phony: travis-install-agda-stdlib travis-uninstall-agda-stdlib travis-reinstall-agda-stdlib epub


# Acknowledgements

travis-install-acknowledgements: $(HOME)/.local/bin/acknowledgements

$(HOME)/.local/bin/acknowledgements:
	travis_retry curl -L https://github.com/plfa/acknowledgements/archive/master.zip\
	                  -o $(HOME)/acknowledgements-master.zip
	unzip -qq $(HOME)/acknowledgements-master.zip -d $(HOME)
	cd $(HOME)/acknowledgements-master;\
		stack install

travis-uninstall-acknowledgements:
	rm -rf $(HOME)/acknowledgements-master/
	rm $(HOME)/.local/bin/acknowledgements

travis-reinstall-acknowledgements: travis-uninstall-acknowledgements travis-reinstall-acknowledgements

.phony: travis-install-acknowledgements travis-uninstall-acknowledgements travis-reinstall-acknowledgements


# Lua

travis-install-lua:\
	$(LUA_MODULES)/share/lua/$(LUA_VERSION)/cjson\
	$(LUA_MODULES)/share/lua/$(LUA_VERSION)/tinyyaml.lua\
	$(LUA_MODULES)/share/lua/$(LUA_VERSION)/liquid.lua

$(LUA_MODULES)/share/lua/$(LUA_VERSION)/cjson:
# Only this particular version works:
# https://github.com/mpx/lua-cjson/issues/56:
	$(LUAROCKS) install --tree=$(LUA_MODULES) lua-cjson 2.1.0-1

$(LUA_MODULES)/share/lua/$(LUA_VERSION)/tinyyaml.lua:
	$(LUAROCKS) install --tree=$(LUA_MODULES) lua-tinyyaml

$(LUA_MODULES)/share/lua/$(LUA_VERSION)/liquid.lua:
	$(LUAROCKS) install --tree=$(LUA_MODULES) liquid
