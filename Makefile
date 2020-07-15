SHELL := /usr/bin/env bash
AGDA_FILES := $(shell find . -type f -and \( -path './src/*' -or -path './courses/*' \) -and -name '*.lagda.md')
AGDAI_FILES := $(shell find . -type f -and \( -path './src/*' -or -path './courses/*' \) -and -name '*.agdai')
MARKDOWN_FILES := $(subst courses/,out/,$(subst src/,out/,$(subst .lagda.md,.md,$(AGDA_FILES))))
PLFA_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
PANDOC := pandoc
EPUBCHECK := epubcheck
RUBY := ruby
GEM := $(RUBY) -S gem
BUNDLE := $(RUBY) -S bundle
JEKYLL := $(BUNDLE) exec jekyll
HTMLPROOFER := $(BUNDLE) exec htmlproofer
LUA_FILES := $(shell find . -type f -and -path '*/epub/*' -and -name '*.lua')
RELEASE_VERSIONS := 19.08 20.07
RELEASES := $(addsuffix /,$(RELEASE_VERSIONS))
LATEST_VERSION := $(word $(words $(RELEASE_VERSIONS)),$(RELEASE_VERSIONS))

ifeq ($(AGDA_STDLIB_VERSION),)
AGDA_STDLIB_URL := https://agda.github.io/agda-stdlib/
else
AGDA_STDLIB_URL := https://agda.github.io/agda-stdlib/v$(AGDA_STDLIB_VERSION)/
endif

ifeq ($(shell sed --version >/dev/null 2>&1; echo $$?),1)
SEDI := sed -i ""
else
SEDI := sed -i
endif


# Build PLFA web version and test links
default: test


# Start Jekyll server with --incremental
serve:
	$(JEKYLL) serve --incremental

# Start detached Jekyll server
server-start:
	$(JEKYLL) serve --no-watch --detach

# Stop detached Jekyll server
server-stop:
	pkill -f jekyll

.phony: serve server-start server-stop


# Build PLFA web version using Jekyll
build: $(MARKDOWN_FILES)
	$(JEKYLL) build

# Build PLFA web version using Jekyll with --incremental
build-incremental: $(MARKDOWN_FILES)
	$(JEKYLL) build --incremental

# Download PLFA web releases
build-history: latest/ $(RELEASES)

latest/: $(addprefix .versions/plfa.github.io-web-,$(addsuffix /,$(LATEST_VERSION)))
	cd $< \
		&& $(JEKYLL) clean \
		&& $(JEKYLL) build --destination '../../latest' --baseurl '/latest'

# Download PLFA web release and build it under the relevant folder
define build_release
version := $(1)
out := $(addsuffix /,$(1))
url := $(addprefix https://github.com/plfa/plfa.github.io/archive/web-,$(addsuffix .zip,$(1)))
tmp_zip := $(addprefix .versions/plfa.github.io-web-,$(addsuffix .zip,$(1)))
tmp_dir := $(addprefix .versions/plfa.github.io-web-,$(addsuffix /,$(1)))
baseurl := $(addprefix /,$(1))

$$(tmp_zip): tmp_zip = $(addprefix .versions/plfa.github.io-web-,$(addsuffix .zip,$(1)))
$$(tmp_zip): url = $(addprefix https://github.com/plfa/plfa.github.io/archive/web-,$(addsuffix .zip,$(1)))
$$(tmp_zip):
	@mkdir -p .versions/
	wget -c $$(url) -O $$(tmp_zip)

$$(tmp_dir): version = $(1)
$$(tmp_dir): tmp_dir = $(addprefix .versions/plfa.github.io-web-,$(addsuffix /,$(1)))
$$(tmp_dir): tmp_zip = $(addprefix .versions/plfa.github.io-web-,$(addsuffix .zip,$(1)))
$$(tmp_dir): $$(tmp_zip)
	yes | unzip -qq $$(tmp_zip) -d .versions/
	$(SEDI) "s/branch: dev/branch: dev-$$(version)/" $$(addsuffix _config.yml,$$(tmp_dir))

$$(out): out = $(addsuffix /,$(1))
$$(out): url = $(addprefix https://github.com/plfa/plfa.github.io/archive/web-,$(addsuffix .zip,$(1)))
$$(out): tmp_dir = $(addprefix .versions/plfa.github.io-web-,$(addsuffix /,$(1)))
$$(out): baseurl = $(addprefix /,$(1))
$$(out): $$(tmp_dir)
	cd $$(tmp_dir) \
		&& rm -rf _posts \
		&& $(JEKYLL) clean \
		&& $(JEKYLL) build --destination '../../$$(out)' --baseurl '$$(baseurl)'
endef

# Incorporate previous releases of PLFA web version
$(foreach release_version,$(RELEASE_VERSIONS),$(eval $(call build_release,$(release_version))))

# Convert literal Agda to Markdown using highlight.sh
define AGDA_template
in := $(1)
out := $(subst courses/,out/,$(subst src/,out/,$(subst .lagda.md,.md,$(1))))
$$(out) : in  = $(1)
$$(out) : out = $(subst courses/,out/,$(subst src/,out/,$(subst .lagda.md,.md,$(1))))
$$(out) : $$(in)
	@echo "Processing $$(subst ./,,$$(in))"
	@mkdir -p out/
ifeq (,$$(findstring courses/,$$(in)))
	./highlight.sh $$(subst ./,,$$(in)) --include-path=src/
else
# Fix links to the file itself (out/<filename> to out/<filepath>)
	./highlight.sh $$(subst ./,,$$(in)) --include-path=src/ --include-path=$$(subst ./,,$$(dir $$(in)))
endif
endef

$(foreach agda,$(AGDA_FILES),$(eval $(call AGDA_template,$(agda))))

.phony: build build-incremental


# Test links using htmlproofer
test: build
	$(HTMLPROOFER) '_site'

# Test local links using htmlproofer
test-offline: build
	$(HTMLPROOFER) '_site' --disable-external

# Test local links for stability under different base URLs
test-stable-offline: $(MARKDOWN_FILES)
	$(JEKYLL) clean
	$(JEKYLL) build --destination '_site/stable' --baseurl '/stable'
	$(HTMLPROOFER) '_site' --disable-external

.phony: test test-offline test-stable-offline


# Build EPUB using Pandoc
epub: out/epub/plfa.epub

# Test EPUB using EPUBCheck
epubcheck: out/epub/plfa.epub
	$(EPUBCHECK) out/epub/plfa.epub

out/epub/plfa.epub: $(AGDA_FILES) $(LUA_FILES) epub/main.css out/epub/acknowledgements.md
	@mkdir -p out/epub/
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
	@mkdir -p out/epub/
	 $(BUNDLE) exec ruby epub/render-liquid-template.rb _config.yml $< $@

.phony: epub epubcheck


# Clean auxiliary files
clean:
	rm -f .agda-stdlib.sed .links-*.sed out/epub/acknowledgements.md
	rm -rf .versions
ifneq ($(strip $(AGDAI_FILES)),)
	rm $(AGDAI_FILES)
endif

# Clean generated files
clobber: clean
	$(JEKYLL) clean
	rm -rf out/
	rm -rf latest/ $(RELEASES)

.phony: clean clobber



# Setup Travis
travis-setup:\
	$(HOME)/.local/bin/agda\
	$(HOME)/.local/bin/acknowledgements\
	$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src\
	$(HOME)/.agda/defaults\
	$(HOME)/.agda/libraries

.phony: travis-setup


# Setup Agda

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


# Setup Agda Standard Library

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


# Setup Acknowledgements

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
