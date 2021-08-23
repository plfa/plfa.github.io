#################################################################################
# Configuration
#################################################################################

SITE_DIR := _site
CACHE_DIR := _cache
TMP_DIR := $(CACHE_DIR)/tmp

AGDA := stack exec agda -- \
		--no-libraries \
		--include-path=standard-library/src
PANDOC := stack exec pandoc -- \
		--indented-code-classes=default
		--top-level-division=chapter


#################################################################################
# Setup Git Hooks
#################################################################################

.PHONY: init
init: setup-check-fix-whitespace setup-install-htmlproofer
	git config core.hooksPath .githooks


#################################################################################
# Build PLFA site
#################################################################################

.PHONY: build
build: \
		standard-library/ChangeLog.md
	stack build && stack exec site build

standard-library/ChangeLog.md:
	git submodule init
	git submodule update --recursive


#################################################################################
# Test generated site with HTMLProofer
#################################################################################

.PHONY: test
test: setup-install-htmlproofer build
	cd $(SITE_DIR) && htmlproofer \
		--check-html                \
		--disable-external          \
		--report-invalid-tags       \
		--report-missing-names      \
		--report-script-embeds      \
		--report-missing-doctype    \
		--report-eof-tags           \
		--report-mismatched-tags    \
		--check-img-http            \
		--check-opengraph           \
		.


#################################################################################
# Test generated EPUB with EPUBCheck
#################################################################################

.PHONY: test-epub
test-epub: setup-check-epubcheck build
	epubcheck $(SITE_DIR)/plfa.epub


#################################################################################
# Automatically rebuild the site on changes, and start a preview server
#################################################################################

.PHONY: watch
watch: \
		standard-library/ChangeLog.md
	stack build && stack exec site watch


#################################################################################
# Update contributor metadata in `contributors/`
#################################################################################

.PHONY: update-contributors
update-contributors:
	stack build && stack exec update-contributors


#################################################################################
# Clean up and remove the cache
#################################################################################

.PHONY: clean
clean: \
		standard-library/ChangeLog.md
	stack build && stack exec site clean


#################################################################################
# List targets in Makefile
#################################################################################

.PHONY: list
list:
	@$(MAKE) -pRrq -f $(lastword $(MAKEFILE_LIST)) : 2>/dev/null | awk -v RS= -F: '/^# File/,/^# Finished Make data base/ {if ($$1 !~ "^[#.]") {print $$1}}' | sort | egrep -v -e '^[^[:alnum:]]' -e '^$@$$'



########################################
# Publish PLFA to plfa.github.io
########################################

.PHONY: publish
publish: setup-check-rsync
	@echo "Building site..."
	make build
	@echo "Testing site..."
	make test
	@echo "Creating web branch..."
	git fetch --all
	git checkout -b web --track origin/web
	rsync -a                   \
		--filter='P _site/'      \
		--filter='P _cache/'     \
		--filter='P .git/'       \
		--filter='P .gitignore'  \
		--filter='P .stack-work' \
		--filter='P .nojekyll'   \
		--filter='P CNAME'       \
		--delete-excluded        \
		_site/ .
	git add -A
	@echo "Publishing web branch..."
	git commit -m "Publish."
	git push origin web:web
	@echo "Deleting web branch..."
	git checkout dev
	git branch -D web


########################################
# Publish PLFA to plfa.inf.ed.ac.uk
########################################

PLFA_AFS_DIR := /afs/inf.ed.ac.uk/group/project/plfa

.PHONY: publish-uoe
publish-uoe:
ifeq (,$(wildcard $(PLFA_AFS_DIR)))
	@echo "Please connect the Informatics OpenAFS filesystem."
	@echo "See: http://computing.help.inf.ed.ac.uk/informatics-filesystem"
	@exit 1
else
ifeq (,$(wildcard $(PLFA_AFS_DIR)/html))
	git clone https://github.com/plfa/plfa.github.io.git --branch web --single-branch --depth 1 html
endif
	cd $(PLFA_AFS_DIR)/html          \
		&& git fetch --depth 1         \
		&& git reset --hard origin/web \
		&& git clean -dfx
	fsr setacl $(PLFA_AFS_DIR)/html system:groupwebserver rl
endif


#################################################################################
# Build PDF
#################################################################################

PDF_DIR          := pdf
PDF_TEMPLATE_DIR := $(PDF_DIR)/templates
PDF_LUA_DIR      := $(PDF_DIR)/lua
MD_DIR           := src
LAGDA_TEX_DIR    := $(TMP_DIR)/lagda_tex
TEX_DIR          := $(TMP_DIR)/tex

# Convert MD_DIR/%.lagda.md to LAGDA_TEX_DIR/%.lagda.tex
define LAGDA_TEX_PATH
$(patsubst $(MD_DIR)/%.lagda.md,$(LAGDA_TEX_DIR)/%.lagda.tex,$(1))
endef

# Convert MD_DIR/%.md to LAGDA_TEX_DIR/%.lagda.tex or TEX_DIR/%.tex
define TEX_PATH
$(patsubst $(PDF_DIR)/%,$(TEX_DIR)/%,\
	$(patsubst README.md,$(TEX_DIR)/plfa/frontmatter/README.tex,\
		$(patsubst $(MD_DIR)/%.md,$(TEX_DIR)/%.tex,\
			$(patsubst $(MD_DIR)/%.lagda.md,$(TEX_DIR)/%.tex,$(1)))))
endef

# List source and intermediate files
PDF_LUA_SCRIPTS  := $(wildcard $(PDF_LUA_DIR)/*.lua)
PDF_STATIC_FILES := $(wildcard pdf/*.*)
MD_FILES         := README.md $(wildcard $(MD_DIR)/plfa/**/*.md)
LAGDA_MD_FILES   := $(filter %.lagda.md,$(MD_FILES))
LAGDA_TEX_FILES  := $(call LAGDA_TEX_PATH,$(LAGDA_MD_FILES))
TEX_FILES        := $(call TEX_PATH,$(MD_FILES) $(PDF_STATIC_FILES))

# Compile PLFA to a PDF
.PHONY: pdf
pdf: $(SITE_DIR)/plfa.pdf

$(SITE_DIR)/plfa.pdf: $(TEX_FILES)
	@cd $(TEX_DIR) && latexmk -pdf -lualatex -use-make -halt-on-error plfa.tex
	@cp $(TEX_DIR)/plfa.pdf $(SITE_DIR)/plfa.pdf


# Copy static files needed by PDF compilation
define MK_COPYSTATIC_RULE
src := $(1)
dst := $(2)
$$(dst): $$(src)
	@echo "Copy $$< to $$@"
	@cp $$< $$@
endef

# Compile Markdown files to LaTeX
define MK_MD2TEX_RULE
src := $(1)
dst := $(2)
tpl := $(3)
$$(dst): export UNCHECKED_FILES = README.md
$$(dst): $$(src) $$(tpl) $(PDF_LUA_SCRIPTS) | setup-install-pandoc
	@echo "Compile $$< to $$@"
	@mkdir -p '$$(@D)'
	@$(PANDOC) \
		--lua-filter=$(PDF_LUA_DIR)/remove-badges.lua \
		--lua-filter=$(PDF_LUA_DIR)/typeset-codeblocks.lua \
		--lua-filter=$(PDF_LUA_DIR)/rewrite-links.lua \
		--lua-filter=$(PDF_LUA_DIR)/single-file-headers-ids.lua \
		--template=$$(tpl) \
		$$< -o $$@
endef

# Compile Literate Agda files to LaTeX
define MK_LAGDA_MD2TEX_RULE
src := $(1)
dst := $(2)
$$(dst): $$(src) $(LAGDA_TEX_FILES) | setup-install-agda
	@$(AGDA) --include-path=$(LAGDA_TEX_DIR) --latex --latex-dir=$(TEX_DIR) $$<
endef


# Copy static files (from PDF_DIR/% to TEX_DIR/%)
$(foreach static_file,\
	$(PDF_STATIC_FILES),\
	$(eval $(call MK_COPYSTATIC_RULE,\
		$(static_file),\
		$(call TEX_PATH,$(static_file)))))

# Compile .md files (from MD_DIR/%.md to TEX_DIR/%.tex)
$(foreach md_file,\
	$(filter-out %acknowledgements.md %.lagda.md,$(MD_FILES)),\
	$(eval $(call MK_MD2TEX_RULE,\
		$(md_file),\
		$(call TEX_PATH,$(md_file)),\
		$(PDF_TEMPLATE_DIR)/chapter.latex)))

# Compile .lagda.md files (from MD_DIR/%.md to LAGDA_TEX_DIR/%.lagda.tex)
$(foreach lagda_md_file,\
	$(LAGDA_MD_FILES),\
	$(eval $(call MK_MD2TEX_RULE,\
		$(lagda_md_file),\
		$(call LAGDA_TEX_PATH,$(lagda_md_file)),\
		$(PDF_TEMPLATE_DIR)/chapter.latex)))

# Compile acknowledgements (from SITE_DIR/acknowledgements.md to TEX_DIR/acknowledgements.tex)
$(eval $(call MK_MD2TEX_RULE,\
	$(SITE_DIR)/acknowledgements.md,\
	$(TEX_DIR)/plfa/backmatter/acknowledgements.tex,\
	$(PDF_TEMPLATE_DIR)/acknowledgements.latex))

# Compile .lagda.tex files (from LAGDA_TEX_DIR/%.lagda.tex to TEX_DIR/%.tex)
$(foreach lagda_md_file,\
	$(LAGDA_MD_FILES),\
	$(eval $(call MK_LAGDA_MD2TEX_RULE,\
		$(call LAGDA_TEX_PATH,$(lagda_md_file)),\
		$(call TEX_PATH,$(lagda_md_file)))))


#################################################################################
# Setup dependencies
#################################################################################

.PHONY: setup-check-stack
setup-check-stack:
ifeq (,$(wildcard $(shell which stack)))
	@echo "The command you called requires the Haskell Tool Stack"
	@echo "See: https://docs.haskellstack.org/en/stable/install_and_upgrade/"
	@exit 1
endif

.PHONY: setup-check-npm
setup-check-npm:
ifeq (,$(wildcard $(shell which npm)))
	@echo "The command you called requires the Node Package Manager"
	@echo "See: https://www.npmjs.com/get-npm"
	@exit 1
endif

.PHONY: setup-check-gem
setup-check-gem:
ifeq (,$(wildcard $(shell which gem)))
	@echo "The command you called requires the RubyGems Package Manager"
	@echo "See: https://www.ruby-lang.org/en/documentation/installation/"
	@exit 1
endif

.PHONY: setup-check-fix-whitespace
setup-check-fix-whitespace: setup-check-stack
ifeq (,$(wildcard $(shell which fix-whitespace)))
	@echo "The command you called requires fix-whitespace"
	@echo "Run: git clone https://github.com/agda/fix-whitespace"
	@echo "     cd fix-whitespace/"
	@echo "     stack install --stack-yaml stack-8.8.3.yaml"
endif

.PHONY: setup-check-epubcheck
setup-check-epubcheck:
ifeq (,$(wildcard $(shell which epubcheck)))
	@echo "The command you called requires EPUBCheck"
	@echo "See: https://github.com/w3c/epubcheck"
endif

.PHONY: setup-check-rsync
setup-check-rsync:
ifeq (,$(wildcard $(shell which rsync)))
	@echo "The command you called requires rsync"
	@echo "See: https://rsync.samba.org/"
	@exit 1
endif

.PHONY: setup-install-htmlproofer
setup-install-htmlproofer: setup-check-gem
ifeq (,$(wildcard $(shell which htmlproofer)))
	@echo "Installing HTMLProofer..."
	gem install html-proofer
endif

.PHONY: setup-install-bundler
setup-install-bundler: setup-check-gem
ifeq (,$(wildcard $(shell which bundle)))
	@echo "Installing Ruby Bundler..."
	gem install bundle
endif

.PHONY: setup-install-agda
setup-install-agda: setup-check-stack
ifeq (,$(wildcard $(shell stack exec which -- agda)))
	@echo "Installing Agda"
	stack build --only-dependencies
endif

.PHONY: setup-install-pandoc
setup-install-pandoc: setup-check-stack
ifeq (,$(wildcard $(shell stack exec which -- pandoc)))
	@echo "Installing Pandoc"
	stack build --only-dependencies
endif

#################################################################################
# Build legacy versions of website using Jekyll
#################################################################################

LEGACY_VERSIONS := 19.08 20.07
LEGACY_VERSION_DIRS := $(addprefix versions/,$(addsuffix /,$(LEGACY_VERSIONS)))

legacy-versions: setup-install-bundle $(LEGACY_VERSION_DIRS)

ifeq ($(shell sed --version >/dev/null 2>&1; echo $$?),1)
SEDI := sed -i ""
else
SEDI := sed -i
endif

define build_legacy_version
version := $(1)
out := $(addsuffix /,$(1))
url := $(addprefix https://github.com/plfa/plfa.github.io/archive/web-,$(addsuffix .zip,$(1)))
tmp_zip := $(addprefix versions/plfa.github.io-web-,$(addsuffix .zip,$(1)))
tmp_dir := $(addprefix versions/plfa.github.io-web-,$(addsuffix /,$(1)))
baseurl := $(addprefix /,$(1))

$$(tmp_zip): tmp_zip = $(addprefix versions/plfa.github.io-web-,$(addsuffix .zip,$(1)))
$$(tmp_zip): url = $(addprefix https://github.com/plfa/plfa.github.io/archive/web-,$(addsuffix .zip,$(1)))
$$(tmp_zip):
	@mkdir -p versions/
	@wget -c $$(url) -O $$(tmp_zip)

$$(tmp_dir): version = $(1)
$$(tmp_dir): tmp_dir = $(addprefix versions/plfa.github.io-web-,$(addsuffix /,$(1)))
$$(tmp_dir): tmp_zip = $(addprefix versions/plfa.github.io-web-,$(addsuffix .zip,$(1)))
$$(tmp_dir): $$(tmp_zip)
	@yes | unzip -qq $$(tmp_zip) -d versions/
	@$(SEDI) "s/branch: dev/branch: dev-$$(version)/" $$(addsuffix _config.yml,$$(tmp_dir))

versions/$$(out): out = $(addsuffix /,$(1))
versions/$$(out): url = $(addprefix https://github.com/plfa/plfa.github.io/archive/web-,$(addsuffix .zip,$(1)))
versions/$$(out): tmp_dir = $(addprefix versions/plfa.github.io-web-,$(addsuffix /,$(1)))
versions/$$(out): baseurl = $(addprefix /,$(1))
versions/$$(out): $$(tmp_dir)
	@echo "source \"https://rubygems.org\"\n\ngroup :jekyll_plugins do\n  gem 'github-pages'\nend" > $$(tmp_dir)/Gemfile
	@cd $$(tmp_dir) \
		&& rm -rf _posts \
		&& bundle install \
		&& bundle exec jekyll clean \
		&& bundle exec jekyll build --destination '../$$(out)' --baseurl '$$(baseurl)'
endef

$(foreach legacy_version,$(LEGACY_VERSIONS),$(eval $(call build_legacy_version,$(legacy_version))))
