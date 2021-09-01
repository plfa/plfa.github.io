
#################################################################################
# Configuration
#################################################################################

MAKE  ?= make
STACK ?= stack

SITE_DIR  := _site
RAW_DIR   := $(SITE_DIR)/raw
CACHE_DIR := _cache
TMP_DIR   := $(CACHE_DIR)/tmp

AGDA      := $(STACK) exec agda -- --no-libraries --include-path=standard-library/src
PANDOC    := $(STACK) exec pandoc --


#################################################################################
# Build PLFA site, EPUB, and PDF
#################################################################################

.PHONY: all
all:
	$(MAKE) build
	$(MAKE) epub-build
	$(MAKE) pdf-build

.PHONY: all-clean
all-clean:
	$(MAKE) clean
	$(MAKE) epub-clean
	$(MAKE) pdf-clean

#################################################################################
# Setup Git Hooks
#################################################################################

.PHONY: init
init: setup-check-fix-whitespace setup-install-htmlproofer
	@echo "Setting up Git Hooks"
	git config core.hooksPath .githooks


#################################################################################
# Build PLFA site
#################################################################################

.PHONY: build-deps
build-deps:
	$(STACK) build --only-dependencies

.PHONY: build
build: standard-library/ChangeLog.md | build-deps
	@echo "Building website"
	$(STACK) build
	$(STACK) exec site build

standard-library/ChangeLog.md:
	@echo "Updating Agda standard library"
	git submodule init
	git submodule update --recursive


#################################################################################
# Test generated site with HTMLProofer
#################################################################################

.PHONY: test
test: setup-install-htmlproofer build
	@echo "Testing generated HTML using HTMLProofer"
	cd $(SITE_DIR) && htmlproofer  \
		--check-html                 \
		--disable-external           \
		--report-invalid-tags        \
		--report-missing-names       \
		--report-script-embeds       \
		--report-missing-doctype     \
		--report-eof-tags            \
		--report-mismatched-tags     \
		--check-img-http             \
		--check-opengraph            \
		.


#################################################################################
# Automatically rebuild the site on changes, and start a preview server
#################################################################################

.PHONY: watch
watch: standard-library/ChangeLog.md | build-deps
	@echo "Watching for changes and rebuilding"
	$(STACK) build
	$(STACK) exec site watch


#################################################################################
# Update contributor metadata in `contributors/`
#################################################################################

.PHONY: update-contributors
update-contributors: | build-deps
	@echo "Updating contributors from GitHub"
	$(STACK) build
	$(STACK) exec update-contributors


#################################################################################
# Clean up and remove the cache
#################################################################################

.PHONY: clean
clean: standard-library/ChangeLog.md | build-deps
	@echo "Cleaning generated files for site"
	$(STACK) build
	$(STACK) exec site clean


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
	$(MAKE) all
	@echo "Cleaning intermediate files"
	rm -rf $(RAW_DIR)
	$(MAKE) test
	@echo "Creating web branch"
	git fetch --all
	git checkout -b web --track origin/web
	rsync -a                     \
		--filter='P $(SITE_DIR)/'  \
		--filter='P $(CACHE_DIR)/' \
		--filter='P .git/'         \
		--filter='P .gitignore'    \
		--filter='P .stack-work'   \
		--filter='P .nojekyll'     \
		--filter='P CNAME'         \
		--delete-excluded          \
		$(SITE_DIR) .
	git add -A
	@echo "Publishing web branch"
	git commit -m "Publish."
	git push origin web:web
	@echo "Deleting web branch"
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
	@echo "Checkout latest version from GitHub"
	git clone https://github.com/plfa/plfa.github.io.git --branch web --single-branch --depth 1 html
endif
	@echo "Checkout latest version from GitHub"
	@cd $(PLFA_AFS_DIR)/html         \
		&& git fetch --depth 1         \
		&& git reset --hard origin/web \
		&& git clean -dfx
	@echo "Setting permissions to include web server"
	@fsr setacl $(PLFA_AFS_DIR)/html system:groupwebserver rl
endif


#################################################################################
# Build EPUB
#################################################################################

include book/epub.mk


#################################################################################
# Build PDF
#################################################################################

include book/pdf.mk


#################################################################################
# Setup or check dependencies
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

.PHONY: setup-check-latexmk
setup-check-latexmk:
ifeq (,$(wildcard $(shell which latexmk)))
	@echo "The command you called requires Latexmk"
	@echo "Latemk is included in MacTeX and MikTeX"
	@echo "See: https://mg.readthedocs.io/latexmk.html"
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
