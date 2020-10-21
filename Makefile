#################################################################################
# Configuration
#################################################################################

SITE_DIR := _site
CACHE_DIR := _cache
TMP_DIR := $(CACHE_DIR)/tmp


#################################################################################
# Setup Git Hooks
#################################################################################

.PHONY: init
init:
	git config core.hooksPath .githooks


#################################################################################
# Build PLFA site
#################################################################################

.PHONY: build
build: $(SITE_DIR)

$(SITE_DIR): authors contributors css courses hs posts public src templates
	stack build && stack exec site build


#################################################################################
# Test generated site with HTMLProofer
#################################################################################

.PHONY: test
test: $(SITE_DIR)
	cd $(SITE_DIR) && htmlproofer \
		--check-html \
		--disable-external \
		--report-invalid-tags \
		--report-missing-names \
		--report-script-embeds \
		--report-missing-doctype \
		--report-eof-tags \
		--report-mismatched-tags \
		--check-img-http \
		--check-opengraph \
		.


#################################################################################
# Automatically rebuild the site on changes, and start a preview server
#################################################################################

.PHONY: watch
watch:
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
clean:
	stack build && stack exec site clean


#################################################################################
# List targets in Makefile
#################################################################################

.PHONY: list
list:
	@$(MAKE) -pRrq -f $(lastword $(MAKEFILE_LIST)) : 2>/dev/null | awk -v RS= -F: '/^# File/,/^# Finished Make data base/ {if ($$1 !~ "^[#.]") {print $$1}}' | sort | egrep -v -e '^[^[:alnum:]]' -e '^$@$$'


#################################################################################
# Setup dependencies
#################################################################################

.PHONY: setup
setup: setup-check-stack setup-check-npm setup-check-gem

.PHONY: setup-check-stack
check-stack:
ifeq (,$(wildcard $(shell which stack)))
	@echo "Setup requires the Haskell Tool Stack"
	@echo "See: https://docs.haskellstack.org/en/stable/install_and_upgrade/"
	@exit 1
endif

.PHONY: setup-check-npm
ifeq (,$(wildcard $(shell which npm)))
	@echo "Setup requires the Node Package Manager"
	@echo "See: https://www.npmjs.com/get-npm"
	@exit 1
endif

.PHONY: setup-check-gem
check-gem:
ifeq (,$(wildcard $(shell which gem)))
	@echo "Setup requires the RubyGems Package Manager"
	@echo "See: https://www.ruby-lang.org/en/documentation/installation/"
	@exit 1
endif

.PHONY: setup-install-html-proofer
setup-install-html-proofer: setup-check-npm
ifeq (,$(wildcard $(shell which htmlproofer)))
	@echo "Installing HTMLProofer..."
	gem install html-proofer
endif

.PHONY: setup-install-bundle
setup-install-html-proofer: setup-check-gem
ifeq (,$(wildcard $(shell which bundle)))
	@echo "Installing Ruby Bundler..."
	gem install bundle
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
