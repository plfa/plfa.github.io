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

$(SITE_DIR): authors contributors css courses hs pages posts public src templates
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
# Clean up and remove the cache
#################################################################################

.PHONY: clean
clean:
	stack build && stack exec site clean


#################################################################################
# Update contributor metadata in `contributors/`
#################################################################################

.PHONY: update-contributors
update-contributors:
	stack build && stack exec update-contributors


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
