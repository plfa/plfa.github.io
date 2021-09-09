#################################################################################
# Configuration
#################################################################################

STACK         ?= stack
EBOOK_CONVERT ?= ebook-convert
EPUBCHECK     ?= epubcheck
HTML_PROOFER  ?= htmlproofer
BROWSER_SYNC  ?= browser-sync
SITE_DIR      := _site


.PHONY: build
build: | needs-stack
	@$(STACK) build --silent && $(STACK) run

.PHONY: serve
serve: | needs-browser-sync
	@cd $(SITE_DIR) &&			\
		$(BROWSER_SYNC) start	\
			--server						\
			--files "."					\
			--no-ui							\
			--reload-delay 500	\
			--reload-debounce 500


#################################################################################
# Testing
#################################################################################

.PHONY: test
test: | build needs-htmlproofer
	@cd $(SITE_DIR) && $(HTML_PROOFER)	\
		--check-html											\
		--disable-external								\
		--report-invalid-tags							\
		--report-missing-names						\
		--report-script-embeds						\
		--report-missing-doctype					\
		--report-eof-tags									\
		--report-mismatched-tags					\
		--check-img-http									\
		--check-opengraph									\
		.

.PHONY: test-external
test-external: | build needs-htmlproofer
	@cd $(SITE_DIR) && $(HTML_PROOFER)	\
		--external_only

.PHONY: test-epub
test-epub: | build needs-epubcheck
	$(EPUBCHECK) $(SITE_DIR)/plfa.epub


#################################################################################
# Cleaning up
#################################################################################

.PHONY: clean
clean:
	@rm -rf _build

.PHONY: clobber
clobber: clean
	@rm -rf _site


#################################################################################
# Check if dependencies are available
#################################################################################

.PHONY: needs-stack
needs-stack:
ifeq (,$(wildcard $(shell which $(STACK))))
	@echo "The command you called requires the Haskell Tool Stack"
	@echo "See: https://docs.haskellstack.org/en/stable/install_and_upgrade/"
	@exit 1
endif

.PHONY: needs-htmlproofer
needs-htmlproofer:
ifeq (,$(wildcard $(shell which $(HTML_PROOFER))))
	@echo "The command you called requires HTMLProofer"
	@echo "See: https://github.com/gjtorikian/html-proofer"
	@exit 1
endif

.PHONY: needs-browser-sync
needs-browser-sync:
ifeq (,$(wildcard $(shell which $(BROWSER_SYNC))))
	@echo "The command you called requires Browsersync"
	@echo "See: https://browsersync.io/"
	@exit 1
endif

.PHONY: needs-epubcheck
needs-epubcheck:
ifeq (,$(wildcard $(shell which $(EPUBCHECK))))
	@echo "The command you called requires EPUBCheck"
	@echo "See: https://github.com/w3c/epubcheck"
endif

.PHONY: needs-calibre
needs-calibre:
ifeq (,$(wildcard $(shell which $(EBOOK_CONVERT))))
	@echo "The command you called requires Calibre"
	@echo "See: https://calibre-ebook.com/"
endif
