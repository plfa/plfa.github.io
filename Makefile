#################################################################################
# Configuration
#################################################################################

STACK        ?= stack
HTML_PROOFER ?= htmlproofer
BROWSER_SYNC ?= browser-sync
SITE_DIR     := _site


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

.PHONY: test
test: | build needs-htmlproofer
	@cd $(SITE_DIR) && htmlproofer \
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
