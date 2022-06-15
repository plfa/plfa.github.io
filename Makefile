OUT_DIR := _site
TMP_DIR := _cache

CABAL ?= $(wildcard $(shell which cabal))
NPX ?= $(wildcard $(shell which npx))
RBENV ?= $(wildcard $(shell which rbenv))

.PHONY: default
default: build

########################################
# Command-line arguments
########################################

# make test-html-proofer:
#   - EXTERNAL_LINKS:
#     If set, external links are checked.


########################################
# Initialize Git Hooks
########################################

.PHONY: init
init:
	git config core.hooksPath .githooks


########################################
# Build site with Shake
########################################

SHAKE_ARGS += -j
SHAKE_ARGS += --lint
SHAKE_ARGS += --profile=$(TMP_DIR)/reports/build.html
SHAKE_ARGS += --timing

HTML_MINIFIER ?= $(wildcard $(shell which html-minifier))

HTML_MINIFIER_ARGS += --collapse-whitespace
HTML_MINIFIER_ARGS += --collapse-boolean-attributes
HTML_MINIFIER_ARGS += --minify-css
HTML_MINIFIER_ARGS += --minify-js
HTML_MINIFIER_ARGS += --minify-urls
HTML_MINIFIER_ARGS += --remove-comments
HTML_MINIFIER_ARGS += --input-dir=$(OUT_DIR)
HTML_MINIFIER_ARGS += --output-dir=$(OUT_DIR)
HTML_MINIFIER_ARGS += --file-ext=html

UNZIP ?= unzip

ifeq ($(CI),)
UNZIP_ARGS += -q
endif
UNZIP_ARGS += -n
UNZIP_ARGS += -d $(OUT_DIR)

.PHONY: build
build: check-haskell check-html-minifier
	@echo "Building PLFA..."
	@mkdir -p $(TMP_DIR)/reports/
	@$(CABAL) $(CABAL_ARGS) v2-run builder -- build $(SHAKE_ARGS)
	@echo "Minifying HTML with html-minifier..."
	@$(HTML_MINIFIER) $(HTML_MINIFIER_ARGS)
	@echo "Unpacking legacy versions..."
	@$(UNZIP) $(UNZIP_ARGS) data/legacy/19.08.zip
	@$(UNZIP) $(UNZIP_ARGS)  data/legacy/20.07.zip

.PHONY: clean
clean: check-haskell
	@$(CABAL) $(CABAL_ARGS) v2-run builder -- clean

.PHONY: clobber
clobber: check-haskell
	@$(CABAL) $(CABAL_ARGS) v2-run builder -- clobber


########################################
# Watch for changes with fswatch
########################################

FSWATCH ?= $(wildcard $(shell which fswatch))

FSWATCH_ARGS += --event=IsFile
FSWATCH_ARGS += --event=Created
FSWATCH_ARGS += --event=Updated
FSWATCH_ARGS += --event=Removed
FSWATCH_ARGS += --event=Renamed
FSWATCH_ARGS += --event=MovedFrom
FSWATCH_ARGS += --event=MovedTo
FSWATCH_ARGS += --one-per-batch
FSWATCH_ARGS += --recursive
FSWATCH_ARGS += --exclude="\.git/.*"
FSWATCH_ARGS += --exclude="dist-newstyle/.*"
FSWATCH_ARGS += --exclude="$(OUT_DIR)/.*"
FSWATCH_ARGS += --exclude="$(TMP_DIR)/.*"
FSWATCH_ARGS += "."

.PHONY: watch
watch:
	$(FSWATCH) $(FSWATCH_ARGS) | xargs -n1 -I{} make build


########################################
# Start local server with BrowserSync
########################################

BROWSER_SYNC ?= $(wildcard $(shell which browser-sync))

BROWSER_SYNC_ARGS += start
BROWSER_SYNC_ARGS += --server
BROWSER_SYNC_ARGS += --files "."
BROWSER_SYNC_ARGS += --no-ui
BROWSER_SYNC_ARGS += --reload-delay 500
BROWSER_SYNC_ARGS += --reload-debounce 500

.PHONY: serve
serve: check-browser-sync
	@(cd $(OUT_DIR) && $(BROWSER_SYNC) $(BROWSER_SYNC_ARGS))


########################################
# Test site with:
# - html-validate
# - feed-validator (optional)
# - HTMLProofer (optional)
# - EPUBCheck (optional)
########################################


# html-validate

HTML_VALIDATE ?= $(wildcard $(shell which html-validate))

HTML_VALIDATE_ARGS += .

.PHONY: test-html-validate
test-html-validate: check-html-validate
	@echo "Checking HTML with html-validate..."
	@(cd $(OUT_DIR) && $(HTML_VALIDATE) $(HTML_VALIDATE_ARGS))


# feed-validator

FEED_VALIDATOR ?= $(wildcard $(shell which feed-validator))

FEED_VALIDATOR_ARGS += --config ../.feed-validator.config.js
FEED_VALIDATOR_ARGS += --no-showfeed
FEED_VALIDATOR_ARGS += rss.xml

.PHONY: test-feed-validator
test-feed-validator: check-feed-validator
	@echo "Checking RSS with feed-validator..."
	@(cd $(OUT_DIR) && $(FEED_VALIDATOR) $(FEED_VALIDATOR_ARGS))


# HTMLProofer

HTML_PROOFER ?= $(wildcard $(shell which htmlproofer))

HTML_PROOFER_ARGS += --check-html
HTML_PROOFER_ARGS += --check-img-http
HTML_PROOFER_ARGS += --check-opengraph
HTML_PROOFER_ARGS += --file-ignore="/\.\/assets\/.*\.html/"
ifeq ($(EXTERNAL_LINKS),)
HTML_PROOFER_ARGS += --disable-external
endif
HTML_PROOFER_ARGS += --report-eof-tags
HTML_PROOFER_ARGS += --report-invalid-tags
HTML_PROOFER_ARGS += --report-missing-names
HTML_PROOFER_ARGS += --report-missing-doctype
HTML_PROOFER_ARGS += --report-mismatched-tags
HTML_PROOFER_ARGS += --report-script-embeds
HTML_PROOFER_ARGS += .

.PHONY: test-html-proofer
test-html-proofer: check-html-proofer
	@echo "Checking HTML with HTMLProofer..."
	@(cd $(OUT_DIR) && $(HTML_PROOFER) $(HTML_PROOFER_ARGS))


# EPUBCheck

EPUBCHECK ?= $(wildcard $(shell which epubcheck))

EPUBCHECK_ARGS += --customMessages .epubcheck.tsv
EPUBCHECK_ARGS += $(OUT_DIR)/plfa.epub

.PHONY: test-epubcheck
test-epubcheck: check-epubcheck
	@echo "Checking EPUB with EPUBCheck..."
	@$(EPUBCHECK) $(EPUBCHECK_ARGS)


# Ace by Daisy

ACE ?= $(wildcard $(shell which ace))

ACE_ARGS += --lang=en
ACE_ARGS += --tempdir=$(TMP_DIR)/ace
ACE_ARGS += --outdir=$(TMP_DIR)/ace
ACE_ARGS += $(OUT_DIR)/plfa.epub

.PHONY: test-ace
test-ace: check-ace
	@echo "Checking EPUB with Ace by DAISY..."
	@$(ACE) $(ACE_ARGS)
	@echo "See report: $(TMP_DIR)/ace/report.html"


########################################
# Dependencies
########################################

.PHONY: check-haskell
check-haskell:
ifeq (,$(CABAL))
	@echo "This task requires GHC and Cabal:"
	@echo "https://www.haskell.org/ghcup/"
	@exit 1
endif

.PHONY: check-html-minifier
ifeq (,$(HTML-MINIFIER))
check-html-minifier: check-node
	@$(eval HTML_MINIFIER := npm_config_yes=true npx html-minifier)
endif

.PHONY: check-browser-sync
ifeq (,$(BROWSER_SYNC))
check-browser-sync: check-node
	@$(eval BROWSER_SYNC := npm_config_yes=true npx browser-sync)
endif

.PHONY: check-feed-validator
ifeq (,$(FEED_VALIDATOR))
check-feed-validator: check-node
	@$(eval FEED_VALIDATOR := npm_config_yes=true npx feed-validator)
endif

.PHONY: check-html-validate
ifeq (,$(HTML_VALIDATE))
check-html-validate: check-node
	@$(eval HTML_VALIDATE := npm_config_yes=true npx html-validate)
endif

.PHONY: check-ace
ifeq (,$(ACE))
check-ace: check-node
	@$(eval ACE := npm_config_yes=true npx @daisy/ace)
endif

.PHONY: check-node
ifeq (,$(NPX))
check-node:
	@echo "This task requires Node.js:"
	@echo "https://nodejs.org/en/download/"
	@exit 1
endif

.PHONY: check-html-proofer
ifeq (,$(HTML_PROOFER))
check-html-proofer: check-rbenv
	@$(RBENV) exec gem install --silent bundler
	@$(RBENV) exec bundle install --quiet
	@$(eval HTML_PROOFER := $(RBENV) exec bundle exec htmlproofer)
endif

.PHONY: check-rbenv
ifeq (,$(RBENV))
check-rbenv:
	@echo "This task requires RBEnv:"
	@echo "https://github.com/rbenv/rbenv#installation"
	@exit 1
endif

.PHONY: check-fswatch
ifeq (,$(FSWATCH))
check-fswatch:
	@echo "This task requires fswatch:"
	@echo "https://github.com/emcrisostomo/fswatch#getting-fswatch"
	@exit 1
endif

.PHONY: check-epubcheck
ifeq (,$(EPUBCHECK))
check-epubcheck:
	@echo "This task requires epubcheck:"
	@echo "https://www.w3.org/publishing/epubcheck/"
	@exit 1
endif
