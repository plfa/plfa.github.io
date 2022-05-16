OUT_DIR := _site
TMP_DIR := _cache

# OS = {Windows_NT, Linux, Darwin}
ifneq ($(OS),Windows_NT)
OS := $(shell uname -s)
endif

CABAL ?= $(wildcard $(shell which cabal))
NPX ?= $(wildcard $(shell which npx))
RBENV ?= $(wildcard $(shell which rbenv))

.PHONY: default
default: build

########################################
# Command-line arguments
########################################

# make test-html-proofer:
#   - CHECK_EXTERNAL_LINKS:
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

CABAL_ARGS += --verbose=0

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

.PHONY: build
build: check-haskell check-html-minifier
	@$(CABAL) $(CABAL_ARGS) v2-run builder -- build
	@echo "Minifying HTML..."
	@$(HTML_MINIFIER) $(HTML_MINIFIER_ARGS)

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
# - cabal tests
########################################

.PHONY: test
test: test-html-validate
	@$(CABAL) $(CABAL_ARGS) v2-test


# HTMLProofer

HTML_PROOFER ?= $(wildcard $(shell which htmlproofer))

HTML_PROOFER_ARGS += --check-html
HTML_PROOFER_ARGS += --check-img-http
HTML_PROOFER_ARGS += --check-opengraph
HTML_PROOFER_ARGS += --file-ignore="/\.\/assets\/.*\.html/"
HTML_PROOFER_ARGS += --report-eof-tags
HTML_PROOFER_ARGS += --report-invalid-tags
HTML_PROOFER_ARGS += --report-missing-names
HTML_PROOFER_ARGS += --report-missing-doctype
HTML_PROOFER_ARGS += --report-mismatched-tags
HTML_PROOFER_ARGS += --report-script-embeds
HTML_PROOFER_ARGS += .

.PHONY: test-html-proofer
test-html-proofer: check-html-proofer
	@echo "Checking HTML..."
	@(cd $(OUT_DIR) && $(HTML_PROOFER) $(HTML_PROOFER_ARGS))


# html-validate

HTML_VALIDATE ?= $(wildcard $(shell which html-validate))

HTML_VALIDATE_ARGS += .

.PHONY: test-html-validate
test-html-validate: check-html-validate
	@echo "Checking HTML..."
	@(cd $(OUT_DIR) && $(HTML_VALIDATE) $(HTML_VALIDATE_ARGS))


# feed-validator

FEED_VALIDATOR ?= $(wildcard $(shell which feed-validator))

FEED_VALIDATOR_ARGS += --config ../.feed-validator.config.js
FEED_VALIDATOR_ARGS += --no-showfeed
FEED_VALIDATOR_ARGS += rss.xml

.PHONY: test-feed-validator
test-feed-validator: check-feed-validator
	@echo "Checking rss.xml..."
	@(cd $(OUT_DIR) && $(FEED_VALIDATOR) $(FEED_VALIDATOR_ARGS))


########################################
# Deploy blog
########################################

.PHONY: deploy
deploy:
	@if [[ `git status --porcelain` ]]; then echo "Uncommited changes!"; exit 1; fi
	@echo "Running tests..."
	@make test
	@echo "Backing up Agda interfaces..."
	@mkdir -p $(TMP_DIR)/agda-stdlib
	@if [ -d "agda-stdlib/_build" ]; then mv agda-stdlib/_build $(TMP_DIR)/agda-stdlib/; fi
	@echo "Deploying site..."
	git fetch --all
	git checkout -b main --track origin/main
	rsync -r --delete --exclude=$(OUT_DIR) --exclude=$(TMP_DIR) --exclude=.git --exclude=.gitignore --exclude=CNAME $(OUT_DIR)/ .
	git add -A
	git commit -m "Publish"
	git push origin main:main
	git checkout dev
	git branch -D main
	git submodule update --init
	if [ -d "$(TMP_DIR)/agda-stdlib/_build" ]; then mv $(TMP_DIR)/agda-stdlib/_build agda-stdlib/; fi




########################################
# Dependencies for build
########################################

.PHONY: check-haskell
check-haskell:
ifeq (,$(CABAL))
	@echo "This task requires GHC and Cabal:"
	@echo "https://www.haskell.org/ghcup/"
	@exit 1
endif

########################################
# Dependencies for watch
########################################

.PHONY: check-fswatch
ifeq (,$(FSWATCH))
check-fswatch:
	@echo "This task requires fswatch:"
	@echo "https://github.com/emcrisostomo/fswatch#getting-fswatch"
	@exit 1
endif


########################################
# Dependencies for serve
########################################

.PHONY: check-browser-sync
ifeq (,$(BROWSER_SYNC))
check-browser-sync: check-node
	@$(eval BROWSER_SYNC := npx --yes browser-sync)
endif

.PHONY: check-html-minifier
ifeq (,$(HTML-MINIFIER))
check-html-minifier: check-node
	@$(eval HTML_MINIFIER := npx --yes html-minifier)
endif

.PHONY: check-feed-validator
ifeq (,$(FEED_VALIDATOR))
check-feed-validator: check-node
	@$(eval FEED_VALIDATOR := npx --yes feed-validator)
endif

.PHONY: check-html-validate
ifeq (,$(HTML_VALIDATE))
check-html-validate: check-node
	@$(eval HTML_VALIDATE := npx --yes html-validate)
endif

.PHONY: check-node
ifeq (,$(NPX))
check-node:
	@echo "This task requires Node.js:"
	@echo "https://nodejs.org/en/download/"
	@exit 1
endif


########################################
# Dependencies for test
########################################

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
