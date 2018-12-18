agda := $(shell find src tspl -type f -name '*.lagda')
agdai := $(shell find src tspl -type f -name '*.agdai')
markdown := $(subst tspl/,out/,$(subst src/,out/,$(subst .lagda,.md,$(agda))))
PLFA_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
AGDA2HTML_FLAGS := --verbose --link-to-local-agda-names --use-jekyll=out/


# Build PLFA and test hyperlinks
test: build
	ruby -S bundle exec htmlproofer _site


# Build PLFA and test hyperlinks offline
test-offline: build
	ruby -S bundle exec htmlproofer _site --disable-external


statistics:
	hs/agda-count


out/:
	mkdir -p out/


# Build PLFA pages
out/%.md: src/%.lagda | out/
	agda2html $(AGDA2HTML_FLAGS) -i $< -o $@ 2>&1 \
		| sed '/^Generating.*/d; /^Warning\: HTML.*/d; /^reached from the.*/d; /^\s*$$/d'
	@sed -i '1 s|---|---\nsrc       : $(<)|' $@


# Build TSPL pages
out/%.md: tspl/%.lagda | out/
	agda2html $(AGDA2HTML_FLAGS) -i $< -o $@ -- --include-path=$(realpath src) 2>&1 \
		| sed '/^Generating.*/d; /^Warning\: HTML.*/d; /^reached from the.*/d; /^\s*$$/d'
	@sed -i '1 s|---|---\nsrc       : $(<)|' $@


# Start server
serve:
	ruby -S bundle exec jekyll serve --incremental


# Start background server
server-start:
	ruby -S bundle exec jekyll serve --no-watch --detach


# Stop background server
server-stop:
	pkill -f jekyll


# Build website using jekyll
build: AGDA2HTML_FLAGS += --link-to-agda-stdlib
build: $(markdown)
	ruby -S bundle exec jekyll build


# Build website using jekyll offline
build-offline: $(markdown)
	ruby -S bundle exec jekyll build


# Build website using jekyll incrementally
build-incremental: AGDA2HTML_FLAGS += --link-to-agda-stdlib
build-incremental: $(markdown)
	ruby -S bundle exec jekyll build --incremental


# Remove all auxiliary files
clean:
ifneq ($(strip $(agdai)),)
	rm $(agdai)
endif


# Remove all generated files
clobber: clean
	ruby -S bundle exec jekyll clean
	rm -rf out/

.phony: clobber


# MacOS Setup (install Bundler)
macos-setup:
	brew install libxml2
	ruby -S gem install bundler --no-ri --no-rdoc
	ruby -S gem install pkg-config --no-ri --no-rdoc -v "~> 1.1"
	ruby -S bundle config build.nokogiri --use-system-libraries
	ruby -S bundle install

.phony: macos-setup


# Travis Setup (install Agda, the Agda standard library, agda2html, acknowledgements, etc.)
travis-setup:\
	$(HOME)/.local/bin/agda\
	$(HOME)/.local/bin/agda2html\
	$(HOME)/.local/bin/acknowledgements\
	$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src\
	$(HOME)/.agda/defaults\
	$(HOME)/.agda/libraries

.phony: travis-setup


travis-install-agda2html: $(HOME)/.local/bin/agda2html

$(HOME)/.local/bin/agda2html:
	curl -L https://github.com/wenkokke/agda2html/archive/master.zip -o $(HOME)/agda2html-master.zip
	unzip -qq $(HOME)/agda2html-master.zip -d $(HOME)
	cd $(HOME)/agda2html-master;\
		stack install

travis-uninstall-agda2html:
	rm -rf $(HOME)/agda2html-master/
	rm $(HOME)/.local/bin/agda2html

travis-reinstall-agda2html: travis-uninstall-agda2html travis-install-agda2html

.phony: travis-install-agda2html travis-uninstall-agda2html travis-reinstall-agda2html


travis-install-acknowledgements: $(HOME)/.local/bin/acknowledgements

$(HOME)/.local/bin/acknowledgements:
	curl -L https://github.com/plfa/acknowledgements/archive/master.zip -o $(HOME)/acknowledgements-master.zip
	unzip -qq $(HOME)/acknowledgements-master.zip -d $(HOME)
	cd $(HOME)/acknowledgements-master;\
		stack install

travis-uninstall-acknowledgements:
	rm -rf $(HOME)/acknowledgements-master/
	rm $(HOME)/.local/bin/acknowledgements

travis-reinstall-acknowledgements: travis-uninstall-acknowledgements travis-reinstall-acknowledgements

.phony: travis-install-acknowledgements travis-uninstall-acknowledgements travis-reinstall-acknowledgements


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
	curl -L https://github.com/agda/agda/archive/v$(AGDA_VERSION).zip -o $(HOME)/agda-$(AGDA_VERSION).zip
	unzip -qq $(HOME)/agda-$(AGDA_VERSION).zip -d $(HOME)
	cd $(HOME)/agda-$(AGDA_VERSION);\
		stack install --stack-yaml=stack-8.0.2.yaml

travis-uninstall-agda:
	rm -rf $(HOME)/agda-$(AGDA_VERSION)/
	rm -f $(HOME)/.local/bin/agda
	rm -f $(HOME)/.local/bin/agda-mode

travis-reinstall-agda: travis-uninstall-agda travis-install-agda

.phony: travis-install-agda travis-uninstall-agda travis-reinstall-agda


travis-install-agda-stdlib: $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src

$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src:
	curl -L https://github.com/agda/agda-stdlib/archive/v$(AGDA_STDLIB_VERSION).zip -o $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION).zip
	unzip -qq $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION).zip -d $(HOME)
	mkdir -p $(HOME)/.agda

travis-uninstall-agda-stdlib:
	rm $(HOME)/.agda/defaults
	rm $(HOME)/.agda/libraries
	rm -rf $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/

travis-reinstall-agda-stdlib: travis-uninstall-agda-stdlib travis-install-agda-stdlib

.phony: travis-install-agda-stdlib travis-uninstall-agda-stdlib travis-reinstall-agda-stdlib
