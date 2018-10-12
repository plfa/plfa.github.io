agda := $(wildcard src/*.lagda) $(wildcard src/**/*.lagda) $(wildcard tspl/*.lagda) $(wildcard tspl/**/*.lagda)
agdai := $(wildcard src/*.agdai) $(wildcard src/**/*.agdai) $(wildcard tspl/*.agdai) $(wildcard tspl/**/*.agdai)
markdown := $(subst tspl/,out/,$(subst src/,out/,$(subst .lagda,.md,$(agda))))
PLFA_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))

all: $(markdown)

test: build
	ruby -S bundle exec htmlproofer _site --disable-external

statistics:
	hs/agda-count

out/:
	mkdir -p out/

out/%.md: src/%.lagda | out/
	agda2html --verbose --link-to-agda-stdlib --link-to-local-agda-names --use-jekyll=out/ -i $< -o $@ 2>&1 \
		| sed '/^Generating.*/d; /^Warning\: HTML.*/d; /^reached from the.*/d; /^\s*$$/d'
	@sed -i '1 s|---|---\nsrc       : $(<)|' $@

# should fix this -- it's the same as above
out/%.md: tspl/%.lagda | out/
	agda2html --verbose --link-to-agda-stdlib --link-to-local-agda-names --use-jekyll=out/ -i $< -o $@ 2>&1 \
		| sed '/^Generating.*/d; /^Warning\: HTML.*/d; /^reached from the.*/d; /^\s*$$/d'
	@sed -i '1 s|---|---\nsrc       : $(<)|' $@

serve:
	ruby -S bundle exec jekyll serve

# start server
server-start:
	ruby -S bundle exec jekyll serve --no-watch --detach

# stop server
server-stop:
	pkill -f jekyll

# build website using jekyll
build: $(markdown)
	ruby -S bundle exec jekyll build

# build website using jekyll incrementally
build-incremental: $(markdown)
	ruby -S bundle exec jekyll build --incremental

# remove all auxiliary files
clean:
ifneq ($(strip $(agdai)),)
	rm $(agdai)
endif

# remove all generated files
clobber: clean
	ruby -S bundle exec jekyll clean
	rm -rf out/

# install bundler, and gem dependencies
macos-setup:
	brew install libxml2
	ruby -S gem install bundler --no-ri --no-rdoc
	ruby -S gem install pkg-config --no-ri --no-rdoc -v "~> 1.1"
	ruby -S bundle config build.nokogiri --use-system-libraries
	ruby -S bundle install

# install agda, agda-stdlib, and agda2html
travis-setup:\
	$(HOME)/.local/bin/agda\
	$(HOME)/.local/bin/agda2html\
	$(HOME)/.local/bin/acknowledgements\
	$(HOME)/agda-stdlib-master/src\
	$(HOME)/.agda/defaults\
	$(HOME)/.agda/libraries

$(HOME)/.agda/defaults:
	echo "standard-library" >> $(HOME)/.agda/defaults
	echo "plfa" >> $(HOME)/.agda/defaults

$(HOME)/.agda/libraries:
	echo "$(HOME)/agda-stdlib-master/standard-library.agda-lib" >> $(HOME)/.agda/libraries
	echo "$(PLFA_DIR)/plfa.agda-lib" >> $(HOME)/.agda/libraries

$(HOME)/.local/bin/agda:
	curl -L https://github.com/agda/agda/archive/master.zip -o $(HOME)/agda-master.zip
	unzip -qq $(HOME)/agda-master.zip -d $(HOME)
	cd $(HOME)/agda-master;\
		stack install --stack-yaml=stack-8.2.2.yaml

$(HOME)/.local/bin/agda2html:
	curl -L https://github.com/wenkokke/agda2html/archive/master.zip -o $(HOME)/agda2html-master.zip
	unzip -qq $(HOME)/agda2html-master.zip -d $(HOME)
	cd $(HOME)/agda2html-master;\
		stack install

$(HOME)/.local/bin/acknowledgements:
	curl -L https://github.com/plfa/acknowledgements/archive/master.zip -o $(HOME)/acknowledgements-master.zip
	unzip -qq $(HOME)/acknowledgements-master.zip -d $(HOME)
	cd $(HOME)/acknowledgements-master;\
		stack install

$(HOME)/agda-stdlib-master/src:
	curl -L https://github.com/agda/agda-stdlib/archive/master.zip -o $(HOME)/agda-stdlib-master.zip
	unzip -qq $(HOME)/agda-stdlib-master.zip -d $(HOME)
	mkdir -p $(HOME)/.agda

.phony: serve build test clean clobber macos-setup travis-setup

# workaround for a bug in agda2html
bugfix:
	@mkdir -p out
	@touch out/Nat.md
.phony: bugfix
