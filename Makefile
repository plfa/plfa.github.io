agda := $(wildcard src/*.lagda)
agdai := $(wildcard src/*.agdai)
markdown := $(subst src/,out/,$(subst .lagda,.md,$(agda)))

all: $(markdown)

out/:
	mkdir -p out

out/%.md: src/%.lagda out/
	agda2html --verbose --link-to-agda-stdlib --jekyll-root=out/ -i $< -o $@


# serve website using jekyll
serve:
	ruby -S bundle exec jekyll serve

.phony: serve


# remove all auxiliary files
clean:
ifneq ($(strip $(agdai)),)
	rm $(agdai)
endif

.phony: clean


# remove all generated files
clobber: clean
	ruby -S bundle exec jekyll clean
ifneq ($(strip $(markdown)),)
	rm $(markdown)
endif
	rmdir out/

.phony: clobber


# install bundler, and gem dependencies
setup:
	ruby -S gem install bundler --no-ri --no-rdoc
	ruby -S bundle install

.phony: setup


# install agda, agda-stdlib, and agda2html
travis-setup:\
	$(HOME)/agda-master/\
	$(HOME)/agda-stdlib-master/\
	$(HOME)/agda2html-master/

.phony: travis-setup

$(HOME)/agda-master/:
	curl -L https://github.com/agda/agda/archive/master.zip -o $(HOME)/agda-master.zip
	unzip -qq $(HOME)/agda-master.zip -d $(HOME)
	cd $(HOME)/agda-master;\
		stack install --stack-yaml=stack-8.2.2.yaml

$(HOME)/agda-stdlib-master/:
	curl -L https://github.com/agda/agda-stdlib/archive/master.zip -o $(HOME)/agda-stdlib-master.zip
	unzip -qq $(HOME)/agda-stdlib-master.zip -d $(HOME)
	mkdir $(HOME)/.agda
	echo "standard-library" > $(HOME)/.agda/defaults
	echo "$(HOME)/agda-stdlib-master/standard-library.agda-lib" > $(HOME)/.agda/libraries

$(HOME)/agda2html-master/:
	curl -L https://github.com/wenkokke/agda2html/archive/master.zip -o $(HOME)/agda2html-master.zip
	unzip -qq $(HOME)/agda2html-master.zip -d $(HOME)
	cd $(HOME)/agda2html-master;\
		stack install
