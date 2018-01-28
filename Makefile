agda := $(wildcard src/*.lagda)
agdai := $(wildcard src/*.agdai)
markdown := $(subst src/,out/,$(subst .lagda,.md,$(agda)))

default: $(markdown)

out/:
	mkdir out

out/%.md: src/%.lagda out/
	agda2html --verbose --link-to-agda-stdlib --jekyll-root=out/ -i $< -o $@

.phony: serve

serve:
	ruby -S gem install bundler --no-ri --no-rdoc
	ruby -S bundle install
	ruby -S bundle exec jekyll serve

.phony: clean

clean:
ifneq ($(strip $(agdai)),)
	rm $(agdai)
endif

.phony: clobber

clobber: clean
	ruby -S gem install bundler --no-ri --no-rdoc
	ruby -S bundle install
	ruby -S bundle exec jekyll clean
ifneq ($(strip $(markdown)),)
	rm $(markdown)
endif
	rmdir out/

setup:\
	$(HOME)/.local/bin/agda\
	$(HOME)/.local/bin/agda2html\
	$(HOME)/agda-stdlib-master/

.phony: setup

$(HOME)/.local/bin/agda:
	curl -L https://github.com/agda/agda/archive/master.zip -o agda-master.zip
	unzip -qq agda-master.zip
	cd agda-master;\
		stack install --stack-yaml=stack-8.2.2.yaml

$(HOME)/.local/bin/agda2html:
	curl -L https://github.com/wenkokke/agda2html/archive/master.zip -o agda2html-master.zip
	unzip -qq agda2html-master.zip
	cd agda2html-master;\
		stack install

$(HOME)/agda-stdlib-master/:
	curl -L https://github.com/agda/agda-stdlib/archive/master.zip -o agda-stdlib-master.zip
	unzip -qq agda-stdlib-master.zip -d $HOME
	mkdir $HOME/.agda
	$(file >$(HOME)/.agda/defaults,standard-library)
	$(file >$(HOME)/.agda/libraries,$(HOME)/agda-stdlib-master/standard-library.agda-lib)
