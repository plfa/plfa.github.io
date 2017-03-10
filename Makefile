agda := $(wildcard src/*.lagda)
markdown := $(subst src/,out/,$(subst .lagda,.md,$(agda)))

default: $(markdown)

out/:
	mkdir out

out/%.md: src/%.lagda out/
	agda2html --strip-implicit-args --link-to-agda-stdlib --link-local -i $< -o $@
