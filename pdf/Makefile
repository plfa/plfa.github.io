# To use the makefile, specify the path to source files under SRC
# and the path to pandoc-filters under FILTERS


.PHONY: all clean

SRC := ../src
SITE := ../_site
front_and_back := latex/plfa/frontmatter/dedication.tex latex/plfa/frontmatter/README.tex\
	latex/plfa/frontmatter/preface.tex latex/plfa/backmatter/acknowledgements.tex
lagda_md_files := $(shell find $(SRC) -name '*.lagda.md')
transpiled_files := $(patsubst $(SRC)/%.md,lagda_tex/%.tex,$(lagda_md_files))
latex_files := $(patsubst $(SRC)/%.lagda.md,latex/%.tex,$(lagda_md_files)) 
pdfs := $(patsubst $(SRC)/%.lagda.md,pdf/%.pdf,$(lagda_md_files))

# for make to clean file in subdirectories
# https://stackoverflow.com/questions/4210042/exclude-directory-from-find-command
SUBDIR_ROOTS := tex latex 
DIRS := . $(shell find $(SUBDIR_ROOTS) -type d)
GARBAGE_TYPES         := *.aux *.log *.out *.ptb *.blg *.fdb_latexmk *.agdai *.fls
GARBAGE_TYPED_FOLDERS := $(foreach DIR, $(DIRS), $(addprefix $(DIR)/,$(GARBAGE_TYPES)))

all: all_tex plfa.pdf

# A pdf for the whole book
plfa.pdf: $(latex_files) plfa.tex $(front_and_back)
	latexmk -pdf -lualatex -use-make plfa.tex

plfa-sample.pdf: $(latex_files) plfa-sample.tex $(front_and_back)
	latexmk -pdf -lualatex -use-make plfa-sample.tex

all_tex:  $(transpiled_files)
all_latex: $(latex_files)
all_pdfs : $(pdfs)



# General Rules

# from https://stackoverflow.com/questions/48267813/makefile-compile-objects-to-different-directory-and-build-from-there
# make a different directory for lagda.tex
# --shift-heading-level-by=-1 is a good choice 
# when converting HTML or Markdown documents that use an initial level-1 heading 
# also can try treat first heading as chapter
# by using --top-level-division=chapter
# for the document title and level-2+ headings for sections.
lagda_tex/%.lagda.tex : $(SRC)/%.lagda.md \
		codeblocks.lua rewrite-links.lua header-id.lua \
		lagdamd2tex_chapter.latex 
	@echo "Transpiling $< into $@"
	@mkdir -p '$(@D)'
	pandoc $<   --indented-code-classes=default \
	--lua-filter ./codeblocks.lua \
	--lua-filter ./rewrite-links.lua \
	--lua-filter ./header-id.lua \
	--top-level-division=chapter \
	-o $@ \
	--template=lagdamd2tex_chapter.latex

# run agda under same directory with lagda.tex	
latex/%.tex : lagda_tex/%.lagda.tex 
	cd lagda_tex; agda --latex-dir=../latex \
	--latex $(subst lagda_tex/,,$<)


pdf/%.pdf: latex/%.tex
	@echo $<
	latexmk -pdf -output-directory="pdf" -lualatex -use-make $<

# Specific rules for .md files, could be optimized!
# for general frontmatter
latex/plfa/frontmatter/%.tex : $(SRC)/plfa/frontmatter/%.md codeblocks-readme.lua
	@echo "Transpiling $< into $@"
	@mkdir -p '$(@D)'
	pandoc $<   --indented-code-classes=default \
	--lua-filter ./codeblocks-readme.lua \
	--lua-filter ./header-id.lua \
	--top-level-division=chapter \
	-o $@ \
	--template=lagdamd2tex_chapter.latex
# for readme
latex/plfa/frontmatter/README.tex : ../README.md codeblocks-readme.lua header-id.lua handle-badges.lua \
					lagdamd2tex_chapter.latex
	@echo "Transpiling $< into $@"
	@mkdir -p '$(@D)'
	pandoc $<   --indented-code-classes=default \
	--lua-filter ./codeblocks-readme.lua \
	--lua-filter ./header-id.lua \
	--lua-filter ./handle-badges.lua \
	--top-level-division=chapter \
	-o $@ \
	--template=lagdamd2tex_chapter.latex

# process for acknowledgements
# generate in _site/acknowledgements.md
../_site/acknowledgements.md : $(SRC)/plfa/backmatter/acknowledgements.md
	cd ..; stack build && stack exec site build

# transpile once to html to unify the lists
acknowledgements.html : $(SITE)/acknowledgements.md
	pandoc -o $@ $<

# compile the above version to latex
latex/plfa/backmatter/acknowledgements.tex : acknowledgements.html lagdamd2tex_acknowledgement.latex
	@echo "Transpiling $< into $@"
	@mkdir -p '$(@D)'
	pandoc $<   --indented-code-classes=default \
	--top-level-division=chapter \
	-o $@ \
	--template=lagdamd2tex_acknowledgement.latex


# general backmatter
latex/plfa/backmatter/%.tex : $(SRC)/plfa/backmatter/%.md codeblocks-readme.lua lagdamd2tex_chapter.latex
	@echo "Transpiling $< into $@"
	@mkdir -p '$(@D)'
	pandoc $<   --indented-code-classes=default \
	--lua-filter ./codeblocks-readme.lua \
	--lua-filter ./header-id.lua \
	--top-level-division=chapter \
	-o $@ \
	--template=lagdamd2tex_chapter.latex



clean:
	$(RM) -rf $(GARBAGE_TYPED_FOLDERS)

