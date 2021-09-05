#################################################################################
# Configuration
#################################################################################

PDF_DIR          := book
PDF_TEMPLATE_DIR := $(PDF_DIR)/templates
PDF_LUA_DIR      := $(PDF_DIR)/lua
MD_DIR           := src
LAGDA_TEX_DIR    := $(TMP_DIR)/lagda_tex
TEX_DIR          := $(TMP_DIR)/tex
FONTS_DIR        := $(PDF_DIR)/fonts
FONTS            := $(wildcard $(FONTS_DIR)/*.ttf)


#################################################################################
# Helper functions for translating paths
#################################################################################

# Convert MD_DIR/%.md to its modified source path
define MD_PATH
$(patsubst $(MD_DIR)/%/acknowledgements.md,$(TMP_DIR)/%/acknowledgements.md,\
	$(patsubst $(PDF_DIR)/pdf.tex,$(TMP_DIR)/pdf.tex,$(1)))
endef

# Convert MD_DIR/%.lagda.md to LAGDA_TEX_DIR/%.lagda.tex
define LAGDA_TEX_PATH
$(patsubst $(MD_DIR)/%.lagda.md,$(LAGDA_TEX_DIR)/%.lagda.tex,$(1))
endef

# Convert MD_DIR/%.md to LAGDA_TEX_DIR/%.lagda.tex or TEX_DIR/%.tex
#
# NOTE: This logic is partially duplicated in hs/Main.hs:addTexPath:texPath.
#
define TEX_PATH
$(patsubst $(TMP_DIR)/%,$(TEX_DIR)/%,\
	$(patsubst $(PDF_DIR)/%,$(TEX_DIR)/%,\
		$(patsubst README.md,$(TEX_DIR)/plfa/frontmatter/README.tex,\
			$(patsubst $(MD_DIR)/%.md,$(TEX_DIR)/%.tex,\
				$(patsubst $(MD_DIR)/%.lagda.md,$(TEX_DIR)/%.tex,$(1))))))
endef


#################################################################################
# Lists of source and intermediate files
#################################################################################

PDF_LUA_SCRIPTS  := $(wildcard $(PDF_LUA_DIR)/*.lua)
PDF_STATIC_FILES := $(PDF_DIR)/pdf.tex $(FONTS)
MD_FILES         := README.md $(wildcard $(MD_DIR)/plfa/**/*.md)
LAGDA_MD_FILES   := $(filter %.lagda.md,$(MD_FILES))
LAGDA_TEX_FILES  := $(call LAGDA_TEX_PATH,$(LAGDA_MD_FILES))
TEX_FILES        := $(call TEX_PATH,$(MD_FILES) $(TMP_DIR)/pdf.tex $(PDF_STATIC_FILES))


#################################################################################
# Compile PLFA to a PDF using Pandoc and Latexmk
#################################################################################

.PHONY: pdf pdf-build
pdf: pdf-build
pdf-build: $(SITE_DIR)/plfa.pdf

$(SITE_DIR)/plfa.pdf: $(TEX_FILES)
	@echo "Building PDF"
	@cd $(TEX_DIR) && latexmk -pdf -lualatex -use-make -halt-on-error pdf.tex
	@cp $(TEX_DIR)/pdf.pdf $(SITE_DIR)/plfa.pdf


#################################################################################
# Definitions of various compilation tasks
#################################################################################

# Copy static files needed by PDF compilation
define MK_COPYSTATIC_RULE
src := $(1)
dst := $(2)
$$(dst): $$(src)
	@echo "Copy $$< to $$@"
	@mkdir -p '$$(@D)'
	@cp $$< $$@
endef

# Copy static files from PDF_DIR/% to TEX_DIR/%
$(foreach static_file,\
	$(PDF_STATIC_FILES),\
	$(eval $(call MK_COPYSTATIC_RULE,\
		$(call MD_PATH,$(static_file)),\
		$(call TEX_PATH,$(static_file)))))


# Compile Markdown files to LaTeX
#
# NOTE: Passing --indented-code-classes=default sets the class for /indented/ code blocks
#       to 'default', which lets us distinguish them from /fenced/ code blocks without a
#       class. That's important, since fenced code blocks are checked by Agda, but indented
#       code blocks are /not/, so latex-render-codeblocks.lua needs to be able to tell the
#       difference.
#
define MK_MD2TEX_RULE
src := $(1)
dst := $(2)
$$(dst): $$(src) $(PDF_LUA_SCRIPTS) | setup-install-pandoc
	@echo "Compile $$< to $$@"
	@mkdir -p '$$(@D)'
	@$(PANDOC) \
		--top-level-division=chapter \
    --indented-code-classes=default \
		--lua-filter=$(PDF_LUA_DIR)/remove-badges.lua -M badge-url=https://img.shields.io/badge/ \
		--lua-filter=$(PDF_LUA_DIR)/latex-render-codeblocks.lua -M unchecked-files=README.md \
		--lua-filter=$(PDF_LUA_DIR)/single-file-links.lua \
		$$< -o $$@
endef

# Compile .md files (from MD_DIR/%.md to TEX_DIR/%.tex)
$(foreach md_file,\
	$(filter-out %.lagda.md,$(MD_FILES)),\
	$(eval $(call MK_MD2TEX_RULE,\
		$(call MD_PATH,$(md_file)),\
		$(call TEX_PATH,$(md_file)))))

# Compile .lagda.md files (from MD_DIR/%.md to LAGDA_TEX_DIR/%.lagda.tex)
$(foreach lagda_md_file,\
	$(LAGDA_MD_FILES),\
	$(eval $(call MK_MD2TEX_RULE,\
		$(lagda_md_file),\
		$(call LAGDA_TEX_PATH,$(lagda_md_file)))))


# Compile Literate Agda files to LaTeX
define MK_LAGDA_MD2TEX_RULE
src := $(1)
dst := $(2)
$$(dst): $$(src) $(LAGDA_TEX_FILES) | setup-install-agda setup-check-latexmk
	@$(AGDA) --include-path=$(LAGDA_TEX_DIR) --latex --latex-dir=$(TEX_DIR) $$<
endef

# Compile .lagda.tex files (from LAGDA_TEX_DIR/%.lagda.tex to TEX_DIR/%.tex)
$(foreach lagda_md_file,\
	$(LAGDA_MD_FILES),\
	$(eval $(call MK_LAGDA_MD2TEX_RULE,\
		$(call LAGDA_TEX_PATH,$(lagda_md_file)),\
		$(call TEX_PATH,$(lagda_md_file)))))



#################################################################################
# Tasks for files that are generated by Hakyll
#################################################################################

$(TMP_DIR)/pdf.tex: $(PDF_DIR)/pdf.tex $(MD_DIR)/plfa/toc.metadata
	@make build

# Generated by Hakyll
$(TMP_DIR)/plfa/backmatter/acknowledgements.md: $(MD_DIR)/plfa/backmatter/acknowledgements.md
	@make build
