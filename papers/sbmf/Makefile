.PHONY : default %.pdf clean realclean
.PRECIOUS : %.tex

default : PLFA.pdf

PLFA.pdf : PLFA.tex PLFA.bib
	pdflatex PLFA
	bibtex PLFA
	pdflatex PLFA
	bibtex PLFA
	pdflatex PLFA

final.zip : PLFA.tex PLFA.bib
	zip final.zip agda.sty llncs.cls PLFA.tex PLFA.bib splncsnat.bst figures/plfa-*.png figures/sf-*.png figures/raw.png figures/inherent.png

clean:
	rm -f *.aux *.log *.out *.ptb *.blg *.fdb_latexmk *.agdai *.fls

realclean: clean
	rm -f *.glob *.vo *.bbl latex/* PLFA.pdf
