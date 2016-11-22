defense.pdf: defense.tex definitions.tex packages.tex references.bib
	xelatex defense
	bibtex defense
	xelatex defense
	xelatex defense

clean:
	rm -f *.aux *.bbl *.blg *.log *.maf *.mtc* *.nav *.snm *.out *.toc
	rm -f defense.pdf
