fg2016.pdf: fg2016-presentation.tex definitions.tex packages.tex references.bib
	xelatex fg2016-presentation
	bibtex fg2016-presentation
	xelatex fg2016-presentation
	xelatex fg2016-presentation

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.toc
	rm fg2016-presentation.pdf
