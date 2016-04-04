fg2016.pdf: fg2016.tex definitions.tex references.bib
	pdflatex fg2016
	bibtex fg2016
	pdflatex fg2016
	pdflatex fg2016

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.toc
	rm fg2016.pdf
