dissertation.pdf: *.tex references.bib
	lualatex dissertation
	bibtex dissertation
	lualatex dissertation
	lualatex dissertation

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.toc
	rm dissertation.pdf
