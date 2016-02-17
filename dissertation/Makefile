dissertation.pdf: *.tex references.bib
	make -C diagrams all
	pdflatex dissertation
	bibtex dissertation
	pdflatex dissertation
	pdflatex dissertation

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.toc
	rm dissertation.pdf
	make -C diagrams clean
