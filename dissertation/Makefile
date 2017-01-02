PATH := /home/jirka/Projects/pygments-main:$(PATH)

dissertation.pdf: *.tex references.bib
	xelatex -shell-escape dissertation
	bibtex dissertation
	xelatex -shell-escape dissertation
	xelatex -shell-escape dissertation

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.toc
	rm dissertation.pdf
