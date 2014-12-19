writeup.pdf: writeup.tex effects-writeup.bib
	pdflatex writeup.tex -output-directory=~/Dropbox/Public
	bibtex writeup.aux
	pdflatex writeup.tex -output-directory=~/Dropbox/Public
	pdflatex writeup.tex -output-directory=~/Dropbox/Public
