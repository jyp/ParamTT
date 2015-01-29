all:
	pdflatex tt4
	bibtex tt4; true
	pdflatex tt4
