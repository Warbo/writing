all : report.pdf

# Get styles
mathpartir.sty :
	wget "http://cristal.inria.fr/~remy/latex/mathpartir.sty"

mmm.sty :
	wget "http://www.ccs.neu.edu/course/csg264/latex/mmm.sty"

psfig.sty :
	wget "http://anorien.csc.warwick.ac.uk/mirrors/CTAN/graphics/psfig/psfig.sty"

cmd := pdflatex -interaction=nonstopmode -halt-on-error --shell-escape report

report.pdf : ../Bibtex.bib background.tex evaluation.tex implementation.tex intro.tex report.tex contributions.tex examples.tex related.tex psfig.sty mmm.sty mathpartir.sty
	$(cmd)
	echo "RUNNING bibtex"
	bibtex report
	$(cmd)
	$(cmd)

clean :
	for EXT in aux bbl blg dvi log out pdf; do rm -f "report.$$EXT"; done

.PHONY : all clean
