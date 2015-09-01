#! /usr/bin/env nix-shell
#! nix-shell -p gnumake -p bash -p haskellPackages.pandoc-citeproc -p panpipe -p panhandle -p ditaa -i bash
make -j2 -f <(tail -n+4 "$0") "$@"; exit "$?"

slides:
	pandoc -w dzslides --standalone --self-contained --mathml -o slides.html --filter=pandoc-citeproc --filter=panpipe --filter=panhandle slides.md

pdf :
	latex article
	bibtex article
	latex article
	pdflatex article

.PHONY : clean
clean :
	rm -f article.aux
	rm -f article.blg
	rm -f article.log
	rm -f article.pdf
	rm -f article.bbl
	rm -f article.dvi
	rm -f article.out
