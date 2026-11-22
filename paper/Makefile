# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

# Build zzn.pdf; intermediate files go in build/.
#
all: build/zzn.pdf build/supplement.pdf

build/zzn.pdf: zzn.tex references.bib $(wildcard figures/*.pdf)
	mkdir -p build
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory build zzn.tex
	cd build && BIBINPUTS=.. bibtex zzn
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory build zzn.tex
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory build zzn.tex

# The supplement; its intermediate files go in build-supp/.
#
build/supplement.pdf: supplement.tex references.bib $(wildcard figures/*.pdf)
	mkdir -p build build-supp
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory build-supp supplement.tex
	cd build-supp && BIBINPUTS=.. bibtex supplement
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory build-supp supplement.tex
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory build-supp supplement.tex
	cp build-supp/supplement.pdf build/supplement.pdf

clean:
	rm -rf build build-supp

.PHONY: all clean
