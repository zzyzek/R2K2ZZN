# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

# Build zzn.pdf; intermediate files go in build/.
#
build/zzn.pdf: zzn.tex references.bib $(wildcard figures/*.pdf)
	mkdir -p build
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory build zzn.tex
	cd build && BIBINPUTS=.. bibtex zzn
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory build zzn.tex
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory build zzn.tex

clean:
	rm -rf build

.PHONY: clean
