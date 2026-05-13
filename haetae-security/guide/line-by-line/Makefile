TEXS := $(wildcard *-line-by-line-guide.tex)
PDFS := $(TEXS:.tex=.pdf)

.PHONY: all index clean

index: index.pdf

all: index.pdf $(PDFS)

%.pdf: %.tex
	pdflatex -interaction=nonstopmode -halt-on-error $<
	pdflatex -interaction=nonstopmode -halt-on-error $<

clean:
	rm -f *.aux *.log *.out *.toc *.pdf
