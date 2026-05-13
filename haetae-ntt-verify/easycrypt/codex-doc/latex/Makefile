TEXS=proof-state-report.tex task-formulas-note.tex ref-jasmin-ntt-proof-report.tex ref-jasmin-ntt-lemma-notes.tex end-to-end-haetae-ntt-proof-status.tex haetae-ntt-full-verification-report.tex
PDFS=$(TEXS:.tex=.pdf)

.PHONY: all clean

all: $(PDFS)

%.pdf: %.tex
	pdflatex -interaction=nonstopmode -halt-on-error $<
	pdflatex -interaction=nonstopmode -halt-on-error $<

clean:
	rm -f *.aux *.log *.out *.pdf
