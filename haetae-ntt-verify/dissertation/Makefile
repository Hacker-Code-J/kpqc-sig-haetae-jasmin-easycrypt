# Makefile for the HAETAE NTT Verification Dissertation
# Usage:
#   make          -- build PDF (pdflatex + bibtex + pdflatex x2)
#   make clean    -- remove auxiliary files
#   make distclean -- also remove the PDF

MAIN    = main
LATEX   = pdflatex
BIBTEX  = bibtex
FLAGS   = -interaction=nonstopmode -halt-on-error

.PHONY: all clean distclean

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex bibliography/refs.bib \
             chapters/titlepage.tex \
             chapters/abstract.tex \
             chapters/acknowledgements.tex \
             chapters/ch01_introduction.tex \
             chapters/ch02_background.tex \
             chapters/ch03_haetae_ntt.tex \
             chapters/ch04_formal_framework.tex \
             chapters/ch05_field_ring.tex \
             chapters/ch06_montgomery.tex \
             chapters/ch07_ntt_spec.tex \
             chapters/ch08_algebra.tex \
             chapters/ch09_jasmin_impl.tex \
             chapters/ch10_refinement.tex \
             chapters/ch11_end_to_end.tex \
             chapters/ch12_conclusion.tex
	$(LATEX) $(FLAGS) $(MAIN)
	$(BIBTEX) $(MAIN) || true
	$(LATEX) $(FLAGS) $(MAIN)
	$(LATEX) $(FLAGS) $(MAIN)

clean:
	rm -f *.aux *.bbl *.blg *.log *.lot *.lof *.lol *.out *.toc *.idx *.ind *.ilg
	rm -f chapters/*.aux

distclean: clean
	rm -f $(MAIN).pdf
