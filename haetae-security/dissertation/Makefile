# Makefile for the HAETAE Provable-Security Verification Dissertation
# Usage:
#   make          -- build PDF (pdflatex + bibtex + pdflatex x2)
#   make clean    -- remove auxiliary files
#   make distclean -- also remove the PDF

MAIN    = main
LATEX   = pdflatex
BIBTEX  = bibtex
FLAGS   = -interaction=nonstopmode -halt-on-error

.PHONY: all inventory clean distclean

all: $(MAIN).pdf

inventory:
	./etc/count-easycrypt-declarations.sh > etc/easycrypt-declaration-counts.csv

$(MAIN).pdf: $(MAIN).tex bibliography/refs.bib \
             chapters/titlepage.tex \
             chapters/abstract.tex \
             chapters/acknowledgements.tex \
             chapters/ch01_introduction.tex \
             chapters/ch02_background.tex \
             chapters/ch03_proof_scope.tex \
             chapters/ch04_model_spec_correspondence.tex \
             chapters/ch04_easycrypt_framework.tex \
             chapters/ch05_security_games.tex \
             chapters/ch06_rom_programming.tex \
             chapters/ch07_sampler_freshness.tex \
             chapters/ch08_transcript_hops.tex \
             chapters/ch09_budgeted_lifting.tex \
             chapters/ch10_reductions_bounds.tex \
             chapters/ch11_pen_paper_reconstruction.tex \
             chapters/ch12_mathematical_cryptological_synthesis.tex \
             chapters/ch13_reproducibility.tex \
             chapters/ch14_conclusion.tex \
             chapters/app_manifest.tex \
             chapters/app_easycrypt_code_analysis.tex \
             chapters/app_mathematical_correspondence.tex \
             chapters/app_formal_easycrypt_semantics.tex \
             chapters/app_easycrypt_declaration_index.tex \
             chapters/app_curated_easycrypt_case_studies.tex
	$(LATEX) $(FLAGS) $(MAIN)
	$(BIBTEX) $(MAIN) || true
	$(LATEX) $(FLAGS) $(MAIN)
	$(LATEX) $(FLAGS) $(MAIN)

clean:
	rm -f *.aux *.bbl *.bcf *.blg *.log *.lot *.lof *.lol *.out *.run.xml *.toc *.idx *.ind *.ilg
	rm -f chapters/*.aux

distclean: clean
	rm -f $(MAIN).pdf
