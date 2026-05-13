MAIN = haetae-provable-security-reimplementation-guide
LATEX = pdflatex
FLAGS = -interaction=nonstopmode -halt-on-error

.PHONY: all clean distclean

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex
	$(LATEX) $(FLAGS) $(MAIN)
	$(LATEX) $(FLAGS) $(MAIN)

clean:
	rm -f *.aux *.log *.out *.toc

distclean: clean
	rm -f $(MAIN).pdf
