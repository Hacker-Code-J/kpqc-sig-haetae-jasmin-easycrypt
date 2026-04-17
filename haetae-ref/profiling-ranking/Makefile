SHELL := /bin/sh

MARKDOWN_BUILD_SCRIPT := ./build_markdown_report.sh
LATEST_RESULTS := results/latest
MARKDOWN_REPORT := $(LATEST_RESULTS)/haetae_build_bin_profiling_report.md

.PHONY: all markdown clean distclean help

all: markdown

markdown: $(MARKDOWN_REPORT)

$(MARKDOWN_REPORT): $(MARKDOWN_BUILD_SCRIPT) $(LATEST_RESULTS)
	$(MARKDOWN_BUILD_SCRIPT) $(LATEST_RESULTS)

clean:
	rm -rf $(LATEST_RESULTS)/visualizations
	rm -f $(LATEST_RESULTS)/haetae_build_bin_profiling_report.md

distclean: clean

help:
	@printf '%s\n' \
	  'Targets:' \
	  '  make markdown Build the Markdown report and PNG charts from results/latest' \
	  '  make clean    Remove generated Markdown report and charts from results/latest' \
	  '  make help     Show this help text'
