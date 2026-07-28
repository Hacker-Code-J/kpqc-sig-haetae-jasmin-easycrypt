BUILD_DIR := build
MAINS := \
	HAETAERefinementMap \
	TargetKeygenShakeStream \
	TargetKeygenUniformXofLeaf \
	TargetKeygenEtaSampler \
	TargetKeygenSamplerCallers \
	TargetKeygenMode2Parent
PDFS := $(addprefix $(BUILD_DIR)/,$(addsuffix .pdf,$(MAINS)))
PDFLATEX := pdflatex
PDFLATEX_FLAGS := -interaction=nonstopmode -halt-on-error -file-line-error \
	-output-directory=$(BUILD_DIR)

.PHONY: all clean list

all: $(PDFS)

$(BUILD_DIR)/%.pdf: %.tex | $(BUILD_DIR)
	$(PDFLATEX) $(PDFLATEX_FLAGS) $<
	$(PDFLATEX) $(PDFLATEX_FLAGS) $<

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

list:
	@printf '%s\n' $(PDFS)

clean:
	rm -rf $(BUILD_DIR)
