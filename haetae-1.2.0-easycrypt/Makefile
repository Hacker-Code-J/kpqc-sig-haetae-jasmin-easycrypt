PYTHON ?= python3

.PHONY: all verify verify-new verify-ntt verify-generated test-gate extract check-extraction
all: verify
verify:
	$(PYTHON) scripts/verify.py
verify-new:
	$(PYTHON) scripts/verify.py --group new
verify-ntt:
	$(PYTHON) scripts/verify.py --group ntt
verify-generated:
	$(PYTHON) scripts/verify.py --group generated
test-gate:
	$(PYTHON) tests/test_verification_gate.py
extract:
	$(PYTHON) scripts/extract.py --write
check-extraction:
	$(PYTHON) scripts/extract.py --check
