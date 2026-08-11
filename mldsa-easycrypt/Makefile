# -*- Makefile -*-

# --------------------------------------------------------------------
EASYCRYPT ?= easycrypt
ECFLAGS   ?=
ECJOBS    ?= 3
ECRUNTEST ?= $(EASYCRYPT) runtest -jobs $(ECJOBS) $(ECFLAGS)

# --------------------------------------------------------------------
PHONY: default check extract clean

# --------------------------------------------------------------------
default: check

# --------------------------------------------------------------------
extract:
	$(MAKE) -C proofs/x86-64/avx2/ml_dsa_65

# --------------------------------------------------------------------
check: extract
	$(ECRUNTEST) config/tests.config all

# --------------------------------------------------------------------
clean:
	find proofs -name '*.eco' -print0 | xargs -0 rm -f
