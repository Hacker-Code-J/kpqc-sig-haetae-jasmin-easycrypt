.RECIPEPREFIX := >
.DEFAULT_GOAL := all
.NOTPARALLEL:

TARGETS := all libs bins kat-bins sign-test api-test interop-test sampler-test sampler-ct test kat check-reference clean
.PHONY: prepare $(TARGETS)

# Do not apply the forwarding pattern to GNU make's own makefile lookup.
Makefile: ;

prepare:
>python3 scripts/materialize.py

$(TARGETS): prepare
>$(MAKE) -f build/baseline.mk $@

%: prepare
>$(MAKE) -f build/baseline.mk $@
