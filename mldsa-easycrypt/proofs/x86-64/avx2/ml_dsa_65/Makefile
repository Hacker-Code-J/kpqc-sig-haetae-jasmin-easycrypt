SOURCE = ../../../../submodules/formosa-mldsa/x86-64/avx2/ml_dsa_65/
COMMON = ../../../../submodules/formosa-mldsa/x86-64/avx2/common
OARRAYS = ../../../arrays
JASMIN2EC = /usr/local/bin/jasmin2ec --output-array=$(OARRAYS)
KECCAK = ../../../../submodules/formosa-mldsa/formosa-keccak/src/amd64/

# --------------------------------------------------------------------
all: ec


ec: 
	env JASMINPATH="Common=$(COMMON):Keccak=$(KECCAK)" $(JASMIN2EC) $(SOURCE)/ml_dsa.jazz --array-model=old -o ml_dsa_65_avx2.ec \
	  -f ml_dsa_65_keygen \
	  -f ml_dsa_65_sign \
	  -f ml_dsa_65_verify
# 	env JASMINPATH="Common=$(COMMON):Keccak=$(KECCAK)" $(JASMIN2EC) $(SOURCE)/ml_dsa.jazz -o ml_dsa_65_avx2_barray.ec \
# 	  -f ml_dsa_65_keygen \
# 	  -f ml_dsa_65_sign \
# 	  -f ml_dsa_65_verify

clean:
	rm -f *.ec
