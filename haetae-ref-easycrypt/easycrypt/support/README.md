# Project-owned EasyCrypt support

`RefJasminNTTLoop.ec` is the checked loop-refinement support required by the
target NTT and mode-2 matrix proofs.  It is kept inside this project because
the required 18-bit inverse-NTT entry theorem is not present in the historical
support snapshot under `../haetae-ntt-verify/easycrypt-ct`.

The verification scripts give this directory precedence over the historical
support directory on the EasyCrypt include path (EasyCrypt resolves duplicate
theory names from the last matching include directory).  The remaining
imported theories are still loaded from that directory and pinned by
`manifests/ntt-proof-support.sha256`.  This arrangement makes the proof gates
reproducible from committed bytes without changing the historical support
tree.
