• I added a new proof scaffold in NTTAlgebra.ec:1 modeled on formosa-mlkem/proof/eclib/NTTAlgebra.ec.

  This first layer does two things:

  - introduces NTT_vars and a factored NTT_opt module for HAETAE forward/inverse NTT,
  - proves the initial inlining equivalences inline_ntt and inline_invntt between NTT_Fq.NTT and NTT_opt.

  Verification: easycrypt compile NTTAlgebra.ec -I . succeeded.

  Changed files: NTTAlgebra.ec:1
  Simplifications made: I copied only the first proof layer from the MLKEM structure, not the full bsrev/naive/algebra pipeline yet.
  Remaining risks: this is only the decomposition and inline-equivalence stage. The next step, if we keep following the MLKEM style, is to add an NTT_bsrev layer and prove
  NTT_opt <=> NTT_bsrev.