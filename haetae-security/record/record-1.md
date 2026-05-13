Do the next work in this order:

  1. Stop adding theorem wrappers. The top-level bound now compiles; more wrappers will not improve assurance.
  2. Create a paper-correspondence gap table for every scaffolded definition:
      - module_sis_eval = polyveck_zero
      - extractor returns polyvecl_zero
      - ROM output is deterministic zero
      - FS/rejection bounds are zeroed
  3. Replace the algebra first. Define the real HAETAE polynomial/module layer:
      - coefficients modulo q
      - polynomial arithmetic modulo x^n + 1
      - vector/matrix multiplication
      - highbits/lowbits/decompose/hint logic
      - concrete Module-SIS relation and norm bounds
  4. Then replace signing/verification. Implement real HAETAE keygen_internal, sign_internal, verify_internal, and prove correctness for those definitions.
  5. Then redo extraction honestly. Replace the current zero extractor with:
      - two accepting transcripts with same commitment/message hash
      - distinct challenges
      - compute response/challenge differences
      - prove the result satisfies bimodal MSIS
      - prove bimodal MSIS maps to concrete Module-SIS
  6. Only after that, redo distributions and bounds.
      - exact challenge distribution
      - exact rejection sampling predicate
      - nonzero FS-with-aborts/ROM programming bound
      - adversary query-count parameters instead of zero constants