# Processing Task: HAETAE EasyCrypt Security Proof

## Objective

Build and maintain a machine-checked EasyCrypt proof for the HAETAE digital
signature scheme. Use the Kyber KEM security development in `kyber-security/` as
the local style and proof-engineering reference, but do not copy KEM definitions
where a signature-specific game or reduction is required.

The expected top-level claim is an existential unforgeability statement for
HAETAE in the random-oracle model, with explicit reductions and failure terms
matching the paper-level HAETAE security argument.

## Reference Corpus

Treat `kyber-security/` as read-only reference material unless the task
explicitly asks for changes there.

The most useful reference files are:

- `kyber-security/PKE_ROM.ec` for abstract game definitions, adversary module
  types, probability lemmas, and left/right game conversion style.
- `kyber-security/KEM_ROM.ec` for random-oracle game structure and oracle
  module discipline.
- `kyber-security/MLWE.ec` for algebraic assumptions, random-oracle sampling,
  and reductions between concrete and ideal sampling games.
- `kyber-security/MLWE_PKE_Basic.ec` for compact game hops from a concrete
  scheme to MLWE assumptions and for correctness/failure-probability factoring.
- `kyber-security/MLWE_PKE.ec` for sampled-matrix and hash-derived matrix
  variants.
- `kyber-security/FO_TT.ec`, `FO_UU.ec`, and `FO_MLKEM.ec` only for large
  modular proof organization, query counting, lazy/eager random-oracle
  transitions, and final advantage-bound assembly.

Use Kyber's patterns for `clone import`, abstract theories, module types,
losslessness assumptions, `byequiv` game hops, `byphoare` failure bounds, and
final concrete advantage inequalities.

## HAETAE Inputs

Use the HAETAE algorithm descriptions and parameter names from:

- `HAETAE_v221122.pdf`
- `HAETAE_v230502.pdf`
- `HAETAE_v231129.pdf`
- `HAETAE_v240223.pdf`
- `HAETAE_v260204.pdf`
- `../haetae-ref/src/sign.c`
- `../haetae-ref/include/api.h`
- `../haetae-ref/include/params.h`
- `../haetae-ref/include/packing.h`

The C implementation is a guide to operational structure, not the primary
EasyCrypt theorem statement. Model the mathematical scheme first, then connect
implementation details only when a task explicitly asks for implementation
refinement.

Important HAETAE surfaces from `sign.c`:

- `crypto_sign_keypair_internal`: seed expansion, matrix expansion, secret
  sampling, rejection on secret norm, public-key packing.
- `crypto_sign_signature_internal`: message hash, signing randomness,
  hyperball sampling, challenge generation, rejection checks, hint generation,
  signature packing.
- `crypto_sign_verify_internal`: public-key unpacking, signature unpacking,
  norm check, reconstruction, challenge recomputation.

## Suggested EasyCrypt Layout

Keep the HAETAE proof files in `haetae-security/` next to this guide. Prefer
small, composable files over one large monolith.

Suggested starting layout:

- `Sig_ROM.ec`: abstract signature syntax, correctness, EUF-CMA/SUF-CMA-style
  games, signing oracle, verification predicate, and query bounds.
- `HAETAE_Params.ec`: abstract HAETAE parameter constants and required
  well-formedness assumptions.
- `HAETAE_Algebra.ec`: ring, module, vector, norm, high/low-bit, hint, and
  rounding interfaces.
- `HAETAE_Distributions.ec`: seed, secret, challenge, hyperball, rejection, and
  randomness distributions with losslessness/fullness/uniformity lemmas.
- `HAETAE_Scheme.ec`: mathematical key generation, signing, and verification
  modules.
- `HAETAE_ROM.ec`: random-oracle instantiation for message hashing,
  challenge generation, matrix expansion, and sampler expansion.
- `HAETAE_Reductions.ec`: game hops and reductions to the HAETAE assumptions.
- `HAETAE_Security.ec`: final theorem assembling correctness, rejection,
  forking/programming, and hardness terms.

Only introduce a file when it has a stable proof boundary. If a lemma is used by
one proof only, keep it local until it becomes shared.

## Proof Architecture

Start with abstract games before scheme details:

1. Define a signature `Scheme` module type with `kg`, `sign`, and `verify`.
2. Define a signing adversary module type with oracle access, following the
   module-parameter style in `PKE_ROM.ec` and `KEM_ROM.ec`.
3. Define the unforgeability game with a signing-query log and an explicit
   freshness predicate for `(message, context, signature)` triples.
4. Prove generic probability rewrites and oracle-counting lemmas before adding
   HAETAE-specific algebra.
5. Model HAETAE keygen/sign/verify at the mathematical level.
6. Prove correctness as a separate theorem before proving unforgeability.
7. Add game hops one at a time, with one named lemma per hop.
8. Finish with one final theorem that states the concrete bound in terms of
   named reduction adversaries and named failure probabilities.

Follow Kyber's convention of making reductions explicit modules. A reduction
should expose exactly the interface required by the target assumption, store only
the state needed to embed a challenge, and have a lemma relating its game to the
adjacent HAETAE game.

## Signature-Specific Modeling Rules

Do not model HAETAE as a KEM or PKE. Reuse proof style from Kyber, not its
security definitions.

The signature proof must account for:

- signing-query transcripts and freshness;
- random-oracle queries for message hashing and challenge generation;
- programmed or guessed challenge points, if the proof uses a forking or
  measure-and-reprogram argument;
- rejection sampling and the distribution of accepted signatures;
- norm-bound failures for secret keys, responses, and verification-side
  reconstructed vectors;
- malformed public keys or signatures if the selected security definition
  allows adversarially supplied encodings;
- mode-dependent parameters for HAETAE mode 2, mode 3, and mode 5.

Keep rejection/failure events as named boolean predicates. Avoid burying them in
large postconditions; this makes final bounds easier to assemble and compare
with the paper.

## Axiom Policy

Minimize axioms. Every axiom must be in the narrowest file that needs it, named
for the mathematical fact it represents, and accompanied by a comment explaining
whether it is:

- a cryptographic assumption;
- a parameter condition;
- an idealized random-oracle/sampler property;
- a paper lemma not yet mechanized;
- an implementation abstraction to be refined later.

Never use a new axiom to close a local EasyCrypt proof obligation that should be
proved from existing definitions. If an axiom is temporary, mark it with
`TODO_PROOF_BOUNDARY` and list the intended replacement lemma.

Before reporting a completed proof theorem, search for:

```sh
rg -n "admit|abort|axiom|TODO_PROOF_BOUNDARY" haetae-security
```

Explain every remaining result in that search output.

## EasyCrypt Style

Match Kyber's style unless there is a clear reason not to:

- Use `abstract theory` for reusable game frameworks and assumptions.
- Use `clone import ... with` for instantiating games and assumptions.
- Use `module type` interfaces for schemes, adversaries, oracles, samplers, and
  reductions.
- Use `declare module A <: ... {-S,-O}` style freshness restrictions.
- Prefer `byequiv` for game hops that are relational equalities.
- Prefer `byphoare` for one-sided probability bounds and failure events.
- Keep losslessness premises explicit and named.
- Keep query bounds as constrained constants, e.g.
  `const qH : { int | 0 <= qH } as ge0_qH`.
- Use short local modules for intermediate games rather than complicated
  boolean flags inside one game.

When using `smt()`, first expose the relevant arithmetic facts in the context.
Broad unexplained SMT calls are acceptable only for routine ring or integer
cleanup after the proof state is already clear.

## Development Order

1. Compile the Kyber reference files to confirm the local EasyCrypt setup:

   ```sh
   cd haetae-security/kyber-security
   easycrypt compile PKE_ROM.ec -I .
   easycrypt compile KEM_ROM.ec -I .
   easycrypt compile MLWE.ec -I .
   easycrypt compile MLWE_PKE_Basic.ec -I .
   ```

2. Create and compile the abstract signature game file:

   ```sh
   cd haetae-security
   easycrypt compile Sig_ROM.ec -I . -I kyber-security
   ```

3. Add HAETAE algebra and distribution interfaces, compiling each file after
   every meaningful lemma.

4. Add the mathematical HAETAE scheme and prove deterministic verification of
   honestly generated signatures, modulo named rejection and encoding failure
   events.

5. Add the unforgeability game hops and reductions incrementally. Compile the
   touched file after each hop.

6. Only then assemble the final theorem in `HAETAE_Security.ec`.

## Verification Commands

Run the narrowest compile command while editing:

```sh
easycrypt compile <file>.ec -I . -I kyber-security
```

Before claiming completion of a HAETAE security proof milestone, run all HAETAE
EasyCrypt files and the Kyber reference files used by imports:

```sh
cd haetae-security
for f in *.ec; do easycrypt compile "$f" -I . -I kyber-security; done
cd kyber-security
easycrypt compile PKE_ROM.ec -I .
easycrypt compile KEM_ROM.ec -I .
easycrypt compile MLWE.ec -I .
easycrypt compile MLWE_PKE_Basic.ec -I .
```

If a proof requires a Why3 server, use the repository's established EasyCrypt
server invocation pattern rather than changing proof statements to avoid solver
work.

## Non-Goals

- Do not alter `kyber-security/` while developing HAETAE unless the task
  explicitly asks for a shared abstraction.
- Do not replace Kyber's proof framework with a new dependency.
- Do not prove C/Jasmin implementation equivalence as part of the first
  HAETAE security proof. Keep implementation refinement separate from the
  mathematical security theorem.
- Do not hide rejection sampling, norm failures, or random-oracle programming
  failures inside unnamed assumptions.
- Do not weaken the final theorem to avoid a difficult hop without recording
  the gap.

## Completion Criteria

A milestone is complete only when:

- the claimed EasyCrypt files compile;
- all new game hops are stated as named lemmas;
- all reductions are explicit modules with clear adversary interfaces;
- all remaining axioms/admissions are accounted for;
- the final report lists compiled files, theorem names, assumptions used, and
  unresolved proof boundaries.


A “full” machine-checked HAETAE security proof means: every game hop and loss term is proved in EasyCrypt, and the final theorem has no proof-boundary premises
  except standard cryptographic assumptions stated as games, such as MLWE and Module-SIS hardness.

  Current state is conditional. Recent checked scaffolding includes concrete
  list-polynomial arithmetic modulo `q`, concrete matrix-vector evaluation for
  Module-SIS, transcript field-consistency predicates, and a forking extractor
  that computes a signature response difference and packages it into a
  fork-specific Module-SIS target equation. The algebra layer now includes
  checked HAETAE-style high/low-bit, LSB, compose, hint-highbit, and alpha-mul
  operators over concrete list polynomials; `sign_internal` uses deterministic
  nonzero commitment carriers; `challenge_hash` is mode-aware and produces a
  checked prefix-sparse structural challenge whose first `tau` coefficients are
  unit signs and whose tail is zero, but it still derives that challenge from
  lowbits/message-hash rather than the full paper transcript; and Module-SIS
  solutions are required to be well-formed `polyvecl`s rather than only
  outer-length-correct lists.
  The public-key algebra now has a named structural packed-keygen bridge:
  `haetae_keygen_raw_public_vector` defines the raw generated vector from the
  structural `A0`, `s1`, and `s2` sources. Keygen now has an explicit
  reference-shaped seed-buffer split: external entropy is expanded into
  `rhoprime`, `sigma`, and `key`, and the scheme-level `kg` routes matrix
  expansion through `haetae_keygen_rhoprime` instead of using the external seed
  directly; the internal transcript, counted-ROM, programmed-ROM, and
  budgeted sampled-signing games use the same `rhoprime` keygen boundary. The
  split now names the reference C constants
  `haetae_reference_keygen_xof_absorb_bytes = seedbytes`,
  `haetae_reference_keygen_xof_squeeze_bytes = 2*seedbytes + crhbytes`,
  the `seedbuf` offsets 0/`seedbytes`/`seedbytes+crhbytes`,
  `haetae_shake256_rate_bytes = 136`, and the SHAKE256 domain byte
  `haetae_shake256_domain_separator = 31`. `haetae_keygen_xof_seedbuf`
  is now defined through `HAETAE_FIPS202.ec`: `haetae_xof256_absorb_once`
  calls the one-block SHAKE256 absorb wrapper and `haetae_xof256_squeeze`
  calls the checked squeeze wrapper. `HAETAE_Keccak1600.ec` gives a concrete
  bit-level Keccak-f[1600] permutation with 64-bit lanes, 5x5 state indexing,
  theta/rho/pi/chi/iota rounds, rotation offsets, round constants, and
  byte/lane little-endian conversion. Round constants now use
  `keccak_word_bit` over `2^64`-normalized lane words rather than the
  byte-normalizing `keccak_byte_bit`, so generated KAT proofs exercise the
  intended 64-bit constant semantics. It also exposes checked bit-projection
  lemmas for lane xor/and/not/rotl, lane constants, state-lane lookup,
  theta-c/theta-d/theta/rho-pi/chi/iota, one full round, and byte assembly
  (`keccak_lane_to_byte_bitsE` plus the first expected empty-SHAKE byte
  constructor `keccak_lane_to_byte_70E`); generated KAT proofs should apply
  these to concrete occurrences and avoid global-repeat rewrites over
  whole-state formulas. `HAETAE_FIPS202_KAT_Empty_Generated.ec` now exercises
  that discipline on concrete empty-input generated proof slices: it proves the
  first-round lane-0 bit-0 fact from the padded state through
  theta/rho-pi/chi/iota, proves that eight generated final-round bits for
  round-24 lane 0 imply output byte 0 equals the published empty-SHAKE byte
  `70`, and proves the full reducer from final round-24 expected-bit equality
  for all 64 output bytes to `shake256_empty_64_known_answer`, with checked
  lazy sequence-projection side conditions and local proved power facts for the
  final bit arithmetic. The FIPS202 layer
  fixes the 200-byte
  Keccak state size, 136-byte SHAKE256 rate, 64-byte capacity, `0x1f`
  SHAKE domain separator, `0x80` final padding byte, and the short-message
  padded state shape used by reference keygen (`seedbytes = 32 < 136`,
  output length `2*seedbytes + crhbytes = 128 < 136`). Checked lemmas prove
  the memcpy-shaped seedbuf size, slice sizes, XOF-call length discipline,
  short-domain discipline, absorb/squeeze equivalence
  (`haetae_keygen_xof_seedbuf_shake256E`), and
  `haetae_reference_keygen_seed_flow_wf_ok` for the reference-shaped public
  key path. `HAETAE_FIPS202_CRef.ec` adds a C-shaped absorb buffer, padding,
  lane load/store bridge, permutation-call, and short-output C API model:
  absorb-once leaves the padded state unpermuted with `pos = SHAKE256_RATE`,
  while the first squeeze step performs the permutation. It proves the lane
  and C-API-shaped views equal the `HAETAE_FIPS202.ec` wrapper for the
  one-block HAETAE uses. `HAETAE_FIPS202_TestVectors.ec` records SHAKE256
  known-answer fixtures for empty input, one zero byte, and the 32-byte HAETAE
  keygen-shaped input, with checked fixture/input/output sizes and checked
  equality between the wrapper outputs and the C-API-shaped model.
  `HAETAE_FIPS202_KAT_Certificates.ec` now factors the empty-input SHAKE256
  KAT through a checked padded-state certificate, an explicit 24-round
  Keccak-f[1600] lane chain, and a checked bridge from the certificate output
  to `shake256_empty_64_actual`. It also has a checked per-byte premise bridge:
  generated facts for all 64 `nth` output bytes imply both the certificate KAT
  boolean and the public `shake256_empty_64_known_answer`. The generated KAT
  file strengthens this with
  `shake256_empty_64_known_answer_from_round24_expected_bits`, so final
  round-24 bit equalities against the expected byte bits imply the public
  empty-SHAKE KAT. The first complete actual final-round byte slice is now
  checked: `empty_round24_lane00_bit00_from_round23_bits` through
  `empty_round24_lane00_bit07_from_round23_bits` prove all eight bits of
  output byte 0 from the concrete Keccak round-24 step, each reduced to 33
  named round-23 bit facts for the three rho-pi inputs consumed by chi/iota.
  `empty_round24_output_byte00_from_expected_bits` then bridges those expected
  bit equalities to the byte-0 KAT equality. The first twenty-two byte-0
  round-23 prerequisites are now pushed one hop backward: the bit-0 group
  `empty_round23_lane00_bit00_from_round22_bits`,
  `empty_round23_lane04_bit00_from_round22_bits`,
  `empty_round23_lane09_bit00_from_round22_bits`,
  `empty_round23_lane14_bit00_from_round22_bits`,
  `empty_round23_lane19_bit00_from_round22_bits`, and
  `empty_round23_lane24_bit00_from_round22_bits`, plus the bit-63 group
  `empty_round23_lane01_bit63_from_round22_bits`,
  `empty_round23_lane06_bit63_from_round22_bits`,
  `empty_round23_lane11_bit63_from_round22_bits`,
  `empty_round23_lane16_bit63_from_round22_bits`, and
  `empty_round23_lane21_bit63_from_round22_bits`; and the bit-20 group
  `empty_round23_lane06_bit20_from_round22_bits`,
  `empty_round23_lane00_bit20_from_round22_bits`,
  `empty_round23_lane05_bit20_from_round22_bits`,
  `empty_round23_lane10_bit20_from_round22_bits`,
  `empty_round23_lane15_bit20_from_round22_bits`,
  `empty_round23_lane20_bit20_from_round22_bits`,
  `empty_round23_lane03_bit20_from_round22_bits`,
  `empty_round23_lane08_bit20_from_round22_bits`,
  `empty_round23_lane13_bit20_from_round22_bits`,
  `empty_round23_lane18_bit20_from_round22_bits`, and
  `empty_round23_lane23_bit20_from_round22_bits`, proving those round-23 facts
  from concrete round-22 Keccak steps and named round-22 bit facts. The helper
  emitter `tools/gen_empty_kat_bit_lemma.py` now generates these one-step
  EasyCrypt lemmas from the concrete empty SHAKE256 state chain. All eleven
  round-23 one-hop premises (the five bit-19 lanes and six bit-21 lanes), and
  all remaining `shake256_empty_round24` one-step bit premises
  (`empty_round24_laneXX_bitYY_from_round23_bits`), are now checked. The remaining
  KAT work is the backward round-premise discharge to the padded input for the full
  set of final-round byte premises (including bytes 1..63) and the alignment of
  these concrete lemmas with the reference C/Jasmin memory model. The generated
  first-round bit slice, all final-round expected-bit-to-KAT reducers, and the full
  64-byte final-output bridge are now checked.
  Proving the concrete Keccak reducer equals all recorded known-answer
  constants remains open. The
  reference public vector is routed through
  `haetae_reference_keygen_public_vector` and
  `packed_haetae_reference_public_key`, with checked packed-key roundtrip and
  verifier-matrix bridge lemmas. The public vector is now routed through
  reference-shaped keygen stages: modes 2/3 use
  `haetae_keygen_mode23_predecompose_vector`, checked `decompose_vk` highbits,
  named rounding lowbits, and an adjusted-error vector; mode 5 uses the
  q-normalized `-2*(A0*s1+s2)` public-key representative. The proof establishes
  q-normalization for the raw/predecompose vectors, proves the mode-specific
  packed public values are in the checked `haetae_polyveck_polyq_coeffs_wf`
  range, and routes keygen through `haetae_keygen_public_key_ref_roundtrip` and
  `concrete_keygen_public_verification_matrix_ref_correct`.
  `haetae_verification_matrix_from_unpacked` builds the verifier matrix with
  mode 2/3 first column `2*(qj - 2*b)` and remaining columns `2*A0`; and
  `honest_public_verification_matrix_eq_packed_keygen` connects
  `keygen_internal` to that packed verifier matrix. The byte-facing
  public-key boundary now has `encoded_pkey`, `haetae_pack_vk`,
  `haetae_unpack_vk_public_key`, mode-specific `POLYQ_PACKEDBYTES` chunks,
  and the reference public-key byte shape
  `HAETAE_CRYPTO_PUBLICKEYBYTES = seedbytes + K * POLYQ_PACKEDBYTES`. It also
  has a byte-exact reference public-key codec layer,
  `haetae_pack_poly_q_ref`, `haetae_unpack_poly_q_ref_at`,
  `haetae_pack_vk_ref`, and `haetae_unpack_vk_public_key_ref`, whose byte
  formulas match the reference `pack_poly_q` layout for mode 2/3 15-bit chunks
  and mode 5 16-bit little-endian chunks. It proves decoder well-formedness
  lemmas plus checked seed-prefix, per-poly q-pack, vector-body, and public-key
  pack/unpack size facts, and proves the exact coefficient, vector-body, and
  public-key roundtrip for mode 2/3 15-bit chunks and mode 5 16-bit chunks
  under `haetae_polyveck_polyq_coeffs_wf`.
  The structural public-key bridge keeps concrete
  `concrete_keygen_public_verification_matrix_correct` and reference-byte
  `concrete_keygen_public_verification_matrix_ref_correct` bridges under the
  checked `size sd = seedbytes` keygen domain restriction instead of an opaque
  `haetae_keygen_public_key_roundtrip_ok` premise. This is still not a full
  public-key proof: the reference byte inverse, keygen-side mode 2/3
  `decompose_vk` range, mode 5 q-range, and mode-shaped verifier-column
  arithmetic, and keygen seed-buffer/XOF call trace are checked against the
  `HAETAE_FIPS202.ec` SHAKE256 absorb/squeeze wrapper and concrete
  `HAETAE_Keccak1600.ec` permutation, with checked pure EasyCrypt
  C-shaped and short-output C-API-shaped FIPS202 absorb/squeeze models. Actual
  reference-C/Jasmin memory equivalence for the FIPS202 implementation, SHAKE
  known-answer equality, NTT placement, rejection-loop sampling, and final
  keygen correspondence remain structural rather than equal to the reference
  implementation.
  Honest signatures now carry deterministic nonzero unit-coefficient response,
  auxiliary-response, and hint vectors with checked well-formedness and
  structural norm bounds; the previous all-zero signature-token shortcut has
  been removed. The random-oracle output distribution is no longer globally `dunit`:
  message-hash, challenge, matrix, and sampler queries have separate structural
  distributions, and `valid_signature` checks concrete signature field sizes and
  challenge shape. `verify_internal` is no longer an existential signer witness:
  it checks signature field well-formedness, message-hash/challenge
  recomputation from the public key, message, context, commitment fields, an
  explicit public-key/challenge/response reconstruction equation for the
  commitment highbits, and the verified signature norm bound. Valid transcripts
  expose this reconstruction equation through checked lemmas at the fork
  boundary. FS-with-aborts and rejection loss terms are
  concrete nonnegative expressions over query/min-entropy factors instead of
  lemmas that rewrite them to zero. The ROM min-entropy failure predicate is no
  longer uninterpreted; it is a mode-indexed prefix-sparse challenge-support
  predicate with checked no-failure lemmas for honest transcripts and for
  transcripts satisfying the simulated-signing record relation. The signing
  simulation boundary now has a checked transcript-record discipline:
  `signing_transcript_record`s project to query logs and transcript logs,
  `signing_record_relation` packages simulated-signing and transcript-validity
  evidence, and `EUF_CMA_TranscriptSimulatedSign` records query, transcript,
  and combined record logs at the signing-oracle boundary. Adding those logs has
  a checked zero-loss erasure hop (`transcript_logging_erasure_exact`), and
  consistent transcript logs imply checked list-level validity and
  no-min-entropy-failure invariants (`transcript_log_consistent_valid`,
  `transcript_log_consistent_no_min_entropy`) plus the combined
  `transcript_log_ready` predicate. Deterministic
  `sign_internal` outputs now have checked attempt, simulation, transcript, and
  record relation lemmas. The concrete internal transcript-signing game
  `EUF_CMA_InternalTranscriptSign` samples signing coins, builds real HAETAE
  transcript records from signature fields, and logs queries, transcripts, and
  combined records. Its signing oracle has a checked Hoare invariant
  (`internal_transcript_sign_oracle_preserves_state`); arbitrary adversaries
  preserve that invariant through the standard `SIG.Adversary` oracle interface
  (`adversary_internal_transcript_state_preserved`); and the full internal game
  has checked final state, transcript-validity, no-min-entropy, and combined
  log-ready theorems (`internal_transcript_sign_main_state_sound`,
  `internal_transcript_sign_main_transcripts_valid`,
  `internal_transcript_sign_main_no_min_entropy`,
  `internal_transcript_sign_main_log_ready`). The adversary boundary now
  also has a ROM-faithful internal transcript game
  (`EUF_CMA_ROMInternalTranscriptSign`) whose signing oracle performs the same
  sampler, message-hash, and challenge random-oracle calls as `HAETAE.sign`
  before logging the concrete transcript record. This game has checked state
  preservation, final state, transcript-validity, no-min-entropy, and log-ready
  lemmas
  (`rom_internal_transcript_sign_oracle_preserves_state`,
  `adversary_rom_internal_transcript_state_preserved`,
  `rom_internal_transcript_sign_main_state_sound`,
  `rom_internal_transcript_sign_main_transcripts_valid`,
  `rom_internal_transcript_sign_main_no_min_entropy`,
  `rom_internal_transcript_sign_main_log_ready`) and an exact zero-loss erasure
  theorem from the real HAETAE EUF-CMA game
  (`haetae_rom_internal_transcript_erasure_exact`). This removes the immediate
  adversary-boundary risk for transcript logging: the proof no longer needs to
  relate the real signing oracle directly to the shortcut internal sampler
  before exposing transcript logs. The top-level security assembly also has a
  checked ROM-transcript entry point
  (`euf_cma_security_from_rom_internal_transcript_hop`) whose remaining premise
  is exactly the bound from this ROM-faithful transcript game to UF-NMA plus the
  FS-with-aborts terms. The transcript-log boundary is now ready as a qualitative
  invariant and now exposes member-level bridge lemmas from a ready transcript
  log to FS-with-aborts no-failure at matching programming sites, including the
  actual signature-field programming site
  (`transcript_log_ready_no_failure_for_matching_site`,
  `transcript_log_ready_no_failure_for_programming_site`,
  `transcript_log_ready_no_failure_for_signature_programming_site`). The
  ROM-programming layer now also names the actual signature challenge output and
  actual signature programming site
  (`transcript_signature_challenge_output`,
  `actual_signature_programming_site`) and proves that the concrete signature
  output matches the transcript's signature challenge. The ready transcript log
  therefore implies the list-level clear-site predicate
  (`transcript_log_ready_signature_sites_clear`). The
  ROM-faithful transcript game consumes that bridge in a checked Hoare
  postcondition for every logged transcript's signature programming site
  (`rom_internal_transcript_sign_main_no_failure_for_signature_site`) and in a
  checked list-level clear-site postcondition
  (`rom_internal_transcript_sign_main_signature_sites_clear`). The same clear-
  site invariant is now consumed in a checked success split: the bad-forgery
  branch where a successful ROM-internal transcript forgery violates the
  signature-programming-site predicate is proved zero
  (`rom_internal_transcript_bad_forgery_zero`) and then bounded by the current
  FS-with-aborts terms (`rom_internal_transcript_bad_forgery_bound`). A parallel
  counted-ROM surface is now present: `HAETAE_Reductions.ec` defines
  hash/signature query budgets, a structural challenge-support lower bound
  (`challenge_support_bits_lower_bound = 58`,
  `challenge_support_cardinality_lower_bound = 288230376151711744`),
  collision/prequery/min-entropy loss components,
  `counted_rom_programming_loss_term`, and `haetae_euf_counted_rom_bound`. The
  counted term is now checked to be the subunit concrete value `37 / 2^58`
  through `counted_rom_programming_loss_term_checked_subunit` and is linked to
  the query-budget numerator through
  `counted_rom_loss_from_query_budgets_and_support`. The prequery/reprogramming
  branch is now separated as `counted_rom_prequery_reprogramming_term`, checked
  to be the concrete value `31 / 2^58`, linked to the numerator
  `(qH + qS + 1)^2 + qS * (qH + 1)` through
  `counted_rom_prequery_reprogramming_from_query_budgets_and_support`, and split
  from the total counted loss by `counted_rom_programming_loss_splitE`.
  `HAETAE_ROM_Programming.ec` defines counted ROM events, prequery and
  reprogramming conflict predicates, a
  `CountedLazyROM` wrapper that records hash queries, programmed sites,
  signature sites, and explicit bad flags, plus the adversary-facing
  `CountedROMInterface`, `CountedROMClient`, and `CountedLazyROMBadGame`
  boundary. Because `CountedROMClient` has direct access to `program`, a
  nontrivial aggregate bad-flag bound is not true for every inhabitant of that
  module type. The file still makes this explicit for the aggregate
  `CountedLazyROMBadGame` result with `counted_lazy_rom_bad_flags_budget_sound`,
  but the prequery/reprogramming branch is no longer hidden behind a generic
  global probability wrapper. For that branch, the checked path now goes through
  the concrete budgeted sampled-signing game and the direct signing-coin sampler
  interface. The counted lazy-ROM layer also has checked clear-state facts:
  initialization clears all bad flags and query/programming logs, ordinary
  lazy-ROM reads preserve clear flags, transcript observation preserves clear
  flags when transcript min-entropy holds, and the `bad` accessor returns false
  under the clear-state invariant. `HAETAE_HopGames.ec` now proves that the
  current counted internal-transcript simulated-signing game satisfies that
  discipline. The `EUF_CMA_ROMInternalTranscriptCountedSign` signing oracle
  tracks prior lazy-ROM outputs through `CountedLazyROM.queries`, logs concrete
  HAETAE transcript records, proves transcript min-entropy from `sign_internal`'s
  checked transcript relation, and preserves an empty `programmed_sites` list
  because this current game performs no ROM programming. The adversary-boundary
  invariant `adversary_counted_rom_internal_transcript_budget_state_preserved`
  lifts those facts through arbitrary `SIG.Adversary` oracle calls, and the
  game-level theorems `counted_rom_internal_transcript_counted_bad_zero`,
  `counted_rom_internal_transcript_budget_sound`, and
  `counted_rom_internal_transcript_counted_bad_subunit` discharge the bad-flag
  discipline for this concrete game. The ROM programming layer now also exposes
  an actual programmed-signing counted game,
  `EUF_CMA_ROMProgrammedTranscriptCountedSign`: its signing oracle performs the
  sampler and message-hash ROM reads, constructs the real HAETAE transcript
  from the signature fields, observes that transcript, and programs the
  transcript's actual signature challenge site instead of reading the challenge
  hash. The state interface has explicit freshness predicates
  (`programming_site_fresh`, `programming_transcript_fresh`) and checked
  preservation lemmas showing that `CountedLazyROM.program` keeps all bad flags
  clear under freshness and that `CountedLazyROM.bad` preserves the
  min-entropy-clear invariant. For the programmed game, the min-entropy branch
  is now machine-checked through arbitrary adversary oracle calls:
  `programmed_counted_sign_oracle_preserves_min_entropy_clear`,
  `adversary_programmed_counted_min_entropy_preserved`,
  `programmed_counted_main_min_entropy_clear`,
  `programmed_counted_min_entropy_bad_zero`, and
  `programmed_counted_min_entropy_bad_bound`. The unbudgeted programmed counted
  game keeps only a concrete budget-expression bridge,
  `programmed_counted_prequery_reprogramming_bad_bound_from_budget_expr`, for
  clients that have already proved a game-level prequery/reprogramming
  probability bound. The adversary-facing
  query-budget discipline for programmed signing is now also a checked game
  boundary. `HAETAE_Reductions.ec` exposes integer budget constants
  `hash_query_budget_count` and `signature_query_budget_count`, tied to the
  real-valued ROM budgets by checked equalities. `HAETAE_HopGames.ec` defines
  `EUF_CMA_ROMProgrammedTranscriptBudgetedCountedSign`, whose adversary hash
  oracle and signing oracle enforce those budgets before forwarding to
  `CountedLazyROM`; over-budget calls return structural fallback values. The
  checked Hoare lemmas
  `budgeted_programmed_hash_get_preserves_query_budget`,
  `budgeted_programmed_sign_oracle_preserves_query_budget`,
  `adversary_budgeted_programmed_query_budget_preserved`, and
  `budgeted_programmed_main_query_budget_preserved` prove that arbitrary
  `SIG.Adversary` calls preserve the concrete query-budget invariant at this
  boundary. The same budgeted game now carries a reprogram-discipline invariant
  combining the public-key/secret-key relation, conflict-free honest programmed
  sites, and a clear `bad_reprogram` flag:
  `budgeted_programmed_hash_get_preserves_discipline`,
  `budgeted_programmed_sign_oracle_preserves_discipline`,
  `adversary_budgeted_programmed_discipline_preserved`,
  `budgeted_programmed_main_reprogram_clear`, and
  `budgeted_programmed_bad_reprogram_zero`. Thus the programmed-game
  reprogramming branch is checked zero at the adversary boundary, not left as a
  budget premise. The bridge
  `budgeted_programmed_query_budget_certifies_branch_bound` connects any
  game-level probability bound with the checked support/cardinality expression
  for `counted_rom_prequery_reprogramming_term`; the sharper
  `budgeted_programmed_query_budget_certifies_branch_bound_from_prequery`
  reduces that branch to the prequery event alone, using the checked zero
  reprogram probability. The ROM-programming layer now uses an entropy-bearing
  signing source: `HAETAE_Distributions.ec` samples a 58-bit
  `signing_entropy_token`, maps it to a length-checked signing-coin carrier
  (`signing_entropy_token_to_coins_size`), and proves a point-mass bound
  (`signing_entropy_token_distribution_point_bound`). `HAETAE_Algebra.ec`
  places signing coins before the fixed secret/context/message source and
  exposes the token in `commitment_lowbits` through
  `commitment_lowbits_entropy_token`, so the programmed challenge-site query has
  a checked token projection. `HAETAE_ROM_Programming.ec` now proves
  `honest_signing_programming_site_query_entropy_token`,
  `honest_signing_programming_site_query_token_injective`, and the concrete
  spread theorem `honest_signing_programming_site_query_spread`, then lifts it
  to prior-query lists by
  `honest_signing_programming_site_query_spread_bound`,
  `honest_signing_programming_site_query_spread_bound_for`,
  `programmed_site_prequery_one_step_fset_bound`,
  `programmed_site_prequery_one_step_budget_bound`, and
  `programmed_site_prequery_one_step_concrete_bound`. It also defines the
  challenge-query projection `ro_query_is_challenge` and proves
  `programming_site_prequeried_honest_challenge_filter`,
  `programmed_site_prequery_one_step_challenge_fset_bound`,
  `programmed_site_prequery_one_step_challenge_budget_bound`, and
  `programmed_site_prequery_one_step_challenge_concrete_bound`, so sampler,
  message-hash, and matrix-expansion ROM traffic do not inflate the support
  count for honest challenge-site prequery. It also records that
  `programming_site_prequeried` ignores the programmed output
  (`programming_site_prequeried_output_irrelevant`), so challenge-output support
  alone cannot bound prequery of the ROM input. Honest HAETAE signing sites are
  no longer tied to a single hard-coded coin distribution at this lift boundary:
  `programmed_site_query_min_entropy_bound_for` and the `_for` one-step
  prequery lemmas route the same fset, challenge-filtered, budgeted, and
  counter-based bounds through any signing-coin distribution that satisfies
  `signing_randomness_token_spread`. The concrete `drandom_coins` sampler is
  still proved as the current entropy-bearing instance by
  `signing_coin_distribution_token_spread` and `signing_coin_distribution_ok`.
  Honest HAETAE signing sites are
  functional for reprogramming (`honest_signing_programming_sites_no_conflict`);
  the generic conflict-free log lemmas
  `programming_site_conflict_free_no_reprograms`,
  `programmed_site_reprogram_one_step_conflict_free_zero`, and
  `programmed_site_prequery_reprogram_one_step_concrete_bound` lift the
  one-step estimate to a prequery-or-reprogram event when the prior programmed
  log is conflict-free. The adaptive prequery lift is now checked for the direct
  signing-coin sampler: `HAETAE_ROM_Programming.ec` exposes
  `SigningCoinSampler` and `DirectSigningCoinSampler`, proves the direct sampler
  message-hash prequery bounds, and `HAETAE_HopGames.ec` instantiates the
  budgeted sampled programmed-signing game with that sampler. The checked
  theorem `budgeted_sampled_direct_prequery_reprogram_bad_checked_31` derives
  the concrete `31 / 2^58` bound from query budgets, challenge-query support,
  lazy-ROM freshness, and the entropy-bearing signing-site spread theorem,
  without a premise-based global probability wrapper. The ROM transcript
  bad-forgery branch is bounded by the subunit counted term
  (`rom_internal_transcript_bad_forgery_counted_bound`). The top-level ROM hop
  now has checked bridges from a clear-site reduction premise to both the
  ordinary ROM-transcript success bound
  (`rom_internal_transcript_hop_from_clear_site_reduction`) and the counted-ROM
  success bound
  (`rom_internal_transcript_hop_from_clear_site_counted_reduction`). The
  top-level ROM entry point also has versions that consume the checked
  bimodal-to-Module-SIS adapter directly
  (`euf_cma_security_from_rom_transcript_and_mechanized_bimodal`,
  `euf_cma_security_from_rom_clear_site_and_mechanized_bimodal`,
  `euf_cma_security_from_rom_transcript_and_counted_bimodal`,
  `euf_cma_security_from_rom_clear_site_and_counted_bimodal`), so the ROM path no
  longer needs a separate abstract bimodal-to-Module-SIS probability premise when
  using `BimodalMSIS_As_ModuleSIS`. The ROM-faithful transcript game now also
  has a constructed NMA adversary bridge: `ROMInternalTranscriptAsNMA` replays
  the same adversary with a signing oracle that uses the same sampler,
  message-hash, challenge-hash, transcript, and record logging discipline, and
  `rom_internal_transcript_clear_site_structural_nma_bound` proves the clear-site
  success branch is bounded by that constructed UF-NMA game. The top-level
  theorem `euf_cma_security_from_structural_nma_and_counted_bimodal` consumes
  this checked clear-site bridge plus the mechanized bimodal-to-Module-SIS
  adapter and the counted ROM loss, so it no longer needs an arbitrary
  clear-site-to-NMA premise. The NMA boundary now has a stricter public-simulator
  surface as well: `ROMInternalTranscriptPublicSimAsNMA` signs using a public-key
  simulator constructor (`public_sim_signature`) rather than a stored signing
  secret, `rom_internal_nma_public_sim_exact` proves exact equivalence to the
  older structural NMA bridge for keys generated by the current model, and the
  top-level theorem
	  `euf_cma_security_from_public_sim_nma_and_counted_bimodal` consumes a
	  UF-NMA bound for this public simulator. This is still structural rather than
	  paper-faithful: the equivalence to the older bridge relies on the current
	  keygen representation where the public seed determines all signing carriers.
	  The next sampler boundary is now explicit: `PaperSimSigningSampler` exposes
	  an initialization/sample interface for sampled simulated signatures,
	  `ROMInternalTranscriptPaperSimAsNMA` signs from that sampler while preserving
	  the same message-hash, challenge-hash, transcript, and record logging shape,
	  `paper_sim_signature_valid` checks validity for well-formed paper-simulator
	  samples, and `public_sim_to_paper_sim_nma_hop_from_sampling_hop` names the
	  exact statistical hop from the public deterministic simulator to this sampled
	  simulator. A concrete ROM-backed structural instance is also checked:
	  `ROMPaperSimSigningSampler` derives signing coins through the sampler ROM
	  output, `paper_sim_sample_from_public_coins` projects them into the sampled
	  simulator fields, and `rom_internal_nma_public_sim_rom_paper_sim_exact`
	  proves exact equality with the current public simulator. The bridge now also
	  has a real-`sign_internal` projection: `paper_sim_sample_from_real_signing_coins`
		  extracts the response, auxiliary response, hint, lowbits carrier, and entropy
		  from the current signing equation; `RealSigningPaperSimSampler` samples through
		  the sampler ROM and returns that projection; and
			  `rom_internal_nma_real_signing_paper_sim_exact` proves exact equality between
			  `ROMInternalTranscriptAsNMA` and the sampled-simulator NMA game instantiated
			  with this real-signing sampler. The rejection/abort replacement point is now
			  named explicitly too: `signing_attempt_state` records the sampled coins,
			  a `signing_attempt_sample` triple separating sampled `y1`, sampled `y2`,
			  and the commitment carrier, then highbits, lowbits, challenge, response,
			  auxiliary response, hint, and produced signature; separate predicates name
			  response-norm, hint-norm, and rejection-sampling aborts. The attempt
		  boundary also now has checked field-discipline predicates:
		  `signing_attempt_state_programmed_lowbits`,
		  `signing_attempt_state_challenge_consistent`,
		  `signing_attempt_state_public_equation_consistent`,
		  `signing_attempt_state_fields_match_signature`,
		  `signing_attempt_state_field_accepts`, and
		  `signing_attempt_state_verification_accepts`. The checked rejection gate is
		  now tied both to verifier discipline and named reference-signing rejection
		  checks: `signing_attempt_state_rejection_accepts` requires the `pk`, message,
		  and context-specific verification predicate plus
		  `signing_attempt_state_reference_rejection_accepts`. That reference gate names
		  the C signing loop's current proof surface via `signing_attempt_reject1_bound`,
		  `signing_attempt_reject2_bound`, `signing_attempt_state_reject1_accepts`,
		  `signing_attempt_state_reject2_accepts`, and
		  `signing_attempt_state_pack_accepts`; `signing_attempt_state_rejection_aborts`
		  and `signing_attempt_state_reference_rejection_aborts` name the corresponding
		  complements rather than a context-free local accept flag. The reject2 branch
		  is no longer a hardcoded false predicate: it is factored through
		  `signature_rejection_branch_byte`,
		  `signing_attempt_state_reject2_branch_bit`,
		  `polyvecl_double`,
		  `signing_attempt_state_reject2_sampled_y1`,
		  `signing_attempt_state_reject2_sampled_y2`,
			  `signing_attempt_state_reject2_balance_response`,
			  `signing_attempt_state_reject2_balance_aux`,
			  `signing_attempt_state_balance_norm_sq`,
			  `signing_attempt_reject2_balance_norm_sq`,
			  `signing_attempt_reject2_concrete_aborts`,
			  `signing_attempt_state_reject2_under_bound`, and
			  `signing_attempt_state_reject2_aborts`, matching the C guard shape
			  "branch bit set and `2z-y` norm below `B0^2*LN^2`". The current
			  structural signer now carries explicit coin-derived deterministic samples
			  through `signing_sample_y1` and `signing_sample_y2`, and proves their
			  reject2 projection through
			  `signing_attempt_state_of_coins_reject2_sampled_y1E`,
			  `signing_attempt_state_of_coins_reject2_sampled_y2E`, and
			  `signing_attempt_state_of_coins_reject2_balance_norm_sqE`. It still keeps
			  the branch byte already accepted, proved by
			  `signing_attempt_state_of_coins_reject2_branch_clear_current`; those are
				  now the precise replacement points for replacing the deterministic
				  structural samples with the real hyperball `y1/y2` sampler and branch-byte
				  calculation. The sample source is now separated as an explicit
				  bounded distribution boundary: `signing_sample_pair`,
				  `signing_sample_pair_sample_ok`,
				  `signing_sample_pair_distribution_ok`, and
				  `dstructural_signing_sample_pair` give the checked current structural
				  instance, while `dsigning_unit_coeff`,
				  `dsigning_unit_poly`, `dsigning_unit_polyvecl`,
				  `dsigning_unit_polyveck`, and
				  `dbounded_unit_signing_sample_pair` keep the checked non-deterministic
				  bounded-unit regression source. The sampler contract now talks about
				  well-formedness plus `signing_sample_pair_bounded`, so it is no longer
				  tied to unit coefficients. `dchecked_hyperball_signing_sample_pair`
				  gives a paper-shaped bounded carrier with checked coefficient bounds,
				  and `checked_hyperball_signing_sample_pair_distribution_ok` proves the
				  generic distribution contract for it. This is still a bounded product
				  carrier, not the exact HAETAE hyperball/sphere sampler or rejection-loop
				  distribution. `dsigning_attempt_state_from_sample_pair_sampler` is the
				  generic attempt-state sampler. Its structural instantiation is checked by
				  `dstructural_signing_attempt_state_from_samplerE`, the direct
				  attempt distribution is connected by
				  `dstructural_signing_attempt_stateE`, the bounded-unit
				  instantiation is exposed through
				  `dbounded_unit_signing_attempt_state_lossless` plus
				  `dbounded_unit_signing_attempt_state_sample_ok`, and the checked
				  hyperball-shaped carrier is exposed through
				  `dchecked_hyperball_signing_attempt_state_lossless` plus
				  `dchecked_hyperball_signing_attempt_state_sample_ok`. The current
				  constructor proves the field facts for `signing_attempt_state_of_coins`;
			  `dsigning_attempt_state` gives the current structural attempt distribution
		  with checked losslessness, token-spread, reference-zero-abort, and
		  rejection-zero-abort facts
		  (`signing_attempt_state_distribution_lossless`,
		  `signing_attempt_state_distribution_token_spread`,
		  `signing_attempt_state_distribution_reference_rejection_abort_zero_current`,
		  and
		  `signing_attempt_state_distribution_rejection_abort_zero_current`); and the
		  paper-simulation bridge proves that an accepted checked rejection attempt
		  reconstructs the same signature fields through
		  `paper_sim_signature_rejection_attempt_matches_state` and
		  `haetae_rejection_sample_from_attempt_signatureE`.
		  `HAETAERejectionPaperSimSampler` samples a signing attempt through the
		  sampler ROM and applies `haetae_rejection_sample_from_attempt` with the
		  current public key, message, and context, whose rejected branch now returns
		  `paper_sim_abort_fallback_sample`; and
		  `rom_internal_nma_real_signing_haetae_rejection_paper_sim_exact` proves the
		  current-model exact bridge from the real-`sign_internal` sampler to this
		  named rejection sampler while carrying the public-key/secret-key invariant
		  needed by the checked gate. The top-level theorem
		  `euf_cma_security_from_paper_sim_nma_and_counted_bimodal` routes the counted
		  ROM security theorem through that bridge, keeping
		  `rejection_sampling_loss_term` in the NMA premise rather than dropping it;
		  `euf_cma_security_from_rom_paper_sim_nma_and_counted_bimodal` routes the same
		  counted theorem through the checked ROM-backed structural sampler without a
		  sampler-distance premise, and
		  `euf_cma_security_from_real_signing_paper_sim_nma_and_counted_bimodal` routes
		  it through the checked real-`sign_internal` sampled boundary;
		  `euf_cma_security_from_haetae_rejection_paper_sim_nma_and_counted_bimodal`
		  routes it through the named current-model rejection-sampler boundary.
	  The remaining FS/rejection work is no longer to prove the counted bad-flag
	  discipline for the current internal-transcript game; that has been
	  machine-checked. The paper-faithful programmed-signing hop now exists, its
  min-entropy branch is checked, and its direct-sampler prequery/reprogramming
  branch is bounded by the checked `31 / 2^58` theorem above. The counted loss
  is no longer a placeholder at least one; it is subunit and derived from the
  current query budgets and challenge-support denominator.
  The
  bimodal-to-Module-SIS layer now has
  a solver-level
  lift game (`BimodalToModuleSIS_Lift_Game`) and a checked exact preservation
  theorem (`bimodal_solver_lift_exact`) showing that a successful bimodal solver
  yields a Module-SIS-valid witness for the lifted instance. It also exposes the
  lifted bimodal distribution (`dmodule_sis_from_bimodal`), proves its current
  identity/losslessness facts (`dmodule_sis_from_bimodalE`,
  `dmodule_sis_from_bimodal_lossless`), and adds mode-aware adversary-boundary
  games for both the concrete Module-SIS sampler (`ModuleSIS_ModeRelation_Game`)
  and the bimodal-sourced Module-SIS view
  (`ModuleSIS_LiftedDistribution_Relation_Game`). The exact adapter theorem
  (`bimodal_mode_solver_lifted_distribution_exact`) deliberately proves only the
  bimodal-sourced view, not the final concrete Module-SIS sampler. The remaining
  Module-SIS risk is distributional: prove that the lifted bimodal instance
  distribution is covered by the concrete Module-SIS hardness game, not merely
  that witness validity is preserved. The fork transcript boundary now also has
  checked same-site and reconstruction facts: valid fork pairs share the same
  challenge random-oracle query (`valid_forking_pair_challenge_query`), share the
  same commitment highbits (`valid_forking_pair_commitment_highbits`), and induce
  equal verification-side reconstructed highbits
  (`valid_forking_pair_reconstructed_highbits_equal`). The transcript layer now
  also names the signature-field public-key challenge term
  (`transcript_public_key_challenge_term`) and uses one uniform
  response-aux/public-key challenge relation
  (`fork_public_challenge_relation`) instead of splitting active and inactive
  reconstruction branches. Checked lemmas reduce verification reconstruction to
  response-aux plus the public-key/challenge term (`transcript_reconstructionE`)
  and lift shared reconstructed-highbits equality to the fork public
  reconstruction obligation (`valid_forking_pair_public_reconstruction_cases`).
  The same transcript
  layer now projects challenge queries and challenge outputs through actual
  signature fields (`transcript_signature_challenge_query`,
  `transcript_signature_challenge_matches`), proves equality with transcript
  fields for valid transcripts, and proves that valid fork pairs have both the
  same signature-field challenge-query site
  (`valid_forking_pair_signature_challenge_query`) and distinct signature-field
  challenges (`valid_forking_pair_distinct_signature_challenges`). The ROM programming layer
  consumes this as a checked same-programming-site query lemma
  (`valid_forking_pair_programming_site_query`) plus fork-pair self-programming
  no-reprogramming facts, and it now exposes signature-field programming sites
  (`signature_programming_site_of_transcript`) with checked query equality,
  matching, no-reprogramming, and fork same-site facts. The special-soundness
  interface now carries the checked public-reconstruction obligation
  (`fork_public_reconstruction_obligation`) alongside the exact
  bimodal-extractor to Module-SIS-extractor adapter
  (`bimodal_special_soundness_lift_exact`), and exposes a combined downstream
  obligation that returns both public-reconstruction case evidence and Module-SIS
  extraction success (`special_soundness_with_public_reconstruction_obligation`).
  The remaining forking risk is the paper-faithful algebraic extraction
  argument, not active-only transcript or extractor interface plumbing.

  The remaining high-risk boundary is now downstream of that exact game: consume
  the ROM-faithful transcript log in the simulated-signing, FS-with-aborts,
  forking, bimodal-MSIS, and Module-SIS distribution hops. The new clear-site
  bridge and counted-ROM entry point remove one unresolved game-hop shape and
  provide the right event vocabulary. The counted term itself is now subunit,
  and the current counted internal-transcript game proves its CountedLazyROM
  bad-flag probability is zero by preserving prior-query freshness,
  no-reprogramming, and no-min-entropy-failure invariants. The public-simulator
  NMA theorem narrows the old arbitrary-NMA boundary further than the
  secret-reconstructing bridge: its signing oracle is stated over the public key
	  and an explicit simulated signature constructor. The remaining shortcut is
	  model-level, not oracle-state-level: the current structural keygen makes the
	  public seed determine the simulated signing carriers. A sampled simulator
	  interface, NMA game, ROM-backed structural sampler instance,
	  real-`sign_internal` sampled boundary, and named rejection-sampler boundary
	  are now present. The exact bridges
	  `rom_internal_nma_public_sim_rom_paper_sim_exact` and
		  `rom_internal_nma_real_signing_paper_sim_exact`, plus the current-model
		  `rom_internal_nma_real_signing_haetae_rejection_paper_sim_exact`, are useful
		  plumbing, and the new attempt-field bridge proves accepted attempts
		  reconstruct real signature fields through the paper-simulator projection,
			  but they are not the paper's abort/rejection distribution. The next proof
			  obligation remains distributional: replace the current structural
			  attempt-field constructor, deterministic structural `signing_sample_y1/y2`,
			  branch byte, and current
			  zero-abort reference rejection gate
		  (`signing_attempt_state_reference_rejection_accepts`,
		  `signing_attempt_state_reject1_accepts`,
		  `signing_attempt_state_reject2_accepts`, and
		  `signing_attempt_state_pack_accepts`) with concrete HAETAE hyperball,
		  `2z-y` branch-bit, hint, and packing definitions, then replace the current
		  structural
		  `dsigning_attempt_state` lemmas by the paper's nonzero abort-loss and
		  sampler-distance theorems and prove the
	  public-simulator-to-paper-sampler hop bound from the sampler distance,
	  lazy-ROM freshness, and challenge-site min-entropy facts. Then feed that
	  sampled game into the existing ROM-programming and forking machinery. The arbitrary
	  program-capable `CountedROMClient` interface still correctly keeps
	  `counted_lazy_rom_bad_flags_budget_sound` as an explicit discipline premise,
  because such a client can force bad by direct programming. The transcript
  bad-forgery event remains structurally clear in the current internal transcript
  game; the remaining quantitative work is to move from this no-programming
	  counted game to a paper-faithful sampled simulated-signing lazy-ROM game and
	  prove the prequery/collision/freshness/min-entropy bounds for actual
	  programmed challenge sites. The
  remaining work is to consume the checked public-reconstruction bridge and
  replace the still-tautological fork-derived MSIS target, structural signing,
  rejection-sampling, ROM-programming, and bimodal-MSIS definitions with
  paper-faithful definitions and to replace the placeholder query/min-entropy
  constants by adversary-counted bounds.
  To make the proof full, remove those abstract premises one by one.

  Roadmap

  1. Freeze the exact final theorem
     State the target as:

     Pr[EUF_CMA_HAETAE(A).main() : res] <=
       Adv_MLWE(Bmlwe) +
       Adv_ModuleSIS(Bsis) +
       concrete_rejection_loss +
       concrete_rom_programming_loss +
       concrete_forking_loss

     The theorem may assume MLWE/Module-SIS hardness games, but it should not
     assume fs_with_aborts_interfaces_ready, forking_extraction_obligation,
     fork_public_reconstruction_obligation, or bimodal_to_module_sis_lift_obligation.
  2. Replace remaining abstract HAETAE algebra
     `HAETAE_Algebra.ec` now has concrete list-polynomial arithmetic modulo
     `X^n + 1` and `q`, vector subtraction, Module-SIS matrix-vector evaluation
     support, highbits/lowbits/decomposition, LSB, hint-highbits, and
     vector-derived signature norm predicates over deterministic nonzero
     unit-vector response carriers. The remaining algebraic
     replacements are:
      - exact sparse challenge polynomial distribution and support counting
      - paper-faithful HAETAE norm predicates over rounded/fixed-point carriers
      - paper-faithful commitment and response equations
      - full verification reconstruction against the HAETAE public-key/module
        equation; the current checked reconstruction is active and mode-shaped,
        and the local packed-keygen verifier matrix is connected to
        `keygen_internal` through the reference-shaped byte public-key
        interface `seed || K * POLYQ_PACKEDBYTES`. The exact reference byte
        codec is now modeled for `pack_vk`/`unpack_vk` and `pack_poly_q`/
        `unpack_poly_q`, with checked mode 2/3 15-bit and mode 5 16-bit
        pack/unpack roundtrips under the codec well-formedness predicates. The
        keygen seed-buffer split, FIPS202 SHAKE256 absorb/squeeze call trace,
        concrete bit-level Keccak-f[1600] permutation, pure EasyCrypt
        C-shaped and short-output C-API-shaped FIPS202 absorb/squeeze
        equivalence, SHAKE known-answer fixtures with checked sizes and
        checked wrapper/C-API output equality, plus an empty-input KAT
        certificate bridge from padded state through the 24 Keccak rounds to
        `shake256_empty_64_actual`, a checked per-byte bridge from generated
        empty-certificate output facts to `shake256_empty_64_known_answer`, and
        generated-style checked proofs of the empty-input first-round lane-0
        bit-0 projection, a final round-24 bit-to-byte-0 bridge, a complete
        actual final round-24 lane-0 byte-0 equality slice from eight
        33-premise bit lemmas and an expected-bit bridge, and the full
        final-round expected-bit-to-KAT reducer under
        64-bit round-constant semantics,
        keygen-side mode 2/3 `decompose_vk` public
        range, mode 5 public q-range, adjusted-error stage, reference-shaped
        packed public key, and reference-byte verification matrix bridge are
        checked. Actual C/Jasmin FIPS202 memory equivalence, full generated
        SHAKE known-answer byte equality, NTT placement, rejection-loop
        sampling, and final verifier matrix correspondence are still structural
        rather than proved equal to the reference implementation.
  3. Model real HAETAE signing exactly
     The current signing module now routes sampler random-oracle output back
     into the signing coins, but the rest is still a structural model. Define
     signing as the real rejection loop:
      - sample signing randomness
      - compute commitment
      - hash transcript into challenge
      - compute response
      - check rejection predicates
      - output real signature fields

     Then prove losslessness or bounded failure for the loop.
  4. Prove rejection-sampling indistinguishability
     Replace the current rejection premise with a theorem of the form:

     real_signing_distribution
     <= simulated_signing_distribution + rejection_sampling_loss

     This is usually the hardest statistical part. It needs concrete distribution lemmas for HAETAE’s hyperball / Gaussian-like / bounded samplers.
  5. Mechanize FS-with-aborts / ROM programming
     `HAETAE_ROM.ec` now uses query-specific structural output distributions.
     The ROM programming bound must still be proved against the actual lazy random oracle:
      - define programmed challenge points
      - prove no-reprogramming except collision/bad event
      - prove min-entropy of the programmed challenge site
      - count adversary hash/sign queries
      - derive paper-faithful qH, qS, challenge-space, and abort-loss terms

     Current FS/rejection terms and counted-ROM terms are checked nonnegative
     expressions rather than zero gaps, and the structural challenge-support side
     condition is concrete. `CountedLazyROM` now gives the game boundary for
     prequery, reprogramming, and min-entropy bad events, `CountedLazyROMBadGame`
     exposes the bad flag probability at the adversary boundary, and
     `haetae_euf_counted_rom_bound` gives a top-level theorem target using the
     subunit counted term. The counted term is checked as `37 / 2^58`. The
     current counted internal-transcript simulated-signing game now proves
     `counted_lazy_rom_bad_flags_budget_sound` directly by storing prior
     lazy-ROM outputs, preserving clear bad flags across adversary and signing
     oracle calls, proving transcript min-entropy, and keeping the programmed
     site list empty. The paper-faithful programmed simulator now exists and
     proves the min-entropy bad flag has zero probability. A budgeted
     programmed-signing game now enforces the concrete `qH = 2`, `qS = 2`
     query-count discipline through the adversary oracle interface and proves
     that the invariant is preserved by arbitrary adversary calls. The
     one-step prequery probability is now derived from a concrete spread theorem
     for `honest_signing_programming_site_query`, the checked 58-bit signing
     entropy token, and concrete query-set cardinality. The repaired
     entropy-bearing model is not merely a challenge-output support argument:
     the token is carried by signing coins, exposed in `commitment_lowbits`,
     extracted from the programmed-site ROM input, and bounded through
     `honest_signing_programming_site_query_spread` and
     `programmed_site_prequery_one_step_concrete_bound`. The one-step
     prequery-or-reprogram lift is also checked under an explicit
     conflict-free programmed-site log premise
     (`programmed_site_prequery_reprogram_one_step_concrete_bound`). The
     budgeted programmed game now threads that conflict-free programmed-log
     invariant through every adversary oracle call and proves
     `bad_reprogram` has probability zero
     (`budgeted_programmed_bad_reprogram_zero`). The direct-sampler adaptive
     prequery lift is now checked: `DirectSigningCoinSampler.sample` is tied to
     `drandom_coins`, the message-hash and prior-query prequery probability is
     bounded by `direct_signing_coin_sampler_message_hash_budgeted_prequery_bound`,
     and `budgeted_sampled_direct_bad_prequery_bound` lifts that one-step bound
     through the adversary hash/signing counters. The final direct-sampler
     branch theorem is `budgeted_sampled_direct_prequery_reprogram_bad_checked_31`.
     Do not replace this with challenge-output support alone; the checked
     `programming_site_prequeried_output_irrelevant` lemma shows that prequery
     is a property of the ROM input, not the programmed challenge output.
  6. Mechanize the adversary-level simulated signing hop
     The exact real-signing simulator hop is already checked, and the real
     HAETAE game now has an exact erasure hop into a ROM-faithful
     transcript-logging internal game. The missing part is the statistical
     simulated-signing hop:

     EUF_CMA_simulated_signing
     <= UF_NMA + fs_aborts_loss + rejection_loss

	  The ROM-transcript route now accepts a clear-site reduction premise and
	  pushes the bad-site branch into both the existing FS bound and the counted
	  ROM bound. `PaperSimSigningSampler` and
	  `ROMInternalTranscriptPaperSimAsNMA` now provide the concrete adversary
	  boundary for the sampled simulator, and
	  `euf_cma_security_from_paper_sim_nma_and_counted_bimodal` shows how the
	  top-level theorem consumes its rejection-loss-aware NMA premise. The
	  structural `ROMPaperSimSigningSampler` instance additionally has an exact
	  NMA bridge and top-level counted theorem; `RealSigningPaperSimSampler` does
	  the same for the current `sign_internal` transcript game. The full
	  simulated-signing hop should still replace that structural sampler/premise
	  with a
	  byequiv/byphoare sequence over the real HAETAE rejection sampler and explicit
	  bad events.
  7. Prove forking extraction
     The current extractor computes a response difference from the two embedded
     signature transcripts and builds a fork-specific `A,t` target equation from
     the transcript pair. This removes the structured-zero instance but remains
     tautological until the structural public-key reconstruction is replaced by
     the HAETAE public-key/commitment algebra equation that pins `t` to the
     public key, commitment, and two challenges. The transcript and ROM layers
     now prove that valid fork pairs share the challenge-query site both through
     transcript fields and through actual signature fields, have distinct
     signature-field challenges, share the reconstructed commitment highbits, and
     satisfy a checked uniform public-reconstruction relation over the
     signature-field response-aux/public-key challenge relation. Use those facts
     as the fixed fork-site invariant in the next extraction proof.
     Replace the remaining tautological target construction with a paper-faithful
     EasyCrypt extractor proof:
      - run adversary twice with same prefix randomness
      - program different challenges at the same transcript point
      - obtain two valid signatures
      - prove they share the same commitment target
      - extract a bimodal self-target MSIS solution
  8. Prove bimodal MSIS to Module-SIS
     The instance/solution validity lift is now exposed as checked solver-level
     and mode-aware adversary-boundary games
     (`BimodalToModuleSIS_Lift_Game`,
     `ModuleSIS_LiftedDistribution_Relation_Game`,
     `ModuleSIS_ModeRelation_Game`) with an exact adapter theorem for the
     bimodal-sourced view. The full hardness handoff still needs a distributional
     embedding theorem from the bimodal-sourced Module-SIS view to the concrete
     Module-SIS hardness sampler. Replace bimodal_to_module_sis_lift_obligation by
     concrete algebra:
      - define bimodal self-target MSIS instances
      - define Module-SIS instances
      - implement the lift map
      - prove validity preservation and norm bounds
      - prove the lifted bimodal instance distribution is a valid concrete
        Module-SIS instance distribution for the target hardness game
  9. Assemble the final theorem
     Delete interface readiness assumptions from HAETAE_Security.ec. The final theorem should consume only:
      - MLWE game bound
      - Module-SIS game bound
      - concrete HAETAE parameter facts
      - concrete query bounds
