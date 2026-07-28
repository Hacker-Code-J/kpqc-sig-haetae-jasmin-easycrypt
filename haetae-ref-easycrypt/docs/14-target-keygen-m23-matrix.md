# Target Mode-2 Key-Generation Matrix Arithmetic, Finalization, Helper Totality, and First-Attempt Composition

## Scope

This milestone qualifies the actual extracted helper:

```text
KeygenMode2ParentTarget.M._kp_m23_matrix
```

The source procedure is `_kp_m23_matrix` in
`../haetae-ref-jasmin/jasmin/keypair.jazz`. For mode 2, the caller fixes
`rows = 2` and `cols = 3`. The extracted helper performs:

1. a 768-word copy from `s1p` into `s1hatp`;
2. forward NTT over three 256-word polynomials;
3. a two-row, three-column pointwise matrix accumulation; and
4. inverse NTT over two 256-word output polynomials.

The proofs use this procedure inside the zero-drift actual-parent extraction.
They do not introduce a replacement Jasmin implementation.

The same milestone also qualifies the actual extracted
`KeygenMode2ParentTarget.M._keypair_finalize_m23` helper at the mode-2 count
of 512 words. Its base specification records the exact extracted word
operations. Separate semantic theories now prove canonical reduction on the
reachable input range and identify the resulting pointwise low/high operations
with the coefficient decomposition in `HAETAE_Algebra`.

The final proof in this gate reaches the actual fixed-parameter
`_keypair_full_m23` through a result-carrying mirror that peels its
unconditional first attempt, records that attempt, and retains the complete
residual retry loop and both packing calls. This is a bounded relational and
first-trace result, not a termination, acceptance, packing-semantics, or
end-to-end key-generation theorem.

## Algebraic specification

`easycrypt/spec/KeygenM23MatrixSpec.ec` fixes the mode-2 dimensions and
provides the word-prefix and tail-frame predicates used throughout the proof:

- `word_prefix_eq left right words` compares a selected word prefix;
- `word_tail_frame before after words` states that every complete `W32` word
  after that prefix is unchanged; and
- `word_tail_frame_trans` composes frame facts across consecutive stages.

`easycrypt/spec/KeygenM23ArithmeticSpec.ec` gives the active regions
mathematical polynomial views:

- `wide_poly` views a 256-word `BArray8192` slice as an `Rq.poly`;
- `matrix_poly` views one row/column cell of the active `BArray32768` matrix;
- `pointwise_row_words` is the exact three-term source accumulator, with one
  Montgomery factor `inv NTT_Fq.R` per product;
- `pointwise_row_ntt` rewrites those vector words as
  `NTTFullSpec.full_ntt` values; and
- `output_row` applies `NTTFullSpec.full_invntt` and
  `NTT_Fq.array256_mont` to the pointwise result.

The main representation predicates record both polynomial identity and signed
word bounds:

| Predicate | Active mode-2 region | Bound |
| --- | --- | --- |
| `mode2_input_repr_bound16` | three input-secret polynomials | 16 |
| `mode2_ntt_repr_bound24` | three forward-NTT polynomials | 24 |
| `mode2_pointwise_repr_bound18` | two accumulated rows | 18 |
| `mode2_output_repr_bound16` | two inverse-NTT output rows | 16 |

`pointwise_row_words_ntt`, `mode2_pointwise_words_ntt`, and
`mode2_output_words_ntt` connect the source-word accumulator to the NTT-based
algebraic form used in the final helper theorem.

## Authored results

### Copy, frames, and totality

`easycrypt/refinement/TargetKeygenM23Matrix.ec` retains the structural
contracts and now also proves fixed-mode totality.

`kp_copy_vec_mode2_correct` proves that the generated 768-word copy:

- returns its first 768 destination words equal to the source; and
- preserves destination words 768 through 2047.

`kp_copy_vec_mode2_scratch_independent` and
`kp_m23_matrix_mode2_active_prefix_scratch_independent` establish the
corresponding active-prefix independence from the incoming `bp` and `s1hatp`
scratch arrays.

The losslessness stack consists of:

- `kp_copy_vec_ll`;
- `fqmul_ll`;
- `polyvec_ntt_mode2_ll`;
- `polymat_pointwise_mode2_ll`;
- `polyvec_invntt_mode2_ll`; and
- `kp_m23_matrix_mode2_ll`.

The last theorem proves probability-one termination of the actual
`Parent._kp_m23_matrix` whenever `rows = 2` and `cols = 3`. It does not require
a sampling-progress certificate.

### Wide-array NTT adapters

`easycrypt/refinement/TargetKeygenM23WideSupport.ec` defines checked
`BArray8192` slice and replacement operations. In particular,
`wide_slice_poly_repr_bound` relates an active 256-word slice to the existing
single-polynomial `BArray1024` representation theorem, while the slice and
frame lemmas show that replacing one polynomial preserves all other words.

`easycrypt/refinement/TargetKeygenM23WideNTT.ec` proves
`polyvec_ntt_mode2_equiv` between the actual parent loop and a proof-only
three-slice adapter. `parent_polyvec_ntt_mode2_correct` then proves that three
16-bit input representations become three
`NTTFullSpec.full_ntt` representations at bound 24 and that words after the
768-word active region are unchanged.

### Exact three-column pointwise sum

`easycrypt/refinement/TargetKeygenM23Pointwise.ec` qualifies the actual
`Parent._polymat_pointwise_acc` loop. `parent_fqmul_16_24` proves that a
16-bit matrix word multiplied by a 24-bit transformed-secret word computes
the checked Montgomery product and returns a 16-bit result.

The loop invariant follows initialization and all three column additions for
each of the two rows. `polymat_pointwise_mode2_repr_bound18_frame` proves that,
from `matrix_active_bound16` and `mode2_ntt_repr_bound24`, the actual procedure
returns:

- `mode2_pointwise_repr_bound18`, whose row polynomial is the sum of exactly
  the three Montgomery-reduced products; and
- a tail frame after the 512-word output region.

### Bound-18 inverse NTT

The standalone NTT refinement now exports
`target_poly_invntt_correct18` and
`target_poly_invntt_jazz_correct18`. They accept the conservative 18-bit bound
produced by the three-column accumulator and return the Montgomery
representation of `NTTFullSpec.full_invntt` at bound 16.

`easycrypt/refinement/TargetKeygenM23WideInvNTT.ec` lifts that result through
the actual two-polynomial `BArray8192` loop:

- `polyvec_invntt_mode2_equiv` relates the parent loop to its slice adapter;
- `polyvec_invntt_mode2_correct18` proves the two bound-18-to-bound-16
  polynomial contracts; and
- `polyvec_invntt_mode2_pointwise_correct18` instantiates those contracts with
  the two exact pointwise rows.

The two correctness theorems also preserve words after the 512-word active
output.

### Direct actual-helper arithmetic theorem

`easycrypt/refinement/TargetKeygenM23Arithmetic.ec` composes the copy, forward
NTT, pointwise, and inverse NTT contracts without replacing the helper.

`kp_m23_matrix_mode2_arithmetic_correct` is a Hoare theorem about
`Parent._kp_m23_matrix`. Under fixed dimensions `(2, 3)`,
`matrix_active_bound16 ap`, and `mode2_input_repr_bound16 s1p p0 p1 p2`, it
establishes:

- `mode2_output_repr_bound16 res.1 ap p0 p1 p2`;
- `mode2_ntt_repr_bound24 res.2 p0 p1 p2`;
- preservation of every `bp` word after the 512-word active prefix; and
- preservation of every `s1hatp` word after the 768-word active prefix.

Together with `kp_m23_matrix_mode2_ll`, this gives both partial-correctness
arithmetic semantics and probability-one termination for the actual fixed-mode
helper.

### Exact word-level finalization

`easycrypt/spec/KeygenM23FinalizeSpec.ec` defines the target operations
`freeze_word`, `frozen_sum_word`, `egen_low_word`, and `egen_high_word`
directly over `W32`/`W64`. It then defines:

- `finalize_b_word` as the word-level EGen high output of the frozen sum of
  the incoming `bp`, sampled `s2p`, and sampled `ap` words;
- `finalize_s2_word` as the sampled `s2p` word minus the corresponding
  word-level EGen low output; and
- `finalize_output` as both exact first-512-word results together with tail
  frames for both returned arrays.

`easycrypt/refinement/TargetKeygenM23Finalize.ec` proves
`freeze_word_correct` for the actual extracted `Parent.__freeze` procedure.
`keypair_finalize_m23_mode2_correct` then proves the exact
`finalize_output` contract for the actual
`Parent._keypair_finalize_m23` specialized to
`count = 512`. The proof retains the original `bp`, `s2p`, and `ap` arrays in
its loop invariant, so each result word is stated against the corresponding
initial words.

The accompanying totality surface separates three facts:

- `freeze_word_ll` proves scalar freeze losslessness;
- `keypair_finalize_m23_ll` proves unconditional losslessness of the helper
  for any `W64` count; and
- `keypair_finalize_m23_mode2_ll` gives the fixed-mode probability-one
  termination statement.

### Canonical and HAETAE coefficient finalization

`easycrypt/spec/KeygenM23FinalizeSemantics.ec` supplies the scalar semantic
bridge without changing the exact word specification:

- `barrett_residue_range` proves the Barrett candidate lies in `[0,q]` and
  has the input residue for every integer in `[-2^18,2^18)`;
- `freeze_word_semantics` proves that the complete W64/W32 correction
  sequence returns `W32.of_int (W32.to_sint a %% 64513)` for every
  `Fq.bw32 a 18` input;
- `freeze_word_canonical` records the resulting range `[0,64513)`; and
- `finalize_words_semantics` identifies the exact word-level EGen high word
  and adjusted `s2` word after freezing.

`easycrypt/spec/KeygenM23FinalizeArraySemantics.ec` proves that the inputs
already produced by this mode-2 path are sufficient. A bound-16 inverse-NTT
word, a centered `s2` word in `[-1,1]`, and a uniform coefficient below
`64513` have an exact, non-wrapping integer sum in `[-65537,130048]`, hence a
signed 18-bit word. `finalize_output_semantics` lifts the scalar result across
all 512 active words and retains both exact tail frames. Its decoded
postcondition is:

```text
bp[i]  = vk_high((sint(pre_bp[i]) + sint(sampled_s2[i])
                  + uint(sampled_avec[i])) mod 64513)
s2[i]  = sint(sampled_s2[i]) - vk_low(the same residue)
```

`easycrypt/spec/KeygenM23FinalizeHAETAEBridge.ec` proves the local
`vk_low_int` and `vk_high_int` definitions are exactly
`HAETAE_Algebra.coeff_decompose_vk_low` and
`HAETAE_Algebra.coeff_decompose_vk_high`. Its 512-word predicate and lifting
lemma therefore restate the preceding result directly with the abstract
HAETAE coefficient operations. This is a pointwise decomposition bridge, not
an equality with the security model's complete key-generation procedure.

## Proof-only parent observers

### Sampler-plus-M23 observer

`easycrypt/refinement/TargetKeygenM23ParentComposition.ec` defines
`CheckedMode2ParentM23Prefix.run`. This authored observer first calls the
previously checked `CheckedMode2ParentSamplerPrefix.run`, then calls the actual
extracted `Parent._kp_m23_matrix` with `(rows, cols) = (2, 3)`. It returns
`(seedbuf, mat, s1, bp, s1hatp)`.

`checked_mode2_parent_m23_prefix_correct` composes:

- exact seed-expansion slices;
- finite-stream, range, centered-range, and frame properties for the sampled
  matrix and first `s1`;
- the sampler-derived matrix bound 16 and three secret-polynomial input
  representations at bound 16;
- the helper's two algebraic output rows at bound 16;
- the retained three forward-NTT secret rows at bound 24; and
- the 512-word and 768-word output tail frames.

`checked_mode2_parent_m23_prefix_progress_ll` proves probability-one
termination under `mode2_sampler_prefix_progress`. The certificate premise is
needed only for the rejection-sampling prefix; the following
`_kp_m23_matrix` call is unconditionally lossless at the fixed dimensions.

This observer is deliberately not
`KeygenMode2ParentTarget.M._keypair_full_m23`.

### Sampler-plus-M23-plus-finalizer observer

`easycrypt/refinement/TargetKeygenM23FinalizeComposition.ec` defines
`CheckedMode2ParentM23Finalize.run`. It follows the checked first-attempt
sampler with the actual fixed-mode `_kp_m23_matrix` and then the actual
`_keypair_finalize_m23` at count 512.

`checked_mode2_parent_m23_finalize_correct` preserves:

- all `mode2_sampler_facts`, including seed expansion, sampled matrix/vector
  streams, coefficient ranges, frames, and the first-attempt counter;
- all `mode2_m23_facts`, including the exact algebraic M23 outputs,
  transformed-secret representation, and both M23 tail frames; and
- the exact word-level `finalize_output` for both returned arrays, relative to
  the pre-finalization `bp`, sampled `s2`, and sampled `avec`.

`easycrypt/refinement/TargetKeygenM23FinalizeSemanticComposition.ec`
strengthens that theorem by consequence. It derives, for every active index,
the three reachable-input premises from the retained certificates:

- `mode2_output_repr_bound16` supplies the pre-finalization `bp` bound;
- `eta_vector_centered8192` supplies the sampled `s2` interval; and
- `uniform_vector_range8192` supplies the strict-below-`64513` `avec` bound.

`checked_mode2_parent_m23_finalize_semantic_correct` adds the local canonical
512-word postcondition. `checked_mode2_parent_m23_finalize_haetae_correct`
adds the equivalent abstract HAETAE low/high and adjusted-`s2` coefficient
postcondition while preserving all sampler facts, M23 facts, exact word
outputs, and tail frames.

`checked_mode2_parent_m23_finalize_progress_ll` proves probability-one
termination under `mode2_sampler_prefix_progress`. The certificate conditions
only the sampler prefix; the fixed-mode M23 and finalizer helpers use their
separate losslessness results.

This composition remains a proof-only observer. It does not call or establish
a theorem about the actual `Parent._keypair_full_m23`.

### Actual fixed-mode singular and FFT word semantics

`easycrypt/spec/KeygenM23SingularSpec.ec` and
`easycrypt/spec/KeygenM23SingularFFTSpec.ec` define an exact evaluator for the
machine operations used by the mode-2 singular rejection call. The evaluator
retains `W32` and `W64` addition, subtraction, multiplication, sign extension,
truncation, shifts, and array updates. It models:

- bit-reversal initialization of each 256-coefficient slice;
- the eight-stage, 128-butterfly-per-stage FFT schedule;
- the five calls over three `s1` slices and two adjusted-`s2` slices, threading
  the same FFT scratch array between calls exactly as the extracted procedure
  does;
- all 256 rounded squared-magnitude accumulations per slice; and
- the fixed five-entry selector and finish computation at
  `(best_count, tau, rem) = (5, 58, 24)`.

`TargetKeygenM23SingularHelpers`, `TargetKeygenM23SingularFFT`, and
`TargetKeygenM23Singular` compose those contracts against the actual extracted
procedures. In particular, `singular_full_mode2_word_exact` proves that
`Parent._singular_full` at `(mcount, kcount, best_count, tau, rem) =
(3, 2, 5, 58, 24)` returns `mode2_singular_word` on its two input arrays and
the extracted `jfft_roots` and `jfft_brv8` constants.
`m23sing_total_singular_full_mode2_ll` separately proves probability-one
termination of that fixed call. `mode2_singular_guardE` identifies the
extracted unsigned acceptance guard with
`W64.to_uint(score) <= 611098`.

These are exact finite machine-word semantics. They do not assert that the
fixed-point FFT equals a real or complex DFT, establish numerical error or
non-overflow bounds, identify the returned word with the paper's intended
singular-value quantity, or prove that the bound is satisfied.

### Actual parent with an immutable first-attempt trace

`easycrypt/refinement/TargetKeygenM23FullFirstAttempt.ec` defines
`Mode2FullFirstAttempt.run`. The mirror executes the checked sampler, actual
fixed-mode M23 helper, actual 512-word finalizer, singular call, and extracted
machine guard for the first attempt. It records an immutable trace immediately
after that guard, then executes the complete residual retry loop and the actual
`_pack_vk_m23` and `_pack_sk_m23` calls.

`mode2_full_first_attempt_equiv` relates this mirror to the actual
`Parent._keypair_full_m23` under equal initial arrays and seed plus the exact
mode-2 parameters:

```text
(k, m, vkbytes, best_count, tau, rem, singular_bound)
= (2, 3, 992, 5, 58, 24, 611098)
```

Its postcondition is exact equality between the actual returned `(vkp, skp)`
pair and the result component returned by the mirror. Because the mirror keeps
the residual retry loop and both pack calls, the theorem does not replace
post-attempt parent control flow. The relational judgment does not prove that
either side terminates, and equality of packed results is not a proof that the
packing format is correct.

`mode2_full_first_attempt_snapshot_correct` proves that the mirror's immutable
first trace contains:

- the exact checked mode-2 sampler facts and counter value `5`;
- the exact M23 arithmetic and frame facts;
- the exact 512-word finalizer output, canonical finalizer semantics, and
  abstract HAETAE coefficient-decomposition facts;
- equality between `sv` and the exact fixed-mode `mode2_singular_word`
  evaluator;
- the machine bound `611098`; and
- the exact extracted guard relation
  `reject = (if bound \ult sv then W64.one else W64.zero)`, together with
  `accepted = (reject = W64.zero)`.

`mode2_full_first_attempt_score_guard_correct` further proves that the trace's
accepted bit is equivalent to `W64.to_uint(sv) <= 611098`.
`mode2_full_first_attempt_accepted_correct` retains the conditional consequence
that an accepted trace satisfies `! (bound \ult sv)`. Neither theorem proves
that the first attempt is accepted, and no theorem assigns an analytic
real/spectral singular-value interpretation to `sv`.

## Verification

Run:

```sh
./scripts/verify-keygen-m23-matrix-proof.sh
./scripts/verify-ntt-proof.sh
```

The matrix, finalization, and first-attempt gate checks:

- canonical source-hash success;
- zero regeneration drift for the 32-file, 56-procedure parent extraction,
  the 25-file, 31-procedure sampler-caller extraction, and the 10-file target
  NTT extraction;
- a matching hash manifest for the project-owned NTT loop support and the 17
  imported NTT dependency theories;
- successful fresh `-no-eco` compilation of all 23 authored manifest entries,
  including `TargetKeygenM23FullFirstAttempt.ec`; and
- clean proof-hole, authored-axiom, and leftover debug-command scans.

A successful current run reports
`RESULT: PASS compiled=23 total=23 mode=-no-eco` with exit status 0.

The standalone NTT gate at `2026-07-23T20:40:27Z` separately passed source and
support hashes, zero target-extraction drift, three generated-representation
identity checks, fresh `TargetNTTRefinement.ec` compilation, and hole/axiom
scans. That run includes the bound-18 inverse theorems used above.

## Claim boundary

The verified milestone reaches exact word-level finalization, canonical
reduction, the abstract HAETAE coefficient decomposition, and exact
machine-word semantics plus totality for the actual fixed-mode singular/FFT
call. It also relates the actual fixed-parameter `_keypair_full_m23` result to
a peeled first-attempt mirror and proves exact semantic facts about that
mirror's immutable first trace. It does **not** establish:

- that the first attempt is accepted, semantics for rejected attempts, or
  termination or losslessness of the residual outer retry loop;
- an analytic real/complex or spectral interpretation for the exact
  `_singular_full` evaluator, numerical FFT error bounds, a non-overflow/range
  theorem, or identity with the paper's intended singular-value quantity;
- equality between the target NTT/matrix representation and the complete
  list-based multiplication and key-generation equations used by the
  security model;
- correctness or format semantics of either key-packing call, despite their
  operational preservation in the relational mirror, or the public
  key-generation API;
- pointer aliasing, separation, or source-pointer safety;
- universal sampler-progress certificates or sampler distributions;
- modes 3 or 5; or
- composition with the provable-security theorem.
