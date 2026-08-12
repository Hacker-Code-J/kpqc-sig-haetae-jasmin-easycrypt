# Roadmap

## Sprint 1 — completed evidence baseline

1. Pinned the official PDF, implementation, proof trees, and toolchain.
2. Wrote the top-level functional-correctness and security signatures.
3. Extracted focused Sign/Verify transcript procedures.
4. Proved the position-64 mu32 absorb equivalence and byte-list congruence.
5. Reused the existing KeyGen first-attempt/FFT/guard results through an
   import-only adapter without weakening their premises.
6. Established fresh compilation, hole/axiom scans, source drift checks, and
   baseline verification.

## Sprint 2 — completed results

1. **Packer closure — PROVED partial correctness.**
   `pack_sk_m23_mode2_vk_prefix` proves the actual generated packer property;
   `keypair_full_m23_mode2_return_prefix` and
   `keypair_internal_mode2_return_prefix` lift it to returned mode-2 KeyGen
   values. Retry termination and distribution remain separate.
2. **Raw helper hash closure — PROVED.**
   Actual generated absorb, Keccak, finalize, and 64/32-byte squeeze procedures
   are composed in `sign_verify_raw_mu_top_wrappers_prefix`.
3. **Composition seam — PROVED for explicit raw wrappers.**
   `raw_mu_to_challenge_suffix_zero_loss` connects the raw mu prefix to the
   actual Week 1 challenge-suffix absorb. The required 992-byte memory relation
   is constructible from a returned KeyGen prefix.
4. **Generated top-level control — PARTIAL.**
   `OBL-MU-TOPLEVEL-CONTROL` still separates `_sf_mu_rawpre` and the raw branch
   of `__verify_hash_mu` from the proved local wrappers.
5. **Public context — SPECIFIED.**
   The high-bit/context branch remains separate and unproved.
6. Focused extraction hashes, 11 authored targets, baselines, and the LaTeX
   research notes are integrated into one verifier.

## Sprint 3 — generated raw mu control closed

1. **Sign exact top adapter — PROVED.**
   `sf_mu_rawpre_refines_raw_top` relates the actual generated Sign procedure
   to the Week 2 wrapper.
2. **Verify raw-branch exact top adapter — PROVED.**
   `raw_prelen` is converted to the actual shift-63 branch guard without a new
   axiom, and `verify_hash_mu_raw_refines_raw_top` relates the selected branch
   to the Week 2 wrapper.
3. **Generated cross-procedure mu prefix — PROVED.**
   `sign_verify_generated_raw_mu_prefix` directly compares
   `_sf_mu_rawpre` and `__verify_hash_mu`.
4. **Generated challenge suffix — PROVED.**
   `generated_raw_mu_to_challenge_suffix_zero_loss` justifies
   `delta_mu_raw_top = 0` only for the raw/internal mu seam.
5. **Public API memory chain — PARTIAL with actual helpers proved.**
   `keygen_export_vk_mode2_prefix`, `keygen_export_sk_mode2_prefix`,
   `sign_import_mode2_sk_prefix`, and `verify_import_mode2_vk_prefix` open the
   actual generated copy procedures and prove their mode-2 prefix behavior.
   `keygen_export_sk_mode2_prefix_frames_vk` proves the required disjoint
   write frame for an already exported VK region.
   `imported_sign_sk_reaches_mu_memory` connects those byte relations to the
   generated mu theorem. The remaining `OBL-API-KEY-MEMORY-RAW` is the
   actual caller composition of the two exports, the generated importer's
   `ui64`-to-`int` caller binding, and public-call orchestration.

## Sprint 4 — raw ABI caller evidence, parent still partial

1. **Raw caller extraction — PROVED reproducible.** The three actual
   `cryptolab_haetae_mode2_*_internal` roots and reachable closures are pinned
   by generated hashes.
2. **Address bridge — PROVED.** Canonical `int` ABI addresses round-trip through
   `W64.of_int`; 992/1408/1474-byte region specializations compile.
3. **KeyGen caller — PARTIAL.** Actual-to-trace memory equivalence and both
   exporter/frame theorems compile. The single sequential caller Hoare
   postcondition remains named after bounded proof attempts stalled in final
   array-post normalization.
4. **Sign caller — PROVED to exact trace.** The actual raw Sign caller imports
   1408 bytes, exposes its 992-byte prefix and exact raw hash arguments, and
   preserves its full signing continuation/result through the mirror.
5. **Verify caller — PARTIAL.** Exact trace refinements compile through
   `sign_verify_internal_mode2_jazz`; the public/raw lift and proof that a
   corresponding signature reaches `_sign_verify_tail_m23` remain open.
6. **Stores-free memory bridge — PROVED conditionally.** Actual external-memory
   facts, canonical address binding, and Sign import imply the Week 3
   `sk_memory_prefix` premise. This is not caller reachability by itself.

## Sprint 5 — accepted-path control separated from functional correctness

1. **Actual KeyGen sequential export — PROVED as partial correctness.**
   `keypair_raw_api_exports_matching_prefixes` opens the actual raw KeyGen
   caller and concludes pointwise external VK/SK prefix equality.  It neither
   assumes nor proves retry termination.
2. **Verify outer trace — PROVED.**
   `_api_verify_mode2_raw` and
   `cryptolab_haetae_mode2_verify_internal` are exactly related to mirrors that
   preserve final result and memory on every early-reject and tail branch.
3. **Accepted control path — PROVED.**
   The full M23, internal, raw, and cryptolab lifts establish
   `accept => tail_reached`; accepted traces bind the actual
   `__verify_hash_mu` VK/pre/message inputs.
4. **Generated accepted-path adapters — PROVED with a boundary.**
   `raw_api_accepting_execution_hash_mu_zero_loss` compares the actual
   generated hash procedures under facts supplied by the traces, and the
   suffix theorem composes the position-64 generated absorb helpers.
5. **Former parent claim — SPLIT.**
   `OBL-API-KEY-MEMORY-RAW-ACCEPT` remains **PARTIAL** until a direct theorem
   relates the Sign and accepted Verify traces' `observed_mu` outputs. Week 6
   subsequently closes the Sign-output frame child.
   `OBL-SIGN-OUTPUT-TAIL-REACH` and `OBL-SIGN-VERIFY-CORRECTNESS` are separate
   functional-correctness obligations.

## Sprint 6 — frame and locality closed; direct observation still partial

1. **Actual Sign output frame — PROVED as partial correctness.**
   The actual raw Sign caller preserves disjoint VK/SK/pre/message regions
   across the 1474-byte signature copy and 8-byte siglen store.
2. **Region-local generated mu equality — PROVED.**
   The actual `_sf_mu_rawpre ~ __verify_hash_mu` theorem now uses only
   SK/VK-prefix equality and byte equality on the pre/message read regions;
   whole-memory equality is gone.
3. **Actual sequential trace — PROVED for control/results/memory.**
   Actual raw Sign followed by actual raw Verify is exactly related to the
   corresponding trace sequence. Accepted execution implies `tail_reached`,
   and both observed hash input descriptors are post-state facts.
4. **Direct observed mu — PARTIAL.**
   No compiled theorem yet concludes
   `mu32_prefix(SignTrace.observed_mu, VerifyTrace.observed_mu)` after the two
   trace calls. The missing step is a product/replay semantics rule, not
   another memory-frame or byte-locality lemma.

The security lane remains **no-go for a claimed API zero-loss bound**:
`delta_mu_raw_api_accept = 0` is unavailable. Because Week 6 was the final
focused caller-plumbing sprint, Week 7 should not add another observational
wrapper. Either design and validate one explicit product/replay proof rule, or
freeze the compiled Week 5/6 generated-hash adapter as the paper boundary and
move the main proof effort to a separately scoped functional or security lane.

The functional lane may specify, but must not assume,
`OBL-SIGN-OUTPUT-TAIL-REACH`: a Sign-produced signature passes unpack and norm
gates.  Its proof requires pack/unpack inverse, norm, hint, arithmetic, and
challenge results and remains independent of the accepted-forgery lane.

## Subsequent functional work

- KeyGen: retry losslessness/termination, packing/parsing, public-memory
  contract, distribution, singularity effect, fixed-point error, and TieMin.
- Sign: secret-key parse, public-key embedding, context encoding, hyperball
  sampler, accepted-attempt equations, rejection loop, hints, and packing.
- Verify: canonical parse, matrix reconstruction, norm/hint equations,
  highbits/LSB transcript equality, and exact accept/reject equivalence.

## Security work

After exact API refinement exists, instantiate a byte-faithful
`Sig_ROM.Scheme` and prove the implementation bound. Then close challenge
support/cardinality, accepted signing distribution, exact ROM domains, retry
loss, and two-transcript extraction before relying on the existing conditional
paper reduction.

## Sprint 7 — decision and signature codec refocus

1. **Product/replay — DEFERRED / FREEZE-A.**
   `OBL-MU-PRODUCT-REPLAY` was time-boxed and frozen as an explicit paper
   boundary. No compiled bridge relates actual generated hash returns to
   completed trace observations without new axioms, unjustified one-sided
   losslessness, or wrapper widening. `delta_mu_raw_api_accept = 0` remains
   unavailable.
2. `pack_sig_mode2_full_jazz` and `unpack_sig_mode2_full_jazz` are now pinned
   by generated extraction hash.
3. The mode-2 wrapper parameters and 1474-byte layout are audited from actual
   extracted code.
4. **Actual prefix codec — PROVED as partial correctness / GO-B.**
   `pack_sig_prefix_mode2_layout` and `unpack_sig_prefix_mode2_layout` open the
   actual generated procedures. The sequential
   `pack_unpack_sig_prefix_mode2_roundtrip` proves challenge and 1024 signed
   low-word recovery on canonical inputs, with a compiled non-vacuity witness.
5. **Frames — PARTIAL.** The unpack low-array tail is preserved; pack and
   challenge-array tail frames remain named residuals.
6. Week 8 starts with `OBL-SIG-HBZ-ENCODE-DECODE`, then reuses the rANS proof
   structure for `OBL-SIG-H-ENCODE-DECODE` and canonical suffix composition.

## Sprint 8 — HBZ suffix codec, success-conditioned boundary only

1. **Actual HBZ leaves — PROVED.**
   `Mode2HbzPrepare`, `Mode2HbzApply`, and `Mode2HbzLeafRoundTrip` close the
   mode-2 coefficient↔symbol prepare/apply layer and its local tail frames.
2. **Actual procedure identity across extraction routes — PROVED.**
   `Mode2HbzActualBoundary` shows that the focused HBZ extraction and the
   Week 7 signature pack/unpack extraction expose the same actual
   `_encode_hb_z1_full` / `_decode_hb_z1_full` procedures.
3. **Concrete mode-2 table certificate — PROVED.**
   `Mode2HbzTableCertificate` and
   `Mode2HbzSymbolWordsGenerated.actual_mode2_hbz_tables_certified`
   close the concrete actual-array compatibility claim.
4. **Pure rANS step inverse — PROVED.**
   `Mode2RansCore.hbz_fast_step_decode_inverse` proves that the concrete
   reciprocal encoder step is inverted by the mathematical decoder step for
   `1 <= x < hbz_xmax(s)`.  It does not cover emitted normalization bytes.
5. **Actual rANS loops and full HBZ composition — PARTIAL/BLOCKED.**
   The reverse encoder byte stack, forward decoder consumption, actual loop
   refinements, success-conditioned full-wrapper theorem, and successful
   actual witness still need compilation before
   `OBL-SIG-HBZ-ENCODE-DECODE` can be promoted.
6. **Week 9 decision — CONTINUE-RANS.**
   Focus on the single reverse-byte-stack/forward-consumption invariant and
   its actual encoder/decoder refinements.  Do not expand to the `h` codec or
   highbits/LSB until the actual HBZ parent theorem and witness compile.

## Sprint 9 — common byte trace and actual core boundary

1. **Pure `xs/cuts/bytes` trace — PROVED.**
   `Mode2RansByteStack` fixes the reverse-encoder/forward-decoder index
   convention, proves 0/1/2-byte normalization readback, proves state-bound
   preservation, and connects the trace head to the Week 8 fast-step inverse.
2. **W32/W64 normalization semantics — PROVED as leaf facts.**
   `Mode2RansNormalization` proves shift/division, truncate/remainder,
   one/two-byte append order, and cursor no-underflow lemmas. These are not yet
   a theorem about the nested generated loops.
3. **Actual suffix copy — PROVED.**
   `copy_encoded_suffix_correct` directly opens
   `HbzFullEncodeTarget.M.__copy_encoded_suffix` and proves exact slice copy
   plus the `[size,2048)` frame.
4. **Actual encoder/decoder control surfaces — PROVED; refinements PARTIAL.**
   Direct Hoare theorems fix concrete mode-2 tables/count/state fields and
   prove the returned control bit is 0 or 1. They do not prove trace equality,
   decoded symbols, final state, or consumed size.
5. **Unary actual harness — PROVED for control only.**
   The harness calls actual `_rans_encode`, actual `__copy_encoded_suffix`,
   and actual `_rans_decode`, takes the success branch from the encoder result,
   and fixes decoder inputs to `(1024,size,13)`. No success or inverse premise
   is introduced.
6. **Week 10 decision — CONTINUE-RANS.**
   The single next obligation is the actual encoder outer-loop invariant that
   derives `valid_rans_trace` and `4 <= size <= 1024` from the generated
   success branch. Only after that compiles should the decoder consumption
   invariant be completed. The `h` codec remains NO-GO.

## Sprint 10 — encoder-only semantic refinement

1. **BArray/list and suffix recurrence — PROVED.**
   `Mode2RansArrayListBridge` fixes the actual-array view, suffix index
   convention, canonical suffixes, `segment_matches`, `prefix_frame`, and the
   one-symbol `encode_trace` recurrence without 1024-way unrolling.
2. **Concrete encoder word step — PROVED at word level.**
   `actual_mode2_encoder_word_step_correct` checks the literal table fields,
   reciprocal high multiplication, shift ladder, complement/bias update, and
   W32/W64 no-wrap against `hbz_fast_encode_step`.
3. **Generated inner normalization — real but PARTIAL progress.**
   The direct `_rans_encode` Hoare proof now maintains an exact byte-segment
   and prefix-frame invariant through the nested actual `set8`/shift loop and
   proves cursor no-underflow.  Its finite phase is currently `0..4`; the
   pure trace's stronger `0..2` bound and exact normalization list have not
   yet been installed in the actual outer invariant.
4. **Final serialization leaf and actual success size — PROVED.**
   Four little-endian stores and outside-byte frame compile independently.
   `actual_rans_encode_success_size_bound` directly proves that the actual
   failure branch is retained and actual success yields
   `0 <= off <= 1020` and `4 <= 1024-off <= 1024`.
5. **Whole encoder trace postcondition — PARTIAL.**
   No compiled theorem yet states
   `segment_matches(returned_encp,off,trace_bytes(actual_symbols))` or
   `off + size(trace_bytes(actual_symbols)) = 1024`.  Therefore
   `OBL-RANS-ENCODE-REFINEMENT` stays `PARTIAL`.
6. **Week 11 decision — CONTINUE-ENCODER.**
   Restrict Week 11 to the actual outer one-symbol transition and generated
   final-store composition.  Do not begin decoder semantic refinement until
   the exact actual encoder suffix theorem compiles.  If that single edge
   remains blocked, freeze the current implementation boundary and redesign
   the trace representation instead of adding wrappers.

## Sprint 11 — actual encoder trace closure

1. **Tail-aware inner normalization — PROVED.**
   `encoder_inner_tail_inv` preserves the initial encoder prefix and the exact
   `inner_written_suffix ++ encode_trace(tail).bytes` segment through the
   generated nested loop. `encoder_inner_tail_exit_exact` derives
   `k=mode2_normalization_len<=2` at the actual guard exit.
2. **Generated table/WP word update — PROVED.**
   Literal `x_max`, reciprocal, bias, packed complement/frequency, shift,
   high-product and nested shift-ladder expressions are connected once to the
   pure `hbz_fast_encode_step` by `generated_outer_word_update_matches` and
   `generated_loaded_nested_word_update`.
3. **One-symbol and outer-loop closure — PROVED.**
   `encoder_generated_success_outer_post` composes the actual inner exit,
   generated word update, suffix recurrence, cursor equation and prefix frame.
   The failure transition drops only the live-trace implication and preserves
   the actual `bad=1` branch.
4. **Generated final stores — PROVED.**
   `generated_encoder_outer_finalize_success` identifies the four actual
   little-endian stores with a serialized state prepended to the accumulated
   normalization trace.
5. **Whole actual encoder suffix — PROVED as success-conditioned partial
   correctness.**
   `actual_rans_encode_trace_closure` and
   `actual_rans_encode_trace_refinement` directly target
   `RansEncodeTarget.M._rans_encode` and prove its successful returned suffix
   equals `trace_bytes(symbol_list_of_array(symbols0))`, with exact
   cursor/length equality and prefix frame. Success is not a precondition.
6. **Week 12 decision — GO-ENCODER.**
   The single next proof lane is actual `_rans_decode` trace consumption.
   Encoder success reachability/termination stays a separate stretch claim;
   full HBZ, `h`, metadata, and security work remain out of scope.

## Sprint 12 — actual decoder trace refinement

1. **State/cursor reference model — PROVED.**
   `Mode2RansDecoderCursorSteps` fixes the decoder boundary state and byte
   cursor at every symbol index, including cursor 4 initially, exact segment
   extension, final cursor equal to `size(trace_bytes syms)`, and final state
   `2^23`.
2. **Concrete generated word step — PROVED.**
   `Mode2RansDecoderActualWord` and `Mode2RansDecoderGeneratedStep` connect the
   actual `x & 1023` lookup, packed halfword selection, literal mode-2
   `symbol_words`/`dsyms_words`, and W32 arithmetic to the expected pure
   decoder transition without a table axiom.
3. **Actual 0/1/2-byte normalization — PROVED.**
   The nested generated loop maintains exact cursor, replay state, decoded
   prefix, and untouched output tail. Its consuming step reads the precise
   trace segment byte; its no-consume exit establishes the next state/cursor
   boundary.
4. **Whole generated decoder — PROVED as exact-trace partial correctness.**
   `actual_rans_decode_trace_refinement` directly targets
   `RansDecodeTarget.M._rans_decode`. Exact canonical trace input implies
   returned `bad=0`, consumed offset `encoded_size`, recovery of all 1024
   symbols, and `[1024,2048)` frame. The internal `x=2^23` fact discharges the
   actual final reject check.
5. **Core inverse — remains PARTIAL.**
   Encoder refinement, actual suffix copy, and decoder refinement now compile
   separately. The missing edge is a single actual-harness consequence that
   converts encoder `segment_matches` plus copy `slice_eq` into the decoder's
   pointwise exact-trace read premise.
6. **Week 13 decision — GO-DECODER.**
   Restrict Week 13 to the actual encoder→copy→decoder harness composition.
   Do not begin the `h` codec or full HBZ wrapper until that theorem compiles.
   Encoder-success reachability and both loop-termination claims remain
   separate and must not be inferred from partial correctness.

## Sprint 13 — single remaining core edge

1. **Copy/trace adapter — PROVED.**
   `copied_suffix_is_exact_trace` composes the actual encoder's
   `segment_matches` with the actual copy helper's `slice_eq`; the copied
   decoder buffer therefore contains the same complete trace at offset zero.
2. **Decoder-read constructor — PROVED.**
   `segment_matches_implies_exact_decoder_segment_input` derives every Week 12
   pointwise normalization-byte read from that one global segment relation.
   `actual_decoder_input_from_configured_trace` adds canonical input, exact
   size bounds, and the actual `(1024,size,13)` state fields without assuming
   decoder success.
3. **W64/int size bridge — PROVED.**
   `encoder_success_size_word_bridge` uses the actual encoder offset bound to
   prove that the harness's modular `1024-off` word is exactly the integer
   trace length, with no wraparound.
4. **Actual harness core inverse — PROVED as success-conditioned partial
   correctness.**
   `actual_rans_encode_copy_decode_inverse` calls the three existing actual
   top-level theorems in execution order. Encoder failure skips the decoder
   and preserves the initialized result. Encoder success implies decoder
   `bad=0`, exact `off=size`, recovery of all 1024 symbols, and output-tail
   frame. Success is not a precondition.
5. **Reachability/termination — still PARTIAL.**
   The theorem does not prove that the actual encoder succeeds or that either
   loop terminates. `OBL-RANS-ACTUAL-SUCCESS-WITNESS` remains separate.
6. **Week 14 decision — GO-HBZ.**
   Restrict Week 14 to the success-conditioned production full-HBZ boundary:
   `signature_pack_unpack_hbz_full_actual_exact` /
   `signature_pack_unpack_hbz_full_inverse_mode2` compose actual
   `_encode_hb_z1_full`/`_decode_hb_z1_full` with the proved prepare/apply
   inverse and rANS core inverse. The fixed all-6 success witness now
   compiles, and the `h` codec stays out of scope until Week 16.
7. **Week 15 decision — GO-WITNESS.**
   `Mode2RansActualSuccessWitness.actual_rans_encode_all_six_success` closes
   the fixed all-6 witness, and the HBZ lift
   `actual_hbz_full_encode_decode_zero_success_mode2` /
   `signature_pack_unpack_hbz_zero_success_mode2` carries it through the
   actual wrapper boundary. `OBL-RANS-ACTUAL-SUCCESS-WITNESS` is now PROVED as
   fixed-input Hoare partial correctness.
8. **Week 16 first-task decision — narrowed to the KeyGen snapshot leaf.**
   The active Week 16 result is the transparent two-call KeyGen snapshot
   harness. `Mode2KeygenCoreEquation.actual_m23_matrix_finalize_semantic_snapshot`
   compiles after the rename to the mod-2q zero predicate. The faithful
   `KG-1`, `KG-3`, and paper `A s = q j (mod 2q)` claims remain blocked on
   the missing `output_row` / full-NTT-to-`Agen*sgen` multiplication bridge.
   `OBL-SIG-H-ENCODE-DECODE` stays deferred; the Sign, Verify, and
   composition lanes remain planned, not claimed.
9. **KG-NTT-MUL continuation decision — STOP-KG-NTT.**
   The actual forward-NTT, pointwise-accumulation, and inverse-NTT procedure
   leaves are already checked, and `Mode2KeygenNttMulBridge` fresh-compiles
   their last `output_row` representation rewrite plus its consequence for
   both active rows of the direct matrix/finalizer harness. The checked tree has no
   odd-root orthogonality/full-NTT convolution theorem and no `Rq.poly` to
   HAETAE integer-list multiplication adapter.  KeyGen is frozen at the
   KG-2/finalization boundary; KG-1, KG-3, complete KG-4, and the paper key
   equation are not claimed.  The active lane moves to MINCORE-SIGN.
10. **MINCORE-SIGN decision — STOP-SIGN-CHAL-MODE2.**
    `Mode2SignAcceptedCore` now fresh-compiles a focused harness that directly
    calls `_sf_round_challenge_mode2`, `_sf_z_check`, and the accepted-only
    `_sf_hint_mode2`; its checked control theorem assumes neither rejection
    success nor a target equation.  The first Sign-specific absent semantic
    leaf is `sf_challenge_mode2_highbits_lsb_sampleinball_correct`.  The
    paper-level S-1/S-4 paths also retain the frozen full-NTT convolution
    dependency.  No response, norm, hint, distribution, or termination claim
    is made.  The active lane moves to MINCORE-VERIFY.
11. **MINCORE-VERIFY decision — PARTIAL-VERIFY-MATRIX-CRT.**
    The focused Verify harness calls `_verify_prepare_z1_wprime`,
    `_verify_matrix_crt`, `_sign_verify_recover_w_z2`,
    `_sign_verify_norm_reject`, and the norm-gated `_sign_verify_tail_m23`
    directly and in order.  The checked surface preserves machine-word V-1,
    V-2, V-5, V-6, the W64 norm result, the exact tail trace, and the actual
    mismatch word expression.  The first absent reconstruction theorem is
    `verify_matrix_crt_mode2_fromcrt_freeze_exact`; paper V-3/V-4 therefore
    remain unproved.  V-6 integer centering, norm no-wrap, and the
    highbits/LSB/mu/SampleInBall challenge bridge also remain explicit
    residuals.  Parser, malformed input, codec, public API, KeyGen NTT
    expansion, Sign blockers, distribution, and termination stay outside the
    frozen Verify result.

## Sprint 16 — seven-day minimum paper lane

1. **First-task status: CONTINUE-KG (`BLOCKED-KG-NTT-MUL`).**  The exact
   actual procedure boundary, direct two-call harness, snapshot low/high
   decomposition, adjusted-`s2` equation, snapshot mod-`2q` identity, and
   frames compile.
2. **Continuation status: STOP-KG-NTT.**  The bridge audit reached the exact
   absent leaf
   `mont(full_invntt(ahat * full_ntt(p) * inv R)) = full_invntt(ahat) &* p`.
   Its required odd-root orthogonality formula is not machine-checked in the
   NTT artifact; the security-model list adapter is also absent.
3. **Frozen KeyGen scope:** retain KG-2 and actual finalization semantics only.
   Do not substitute the snapshot-only identity for KG-1, KG-3, complete KG-4,
   or the paper `A s = q j (mod 2q)` theorem.
4. **Sign status: STOP-SIGN-CHAL-MODE2.**  The direct actual helper harness and
   accepted-branch control theorem compile, but the exact full
   highbits/LSB/mu-to-SampleInBall semantics leaf is absent.  S-1/S-4 also
   retain the frozen full-NTT convolution dependency, so S-1--S-7 are not
   claimed.
5. **Verify status: PARTIAL-VERIFY-MATRIX-CRT.**  The exact actual-call order
   and helper-local word semantics compile without desired-result premises.
   The full predicate theorem is not authored because the matrix CRT/freeze
   semantics leaf is absent; downstream V-6 integer, norm no-wrap, and
   challenge-semantic leaves remain named rather than assumed.
6. Keep sampler distributions, retry termination, packers, public APIs,
   parser/codec paths, and general NTT algebra outside the frozen Verify
   target.  Any continuation begins with the named matrix leaf and must again
   pass individual and aggregate fresh compilation and independent audit.

The exact schedule, fallback boundary, non-claims, and completion gates are in
`WEEK16_MINCORE_PLAN.md`.
