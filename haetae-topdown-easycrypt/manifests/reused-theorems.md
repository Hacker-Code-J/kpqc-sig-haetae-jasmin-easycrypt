# Reused theorem manifest

Paper-freeze scope is canonicalized in `manifests/paper-artifacts.md`.
Everything below is a leaf-level reuse record: imported `PROVED` theorems do
not establish the partial or blocked `PAPER-KG`, `PAPER-SIGN`,
`PAPER-VERIFY`, or `PAPER-SIGN-VERIFY` parents.

No source was copied.  Direct reuse is through
`easycrypt/refinement/keygen/ExistingFirstAttemptAdapter.ec`.  Its imported
source is pinned at SHA-256
`1f52619a0249bffef2640acaa32ea26283515206545978b196cea89ab80dc2bf`.

## Directly imported results

### `TargetKeygenM23FullFirstAttempt.mode2_full_first_attempt_equiv`

Exact proposition:

```easycrypt
equiv [Parent._keypair_full_m23 ~ Mode2FullFirstAttempt.run :
  vkp{1}=vkp{2} /\ skp{1}=skp{2} /\ seedp{1}=seedp{2} /\
  k{1}=2 /\ m{1}=3 /\ vkbytes{1}=992 /\
  best_count{1}=5 /\ tau{1}=58 /\ rem{1}=24 /\
  singular_bound{1}=611098
  ==> res{1}=res{2}.`1]
```

New use: `imported_mode2_full_first_attempt_equiv`.  Boundary: the observer
peels and records the first attempt but retains the remaining tail; equality of
returned packed buffers does not prove the paper distribution, termination,
or packing semantics.

### `mode2_full_first_attempt_fft_inputs_bound2_correct`

Exact proposition:

```easycrypt
hoare [Mode2FullFirstAttempt.run : seedp=seed0 ==>
  first_attempt_snapshot_facts seed0 res.`2 /\
  first_attempt_trace_fft_inputs_bound2 res.`2]
```

New use: `imported_mode2_first_attempt_fft_inputs_bound2`.  Boundary: an input
bound is not a fixed-point error theorem or a numerical tail probability.

### `mode2_full_first_attempt_score_guard_correct`

Exact proposition:

```easycrypt
hoare [Mode2FullFirstAttempt.run : seedp=seed0 ==>
  first_attempt_snapshot_facts seed0 res.`2 /\
  (first_attempt_trace_accepted res.`2 <=>
   first_attempt_trace_score_within_bound res.`2)]
```

New use: `imported_mode2_first_attempt_score_guard`.  Boundary: this is the
implementation score/guard relation, not equality to an analytic singularity
predicate under rounding or ties.

### `mode2_full_first_attempt_accepted_correct`

Exact proposition:

```easycrypt
hoare [Mode2FullFirstAttempt.run : seedp=seed0 ==>
  first_attempt_trace_accepted res.`2 =>
    first_attempt_snapshot_facts seed0 res.`2 /\
    first_attempt_trace_guard res.`2]
```

New use: `imported_mode2_first_attempt_accepted`.  Boundary: conditional on
first-attempt acceptance; no probability or later-attempt claim.

## Inspected transitive foundations

- `TargetKeygenMode2ParentComposition.checked_mode2_parent_sampler_prefix_correct`
  (source hash `7230adac...bf54`) gives exact seed expansion, matrix/vector
  streams/ranges/frames, eta streams/centering/frames, and retry counter 5 for
  the checked prefix wrapper.  It is a deterministic stream theorem, not a
  sampler distribution theorem.  Its losslessness companion requires the
  explicit `mode2_sampler_prefix_progress` premise.
- `TargetKeygenM23FinalizeComposition.checked_mode2_parent_m23_finalize_correct`
  (source hash `89a50cd...415d`) composes sampler facts, M23 facts, and
  `KeygenM23FinalizeSpec.finalize_output` for the proof wrapper.  It does not
  cover singular rejection, retry control, or packing.
- `TargetNTTRefinement.target_poly_ntt_correct` and
  `target_poly_invntt_correct18` (source hash `197b0fef...4de8`) establish
  bounded-array representations of the mathematical full NTT/inverse NTT for
  target procedures.  Mode-2 M23 composition imports these through the pinned
  current `hpoly.jazz` extraction; this is not a theorem about every API NTT
  call or public-key layout.

The FIPS202 artifact is deliberately not listed as a functional theorem.  Its
current checked result is reproducible extraction/compilation of one-shot
wrappers, and the specialized KeyGen/Sign/Verify paths do not call those
wrappers directly.

## Week 16 direct M23/finalizer harness boundary

`Mode2KeygenCoreEquation.ec` and `Mode2KeygenSnapshotAlgebra.ec` are authored
locally. No source was copied.

- `Mode2KeygenCoreEquation.ec` SHA-256:
  `6f1cd6f8bae4d3228280da9fe044f9106ac803b3ad6a27347432904b66912d9f`.
- `Mode2KeygenSnapshotAlgebra.ec` SHA-256:
  `d86ecbbcf338f0916ee28131e3adaef1ae534d54a4ba6c74d83933e0c244dbe4`.

- `Mode2KeygenCoreEquation.actual_m23_matrix_finalize_snapshot` directly reuses
  `TargetKeygenM23Arithmetic.kp_m23_matrix_mode2_arithmetic_correct` and
  `TargetKeygenM23Finalize.keypair_finalize_m23_mode2_correct` through a
  transparent two-call harness over the generated parent procedures
  `_kp_m23_matrix` and `_keypair_finalize_m23`.
- The harness snapshots the pre-finalization `bp` array and returns only
  `(pre_bp, s1hat, final_bp, adjusted_s2)`. Its Hoare precondition uses the
  actual matrix/finalizer range premises only; it does not assume desired
  key-generation equations, acceptance, retry success, packing, or public-API
  caller facts.
- `Mode2KeygenSnapshotAlgebra.ec` records the local low/high decomposition
  algebra induced by the finalizer residue. The core theory defines the
  `actual_snapshot_mod2q_zero` predicate and proves it from finalizer semantics
  with `finalize_semantic_output_snapshot_mod2q_zero`. This is a pointwise
  arithmetic hook, not a proof that the transparent harness already
  establishes the full `(KG-1)` to `(KG-4)` equation package.

Current blocker hook: the direct harness stops at exact extracted helper
semantics. The faithful `(KG-1)`, `(KG-3)`, and paper `A s = q j (mod 2q)`
claims need a theorem identifying `KeygenM23ArithmeticSpec.output_row`---the
checked full-NTT/pointwise/inverse-NTT representation---with the security
model's `Agen * sgen` polynomial product. Retry and acceptance remain deferred,
not premises or substitutes for that missing bridge.

### KG-NTT-MUL continuation and stop boundary

`Mode2KeygenNttMulBridge.ec` is an authored boundary file. It reuses
`KeygenM23ArithmeticSpec.pointwise_row_words_ntt` to fresh-compile the exact
rewrite
`output_row = array256_mont(full_invntt(pointwise_row_words ...))` and its
representation transport. Its `actual_m23_matrix_snapshot_rows_explicit`
corollary weakens the already-compiled direct two-call snapshot theorem to
that explicit representation for both active rows. It does not copy an actual
loop proof or import the desired product as a predicate or assumption. The
authored file SHA-256 is
`cc9c645b58fc8c1165982f3053b62148e690e5de7b72c1c5bf4ad214dfd7c2eb`.

The continuation audited the checked NTT leaves
`NTTFullAlgebra.ntt_full_ntt` and `invntt_full_invntt` and the actual
pointwise/inverse parent refinements. The first absent mathematical leaf is
the odd-root orthogonality/full-NTT spectral action
`mont(full_invntt(ahat * full_ntt(p) * inv R)) = full_invntt(ahat) Rq.&* p`.
A subsequent adapter from `Rq.poly` arrays to
`HAETAE_Algebra.poly_mul` integer lists is also absent. Neither result is
treated as reused, trusted, or assumed. Final status is `STOP-KG-NTT`; KeyGen
is frozen at KG-2/finalization. The later Sign pass is separately frozen at
`STOP-SIGN-CHAL-MODE2`; the subsequent Verify pass is frozen at
`STOP-VERIFY-MATRIX-CRT`.

## MINCORE-SIGN actual-call boundary

The generated `SignAcceptedCoreTarget.M` module is not trusted for a paper
postcondition. The authored `Mode2SignAcceptedCore` file opens its three
selected procedures directly and proves only
`actual_sign_accepted_core_branch_control_mode2`. No theorem is reused for
the absent highbits/LSB/mu-to-SampleInBall semantics. In particular, the
current abstract `challenge_hash`, which omits highbits, is not treated as a
valid replacement. The exact non-reused leaf and the response/norm/hint
non-claims are recorded in `WEEK16_SIGN_REPORT.md`.

## MINCORE-VERIFY actual-call boundary

The generated `VerifyCoreTarget.M` procedures are opened directly by four
authored theories; no paper-level Verify theorem is imported or assumed.
`ActualVerifyCoreSequence.run` calls `_verify_prepare_z1_wprime`,
`_verify_matrix_crt`, `_sign_verify_recover_w_z2`,
`_sign_verify_norm_reject`, and the norm-gated `_sign_verify_tail_m23` in
program order. The helper-local proofs establish exact machine-word V-1,
V-2, V-5, V-6, W64 norm semantics, exact tail trace, and the actual
`_poly_mismatch` word expression.

No reused theorem identifies `_verify_matrix_crt` with the paper V-3/V-4
reconstruction. The absent headline
`verify_matrix_crt_mode2_fromcrt_freeze_exact` requires the non-reused
`verify_matrix_ntt_acc_mode2_cols4_correct` and
`verify_crt_freeze_mode2_word_exact` leaves.  The NTT leaf cannot reuse the
KeyGen-only 2-by-3 interface and first lacks `rq_mul_coeff_foldr_to_bigi`,
followed by full-NTT Montgomery spectral action and odd-root orthogonality.
Likewise,
no theorem is reused for the V-6 word/integer centering bridge, W64 norm
no-wrap, or highbits/LSB/mu/SampleInBall semantics. These are neither trusted
facts nor representation premises. Final status and non-claims are recorded
in `WEEK16_VERIFY_REPORT.md` as `STOP-VERIFY-MATRIX-CRT`.

## Week 2 generated-procedure boundary

`ExtractedPackedKeyPrefix.ec` imports generated procedures from
`KeygenMode2ParentTarget.ec`, source SHA-256
`248f8157e348e3f294665d12573a58ee58e860884356bfe82324fda64de5d0b4`.
No theorem about packing is assumed from that file: the new Hoare proofs open
the generated `_pack_vec_eta_to`, `_pack_vec2_eta_to`, `_pack_sk_m23`,
`_keypair_full_m23`, and mode-2 internal procedures themselves.

The focused packer-only extraction is independently regenerated and hashed in
`generated-extractions.sha256`. The broader parent target is used solely
because the focused target intentionally omits the KeyGen caller needed for the
return-value lift.

## Week 2 directly reused byte-order lemmas

Source:
`haetae-ref-easycrypt/easycrypt/spec/KeygenShakeStreamSpec.ec`, SHA-256
`a07ebbd78de3dca5c53bd47617044b5d4529448b3cf64651d49ba3e9e662a97f`.

### `KeygenShakeStreamSpec.drop_bytes0`

Exact proposition:

```easycrypt
lemma drop_bytes0 w : drop_bytes w 0 = w.
```

New use: initializes the word-to-byte invariant in
`ExtractedMuHashPrefix.sign_verify_final_squeeze_mu32_prefix`.

### `KeygenShakeStreamSpec.drop_bytes_succ`

Exact proposition:

```easycrypt
lemma drop_bytes_succ w count :
  0 <= count =>
  drop_bytes w (count + 1) =
    drop_bytes w count `>>` (W8.of_int 8).
```

New use: advances the little-endian byte cursor through each Sign-side 64-bit
lane. The premise `0 <= count` is discharged by the inner squeeze-loop
invariant.

### `KeygenShakeStreamSpec.rate_lane_byte_get8`

Exact proposition:

```easycrypt
lemma rate_lane_byte_get8 state lane byte :
  0 <= lane < 25 =>
  0 <= byte < 8 =>
  rate_lane_byte state lane byte =
    BArray200.get8 state (8 * lane + byte).
```

New use: relates the Sign word-oriented `BArray64.set64d` squeeze to Verify's
byte-oriented `BArray32.set8` squeeze. Both range premises are proved from the
actual generated loop counters.

These lemmas express array/word byte order; they do not assert that an abstract
SHAKE output prefix exists. Permutation equality, finalize equality, and both
squeeze loops are proved over the generated procedures. The imported
`HAETAE_Keccak1600.ec` dependency is pinned at SHA-256
`c82f41322660cacb41306c47f1f93773b487e45e7947e7430231075104e895ec`
and remains part of the imported specification/TCB boundary.

## Week 2 local composition

The remaining Week 2 results are authored locally:

- `ExtractedPackedKeyPrefix.ec`
- `ExtractedMuHashPrefix.ec`
- `Mode2KeyMemoryBridge.ec`
- `Mode2MuChallengeComposition.ec`

No source was copied and no imported theorem was weakened. In particular, no
SHAKE-prefix axiom or implementation-semantic axiom was introduced.

## Week 3 locally reused theorem boundary

Week 3 reuses two Week 1/2 authored theorems by import; it does not treat the
local wrappers as the final implementation claim.

### `ExtractedMuHashPrefix.sign_verify_raw_mu_top_wrappers_prefix`

Source SHA-256:
`3ba2bfd1dbd1c00da6a03db2a93786a7d8f34cf0cae32f506698ac8d4999bf77`.

Exact proposition (with the displayed no-wrap premise):

```easycrypt
equiv [SignRawMuTop.run ~ VerifyRawMuTop.run :
  ={Glob.mem} /\ skp{1}=sk0 /\ Glob.mem{2}=mem0 /\ vkp{2}=base /\
  preaddr{1}=prep{2} /\ prelen{1}=prelen{2} /\
  maddr{1}=mp{2} /\ mlen{1}=mlen{2} /\
  sk_memory_prefix sk0 mem0 base
  ==> mu32_prefix res{1} res{2}]
```

New use: the middle leg of
`ExactMuTopControl.sign_verify_generated_raw_mu_prefix`. The two outer legs
are newly proved exact adapters for the generated Sign and Verify procedures;
therefore the wrapper is not the conclusion boundary.

### `ExtractedChallengeAbsorb.sign_verify_mu32_absorb_from_pos64`

Source SHA-256:
`dcfccd9d4f39635d7648e1d4d81e85858de45b80fec0684988b68c74af64fe36`.

Exact proposition:

```easycrypt
equiv [Sign.__sign_challenge_shake256_absorb_mu32 ~
       Verify.__verify_shake256_absorb_mu32 :
  ={sp_0,statep} /\
  BArray16.get64 statep{1} 0 = W64.of_int 64 /\
  mu32_prefix inp{1} inp{2}
  ==> ={res}]
```

New use: the second call in
`ExactMode2RawMuComposition.generated_raw_mu_to_challenge_suffix_zero_loss`,
after the actual generated hash procedures establish its `mu32_prefix`
premise. It says nothing about highbits/LSB, challenge sampling, or the whole
Sign/Verify API.

## Week 3 API copy-helper boundary

`ApiKeyMemoryBridge.ec` does not import an upstream theorem about copying. It
opens the freshly generated `KeygenApiCopyTarget`, `SignApiCopyTarget`, and
`VerifyApiCopyTarget` procedures and proves their loop invariants locally.
The only reused authored relations are `PackedKeyPrefix.vk_prefix_eq` and
`ExtractedMuHashPrefix.sk_memory_prefix`; neither supplies API pointer
validity, frame preservation, or caller reachability.

Accordingly, the isolated helper theorems are new proof evidence, while the
sequential public-call chain remains the named
`OBL-API-KEY-MEMORY-RAW` obligation. No imported memory axiom or copy
correctness assumption is used.

## Week 4 local reuse and extraction-identity boundary

No existing source or theorem was copied. The Week 4 theories import and
compose the following already-authored results without weakening them:

- `ExtractedPackedKeyPrefix.keypair_internal_mode2_return_prefix`: every
  terminating mode-2 internal KeyGen call returns arrays satisfying
  `vk_prefix_eq sk vk 992`; it is reused by
  `RawApiKeygenExportComposition.raw_keypair_internal_mode2_return_prefix`.
- `ApiKeyMemoryBridge.keygen_export_vk_mode2_prefix` and
  `keygen_export_sk_mode2_prefix_frames_vk`: the generated 992/1408-byte copy
  procedures establish their prefix postconditions, and the second write
  preserves the first region under the displayed disjointness premise.
- `ApiKeyMemoryBridge.imported_sign_sk_reaches_mu_memory`: an imported Sign SK
  prefix and external VK/SK byte agreement imply the exact
  `ExtractedMuHashPrefix.sk_memory_prefix` premise.
- `ExactMuTopControl.sign_verify_generated_raw_mu_prefix`: once the memory,
  raw-branch, pointer and length premises are supplied, the actual generated
  hash procedures return `mu32_prefix`-related outputs.
- `ExactMode2RawMuComposition.generated_raw_mu_to_challenge_suffix_zero_loss`:
  the prior generated hash result composes with the position-64 challenge
  suffix absorb. Week 4 does not strengthen this into a public-caller theorem.

`RawApiMuReachability.raw_sign_hash_extraction_identity` and
`raw_verify_hash_extraction_identity` fresh-compile exact pRHL equivalences
between procedures generated by the Week 4 raw-ABI closure and the Week 2/3
focused hash closure. This is the formal interchange evidence; equal procedure
names or common source hashes alone are not used as proof.

The Week 4 residual names were proof obligations, not axioms.  Week 5 removes
those boolean placeholders from the authored targets and replaces them with
the compiled Hoare/equivalence results recorded below.

## Week 5 local theorem reuse

No external source or theorem was copied in Week 5.  The new theories reuse
previously authored, fresh-compiled local results by import.  These imports do
not change their premises.

### `RawApiKeygenExportComposition.keypair_raw_api_exact_export_trace`

Source SHA-256:
`7ecc30df82313e7c5b90a6586e016b9b345d7e2e67d5769aff8cc41956bb1337`.

Exact proposition:

```easycrypt
equiv [Raw.cryptolab_haetae_mode2_keypair_internal ~
       RawKeygenExportTrace.run :
  ={Glob.mem, vku, sku, seedu} ==> ={Glob.mem, res}]
```

New use: transfers
`RawApiKeygenSequentialExport.keypair_raw_api_trace_exports_matching_prefixes`
to the actual raw KeyGen caller.  The transferred result is partial
correctness and retains the valid/canonical/disjoint-region premises.

### `RawApiCallerMuTrace.sign_raw_api_exact_mu_trace`

Source SHA-256:
`9d89f42deee9af588215830ad94251b134403cb406468d864d77bebb71046ab1`.

Exact proposition:

```easycrypt
equiv [Sign.cryptolab_haetae_mode2_signature_internal ~
       SignRawApiMuTrace.run :
  ={Glob.mem, sigu, siglenu, mu, mlen, preu, prelen, rndu, sku}
  ==> ={Glob.mem, res}]
```

New use: exposes imported SK and actual raw hash-call arguments while
preserving the complete Sign continuation, final result, and final memory.
It does not prove that the Sign output buffer is disjoint from or frames the
key regions across separate API calls.

### `RawApiVerifyMuTrace.verify_raw_api_exact_mu_trace` and
`verify_cryptolab_exact_mu_trace`

Source SHA-256:
`4edff0fcd24cc10d0836a8c2917b291043a939cd86ecb3838548cd1793ddffae`.

Exact propositions:

```easycrypt
equiv [Verify._api_verify_mode2_raw ~ VerifyRawApiMuTrace.run :
  ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
  ==> ={Glob.mem, res}]

equiv [Verify.cryptolab_haetae_mode2_verify_internal ~
       VerifyCryptolabMuTrace.run :
  ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
  ==> ={Glob.mem, res}]
```

New use: transports the unary `accept => tail_reached` and accepted
descriptor-binding Hoare facts to both actual Verify callers.  No precondition
requires `tail_reached`; early-reject branches remain in the mirrors and leave
the observation fields guarded.

### Generated mu and suffix relations

`ExactMuTopControl.sign_verify_generated_raw_mu_prefix` is imported from
source SHA-256
`780508523c62271eed9772a9e46de35999ffc9818a07da3251068283a58adf6d`.
It is reused by
`RawApiAcceptedMuComposition.generated_hash_calls_mu_zero_loss_from_raw_api_regions`
after the external-buffer and imported-prefix premises are discharged.  Its
programs remain the actual generated `_sf_mu_rawpre` and
`__verify_hash_mu`; it does not compare caller trace globals.

`ExactMode2RawMuComposition.generated_raw_mu_to_challenge_suffix_zero_loss`
is imported from source SHA-256
`11952798a8f7aa8ee3d9fc5c21ea3bd5c37e15a496cc6cba71b33540b7031eb7`.
It is reused at position 64 by the Week 5 generated suffix adapter.  The
premise includes an explicit common challenge state/position; actual Sign-core
and Verify-tail challenge-entry state, highbits, and LSB bytes are not supplied
by this theorem.

The Week 5 parent boundary is therefore intentionally **PARTIAL**.  The
remaining missing results are a direct accepted theorem over both caller
traces' stored `observed_mu` values and a Sign-output key-region frame/stability
theorem.  Neither is encoded as an assumption or boolean placeholder.

## Week 6 local theorem reuse

No external theorem or source is copied in Week 6. The new targets reuse the
following previously authored results by import, with their premises intact.

### `RawApiCallerMuTrace.sign_raw_api_exact_mu_trace`

Source SHA-256:
`9d89f42deee9af588215830ad94251b134403cb406468d864d77bebb71046ab1`.

Exact proposition:

```easycrypt
equiv [Sign.cryptolab_haetae_mode2_signature_internal ~
       SignRawApiMuTrace.run :
  ={Glob.mem, sigu, siglenu, mu, mlen, preu, prelen, rndu, sku}
  ==> ={Glob.mem, res}]
```

New use: transfers `sign_raw_trace_frames_reused_regions` to the actual Sign
caller and is one leg of `raw_sign_then_verify_actual_exact_trace`. It adds
ghost observations only; result and final memory are identical.

### `RawApiVerifyMuTrace.verify_cryptolab_exact_mu_trace`

Source SHA-256:
`4edff0fcd24cc10d0836a8c2917b291043a939cd86ecb3838548cd1793ddffae`.

Exact proposition:

```easycrypt
equiv [Verify.cryptolab_haetae_mode2_verify_internal ~
       VerifyCryptolabMuTrace.run :
  ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
  ==> ={Glob.mem, res}]
```

New use: the Verify leg of the actual sequential trace. Early rejects are
preserved; observations are used only under `tail_reached`.

### `RawApiVerifyAcceptTrace` accepted-path Hoare results

Source SHA-256:
`84b9f17377c672b7860c0225b94f0315964ea654d2e57c19e825e24d8f73e6cd`.

Reused propositions are
`verify_cryptolab_trace_accept_implies_tail_reached` and
`verify_cryptolab_trace_accept_binds_hash_inputs`. They supply
`accept => tail_reached` and exact VK/pre/message input bindings from the
post-state of the real trace; neither assumes acceptance or a hash observation
in the precondition.

### Week 6 newly authored boundaries

The following hashes identify new proof evidence rather than trusted imports:

- `RawApiSignOutputFrame.ec`:
  `7fb8c18c9b22f1acedc43a2161e077ed344679d9ff7b05bed7a2223357e80c5f`;
- `RegionLocalMuEquivalence.ec`:
  `288b3af0b0de14c4192a50803881cdd5c462e11136f7cd71537c1225011bf32c`;
- `RegionLocalMuTop.ec`:
  `9b783ad5057e6a48b3f1ccb33af51ae5818f1a2dc220d6d9e8b71399eadf2cb4`;
- `RawApiDirectObservedMu.ec`:
  `16bf1be1179e7a512e31d8c4aced23c4bbfc04354bc3babe5142cc5f9fe3a8ab`.

These hashes are audit identifiers, not assumptions. The direct stored-mu
postcondition is absent from the last file and remains a named obligation.

## Week 7 local codec composition

No upstream codec-correctness theorem is reused. The generated pack/unpack
targets contain programs only; all loop invariants below are authored in the
new tree.

`Mode2SignaturePrefixRoundTrip.ec` (SHA-256
`0fa909f9cd3427b239eec2f56747d7f4c7594c4f972babb44eca50c16314a685`)
reuses these two locally authored procedure theorems:

- `Mode2SignaturePrefixPack.pack_sig_prefix_mode2_layout`, source SHA-256
  `865900a6b3a3ac25c7a1582527ea8bbd5529717a66b45307787554cd9709df92`:

```easycrypt
hoare [Pack._pack_sig_prefix :
  cp = cp0 /\ lowp = low0 /\
  lcount = W64.of_int 4 /\ sigbytes = W64.of_int 1474
  ==>
  packed_challenge_prefix res cp0 32 /\
  packed_low_prefix res low0 1024]
```

- `Mode2SignaturePrefixUnpack.unpack_sig_prefix_mode2_layout`, source SHA-256
  `af24e8fa6218624a2df4efa54874ad5437661a7a4a7210b67b304bfe5af97d6f`:

```easycrypt
hoare [Unpack._unpack_sig_prefix :
  cp = cp0 /\ lowp = low0 /\ lcount = W64.of_int 4 /\
  packed_challenge_prefix sigp cpsrc 32 /\
  packed_low_prefix sigp lowsrc 1024
  ==>
  decoded_challenge_prefix res.`1 cpsrc 256 /\
  decoded_low_prefix res.`2 lowsrc 1024 /\
  low_tail_frame low0 res.`2]
```

The resulting `pack_unpack_sig_prefix_mode2_roundtrip` is a partial-correctness
Hoare theorem over a sequential harness that directly calls the two generated
procedures. It requires canonical one-bit challenge words and signed-byte low
coefficients. It does not reuse or assume an rANS inverse, suffix metadata,
padding, norm, or Verify-tail theorem.

## Week 8 HBZ/rANS boundary

No upstream HAETAE or ML-DSA rANS correctness theorem is imported.  The
generated extraction theories contribute programs and literal tables only;
translator soundness remains in the TCB described in `ASSUMPTIONS.md`.

The locally authored reuse chain is:

- `Mode2HbzPrepare.encode_hb_z1_prepare_mode2_correct` and
  `Mode2HbzApply.decode_hb_z1_apply_mode2_correct` feed
  `Mode2HbzLeafRoundTrip.encode_prepare_decode_apply_mode2_inverse`;
- `Mode2HbzTableCertificate.mode2_hbz_table_certificate` is instantiated by
  the generated-but-EasyCrypt-checked
  `Mode2HbzSymbolWordsGenerated.actual_mode2_hbz_tables_certified`;
- `Mode2RansCore.hbz_fast_step_decode_inverse` reuses the concrete reciprocal
  equality from `Mode2HbzTableCertificate`, but remains a pure single-step
  theorem and is not cited as generated-loop refinement;
- `Mode2HbzActualBoundary.pack_target_encode_hb_z1_full_exact_focused` and
  `unpack_target_decode_hb_z1_full_exact_focused` connect the focused wrapper
  extraction to the Week 7 signature extraction by exact program
  equivalence.  They prove identity, not an inverse.

No theorem in this chain supplies actual encoder/decoder normalization-loop
correctness, a full success-conditioned round trip, or a successful actual
witness.  Those premises are not hidden as assumptions.

Week 8 authored-theory SHA-256 identifiers are:

- `Mode2HbzPrepare.ec`: `909e4eed166261d568cf4932b0e5201acac046e614c99b9e73bcb75a2c0d865f`;
- `Mode2HbzApply.ec`: `03ac5595cc6cd6d19e613edd141a1708150025b338f9936d29efcc1d4fe521d4`;
- `Mode2HbzLeafRoundTrip.ec`: `7da906bcd77c7923e52b657a10dd77da7b956556677762b585f8259756b92e55`;
- `Mode2HbzTableCertificate.ec`: `8bdecef8cae26c35a755f1f319824c1f745564cb3732e8a3d9ab87b6e776ad58`;
- `Mode2HbzSymbolWordsGenerated.ec`: `3f664576f56de9243355413fc9149217484817309accacf72c0865e3d3d6ba90`;
- `Mode2HbzActualBoundary.ec`: `6efb58b5f65b8ae21e00c3ba3dbac21cadb1bd28e937b4ac72daaf480d05ba80`;
- `Mode2RansCore.ec`: `a4a10f5586e3d4b495e68ce0f487124a1925dfb738ad48c1f26ca8e771a5838c`.

## Week 9 reuse and authored boundary

Week 9 reuses the Week 8 results above without modifying or re-proving them.
The direct dependencies are:

- `Mode2HbzTableCertificate.hbz_frequency_positive`,
  `hbz_fast_step_matches_math`, and `hbz_fast_step_w32_range` in the pure
  trace state-bound proof;
- `Mode2RansCore.hbz_encoded_slot_selects_symbol` and
  `hbz_fast_step_decode_inverse` in the trace-head symbol/inverse lemmas;
- the exact focused targets pinned by
  `Mode2HbzActualBoundary` as the generated programs used by the actual
  encoder/copy/decoder harness.

No reused theorem supplies an actual normalization-loop invariant, generated
decoder success, or an actual successful encoder witness.

Week 9 authored-theory SHA-256 identifiers are:

- `Mode2RansByteStack.ec`:
  `e76063db635ef4529fec978b634ceef5e8fcafd93ef357312d2d33a6a3262123`;
- `Mode2RansNormalization.ec`:
  `9d9be0597c0f06d4fdef004932563239ddcedb65b2ae007a247caa32aa0ec825`;
- `Mode2RansSuffixCopy.ec`:
  `160cdc828271a08cc3648d7ebbea96d85aa118732776e5863f6a392044d70121`;
- `Mode2RansEncodeRefinement.ec`:
  `0746f1d7479d35f5c365f52a8076dd21135cc4455ee02f02341585d3dad18055`;
- `Mode2RansDecodeRefinement.ec`:
  `afd862483fc592030a072e480639a7cbdabccbe7f9e823fe405ef5644d3b9372`;
- `Mode2RansActualInverse.ec`:
  `c0925456cdfee7657e9aa2ebf0861e7e88d61903241868ea9c0cbeaa96e838a1`.

These are audit identifiers for locally authored proof evidence, not trusted
assumptions. The `Mode2RansActualInverse` filename denotes the target boundary;
the compiled theorem inside proves harness control only, and the core inverse
claim remains `PARTIAL` in the ledger.

## Week 10 encoder reuse and authored boundary

Week 10 reuses, without modification:

- `Mode2RansByteStack.encode_trace_state_bounds`,
  `normalized_fast_step_state_bounds`, and the normalization-byte trace;
- `Mode2RansNormalization.encoder_shift8_uint`,
  `encoder_low_byte_uint`, and `cursor_decrement_no_underflow`;
- `Mode2HbzTableCertificate.actual_mode2_esym_word_fields` and the concrete
  reciprocal/table arithmetic certificate;
- `Mode2RansEncodeRefinement.mode2_hbz_symbol_stream` and the direct generated
  encoder target pinned by the focused extraction.

No reused theorem supplies the missing whole actual suffix equality, actual
success reachability, termination, or decoder correctness.  The new authored
SHA-256 audit identifiers are:

- `Mode2RansArrayListBridge.ec`:
  `33abcc13d286d82aee895b8c2510284f27d1cfd55c4736e515921e2be950b2c2`;
- `Mode2RansEncoderWordStep.ec`:
  `3fbcf5fe32e8b6babf7e5230de3b53f2f570601b0818e81f6421edd519e2e3a1`;
- `Mode2RansEncoderInnerProgress.ec`:
  `91fd25bd355075ef8dac6498fa63b96dccf75d13134ac007ea778fdae66cae9f`;
- `Mode2RansEncoderSerialization.ec`:
  `0a3eab7cb7df6fdc17c672a320a4ac1b18a91f9fdb402a8e5d48731a1e9936b8`;
- `Mode2RansEncoderTrace.ec`:
  `23c008e8bccc18fcd57ad2f426a3edfd501cd87e436059a0eff131bb308d7418`;
- `Mode2RansEncoderActualInner.ec`:
  `4a30ba534d7474c54641b3e681a01597a889e2f178a90ab409b7ce5b5d2a5450`.

These hashes identify authored evidence; EasyCrypt fresh compilation, not the
hashes, establishes the theorem claims.

## Week 11 encoder trace-closure boundary

Week 11 reuses the Week 9/10 pure trace, normalization, array/list and concrete
table/word results without modifying them. The direct implementation theorem
uses in particular:

- `encode_trace_suffix_extension` and the symbol-suffix recurrence;
- `renorm_len_le2`, normalized-state bounds and byte readback;
- the concrete mode-2 esym field certificate;
- Week 10 W32/W64 cursor, byte and serialization leaves.

None of those reused results supplies encoder success, termination, decoder
correctness, or an existential trace. The new authored boundary closes only
the generated encoder's success-conditioned output refinement. Audit hashes:

- `Mode2RansEncoderTailInvariant.ec`:
  `973ebcd0f77b85e2194d96005057fc33861bf1a14b769c57bcd9882636dd17e0`;
- `Mode2RansEncoderGeneratedWordStep.ec`:
  `3b480e67c83dae2312f8ec8d2c30e408803eee57f72e536f4974c315983a78b7`;
- `Mode2RansEncoderSerializationComposition.ec`:
  `a92ba351afa046df025a2eb4c439ed5fd831ec2f804b620405bf614aa2612e30`;
- `Mode2RansEncoderFinalization.ec`:
  `f7f6e65ffd6c7b78c2b4fd066df8220d248e6b1b84d39a5403e96f88dd3df9e3`;
- `Mode2RansEncoderGeneratedFinalization.ec`:
  `4ec8f9ddd1ba146970358aa6df70d2e91830963043c68c0a3be627582b36cc86`;
- `Mode2RansEncoderActualTraceClosure.ec`:
  `b816d2c8bdd5b1a9228e6ee234134c4fed4c1d99e388a4ac18d3a60d9ec3c0bd`;
- `Mode2RansEncoderOuterRefinement.ec`:
  `0b968acff729756eebfc2e47b41e1338a86f6e92932e4900648cbcaff09a0fc6`.

The hashes are identifiers only. The evidence is the fresh `-no-eco`
compilation of `actual_rans_encode_trace_closure` and
`actual_rans_encode_trace_refinement` against the pinned generated target.

## Week 12 decoder reuse and authored boundary

Week 12 reuses, without modifying or re-proving:

- `Mode2RansByteStack` definitions `encode_trace`, `trace_states`,
  `trace_segments`, `trace_cuts`, and `trace_bytes`, together with state bounds
  and normalization-byte readback;
- `Mode2RansArrayListBridge.symbol_list_of_array`, `symbol_suffix`,
  `segment_matches`, and decoded-array frame algebra;
- the concrete mode-2 `symbol_words`/`dsyms_words` certificate from
  `Mode2HbzTableCertificate` and `Mode2HbzSymbolWordsGenerated`;
- Week 9/10 W32 append, mask/shift and cursor arithmetic lemmas;
- Week 11 `actual_rans_encode_trace_refinement` and the existing
  `copy_encoded_suffix_correct` only as downstream composition inputs.

No reused theorem supplies decoder success, decoded-symbol equality, exact
consumption, or termination. Those semantic conclusions are proved directly
over the pinned generated `_rans_decode` body. Week 12 authored-theory SHA-256
identifiers are:

- `Mode2RansDecoderCursor.ec`:
  `37960c0ecc5c422abf106f6a4c812c26e719efe70f96fe188afd5e41f1591ecc`;
- `Mode2RansDecoderWordStep.ec`:
  `ca33dee90c36521ef2402c8a37d248da653b1fc42c84848181ffffb8c875bfed`;
- `Mode2RansDecoderNormalization.ec`:
  `bebaad5b79313e963bafe3476753ae039137b38766f3b2ad8aac5df16d0a515d`;
- `Mode2RansDecoderActualWord.ec`:
  `aa257e594b01ca04ce7926529d4c785b796214a7d50169d44ef58af75dde91b7`;
- `Mode2RansDecoderGeneratedStep.ec`:
  `e41a727270b3c3b52b1c1fd091736958a1a30bd4432224ddbcfb95cf3a63a321`;
- `Mode2RansDecoderCursorSteps.ec`:
  `dd59c980fce97c16456dbf36016d4db3e1270277c6518fd054440204f1ddd284`;
- `Mode2RansDecoderActualTrace.ec`:
  `41b319e0a3ec2eecfb8f05d46a4cc4a6327851938f988054fb48a1f473a9441f`;
- `Mode2RansDecoderTopHoare.ec`:
  `74752f9c3897d7770698e074ebbf74ab9858d25bc76cbc17a11e64bae86709b8`.

These hashes are audit identifiers only. The evidence is fresh `-no-eco`
compilation of `actual_rans_decode_trace_refinement` against the pinned
`RansDecodeTarget.ec`. The encoder→copy→decoder harness composition is not
included in this boundary and remains `PARTIAL`.

## Week 13 core-composition reuse and authored boundary

Week 13 reuses exactly three direct implementation theorems without weakening
their premises:

### `Mode2RansEncoderOuterRefinement.actual_rans_encode_trace_refinement`

On actual generated encoder return, it proves the failure disjunct or, on
success, the exact actual-symbol `trace_bytes` segment, offset/length equation,
and initial-prefix frame. It does not prove success reachability or
termination. Source SHA-256:
`0b968acff729756eebfc2e47b41e1338a86f6e92932e4900648cbcaff09a0fc6`.

### `Mode2RansSuffixCopy.copy_encoded_suffix_correct`

For explicit non-wrapping offset and length, the actual generated
`__copy_encoded_suffix` establishes `slice_eq` and the output tail frame. It
does not assert that its source slice is a trace. Source SHA-256:
`160cdc828271a08cc3648d7ebbea96d85aa118732776e5863f6a392044d70121`.

### `Mode2RansDecoderTopHoare.actual_rans_decode_trace_refinement`

For `actual_mode2_decoder_trace_input`, the actual generated decoder returns
`bad=0`, consumes the exact encoded size, recovers all 1024 symbols, and
preserves the decoded tail. It does not provide its own buffer trace or prove
termination. Source SHA-256:
`74752f9c3897d7770698e074ebbf74ab9858d25bc76cbc17a11e64bae86709b8`.

The existing direct-call harness is
`Mode2RansActualInverse.ec`, SHA-256
`c0925456cdfee7657e9aa2ebf0861e7e88d61903241868ea9c0cbeaa96e838a1`.
Its production relevance is limited to the ordered direct calls; it is a
proof-authored harness, not the full HBZ wrapper.

Week 13 authored-theory SHA-256 identifiers are:

- `Mode2RansCoreCompositionBridge.ec`:
  `b5ea18df339458716b26f9d2f2ab01ed9422f95acdaa65f058aa067b78c1e1c0`;
- `Mode2RansCoreActualInverse.ec`:
  `a069f4e848844ff0c5b55ec3330e0266d5e6a55f54cc33754963716535894a04`.

The first file proves actual-postcondition adapters for copy, trace indexing,
W64/int size, and decoder-state construction. The second invokes the three
reused top-level theorems sequentially over `Mode2RansActualHarness.run`.
Neither hash is trusted evidence: the claim rests on fresh `-no-eco`
compilation. No reused or new theorem supplies actual encoder success,
termination, full-HBZ wrapper correctness, or an encoding/security result.

## Week 14 full-HBZ wrapper reuse and authored boundary

Week 14 reuses the completed leaf and rANS results without inlining their
generated loops:

- `Mode2HbzPrepare.encode_hb_z1_prepare_core_mode2_correct`;
- `Mode2HbzApply.decode_hb_z1_apply_core_mode2_correct`;
- `Mode2HbzLeafRoundTrip.encode_prepare_decode_apply_mode2_inverse`;
- `Mode2RansEncoderOuterRefinement.actual_rans_encode_trace_refinement`;
- `Mode2RansSuffixCopy.copy_encoded_suffix_correct`;
- `Mode2RansDecoderTopHoare.actual_rans_decode_trace_refinement`;
- `Mode2RansCoreCompositionBridge.copied_suffix_is_exact_trace`;
- `segment_matches_implies_exact_decoder_segment_input` and
  `segment_matches_implies_decoder_word_reads`;
- `actual_decoder_input_from_copied_trace`,
  `configured_decoder_state_fields`, and
  `actual_decoder_input_from_configured_trace`;
- `encoder_success_size_word_bridge`;
- `Mode2HbzActualBoundary.pack_target_encode_hb_z1_full_exact_focused` and
  `unpack_target_decode_hb_z1_full_exact_focused`.

The locally authored Week 14 boundary consists of:

- `Mode2HbzInternalBoundaries.ec`, with four exact procedure equivalences, two
  pure semantic transports, and lifted internal Hoare theorems;
- `Mode2HbzFullEncodeTrace.ec`, proving the actual full encoder's explicit
  failure/success trace and frame contract;
- `Mode2HbzFullDecodeInverse.ec`, proving the actual full decoder's zero-bad
  coefficient inverse and tail frame from an exact successful trace;
- `Mode2HbzFullActualInverse.ec`, directly composing the two actual focused
  full wrappers without a success premise;
- `Mode2HbzSignatureBoundaryLift.ec`, providing the compiled exact production
  harness equivalence and SignaturePack/Unpack corollary.

The prepared-symbol existential in the encoder and pair postconditions is
introduced from the actual prepare call's post-state; it is not a theorem
precondition or an arbitrary exact-trace witness. The final pair and
production theorems retain the zero-size branch and make no termination,
success-reachability, malformed-input, zero-loss, or security claim.

## Week 15 fixed all-six success-witness reuse and authored boundary

Week 15 reuses the Week 14 actual-wrapper chain and the existing literal-table
and loop invariants. In particular, it imports
`actual_rans_encode_trace_closure`, `encoder_outer_tail_inv`,
`encoder_inner_tail_inv`, `full_encode_prepare_mode2_correct`,
`pack_target_encode_hb_z1_full_exact_focused`,
`actual_decode_hb_z1_full_mode2_inverse`, and
`signature_pack_unpack_hbz_full_actual_exact`. No encoder loop is copied into a
new theory.

The authored Week 15 proof boundary is:

- `Mode2RansAllSixBudget.ec` (SHA-256
  `4f3368905676620a1bd118ca65dc7b273a84d9cef5890f108ee24eeccd874dac`),
  which proves the byte-level zero-HBZ load/canonical bridge, actual prepare
  all-six result, symbol-6 one-byte normalization bound, first-four
  zero-emission calculation, and the 1020-byte coarse normalization budget;
- `Mode2RansEncoderActualTraceClosure.ec` (SHA-256
  `689d563a3a2c94b49df5c6b9e5259520223131f5f44638738840f77057648287`),
  whose strengthened postcondition preserves the concrete `off < 4` failure
  cause while retaining the previous public theorem by consequence; and
- `Mode2RansActualSuccessWitness.ec` (SHA-256
  `c006c23c4e5e31bdb20cdb64361dacf904ee65267fb06a3c10b50ba70feadb19`),
  which excludes that failure branch for all-six input and lifts the resulting
  Hoare theorem through the actual full HBZ and SignaturePack boundaries.

The hashes are drift identifiers, not trusted proof evidence. Evidence is the
fresh `-no-eco` compilation recorded by `verify-all.sh`. These are Hoare
partial-correctness results: they do not establish termination, probability
one, a non-vacuous execution witness, all-canonical-input success, or encoding
security.
