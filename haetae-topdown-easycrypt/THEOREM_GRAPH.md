# Theorem graph

Status meanings:

- **PROVED**: fresh-compiled with every premise visible.
- **PARTIAL**: a genuine child claim is proved but the named parent remains
  open.
- **SPECIFIED**: a compiled goal/interface exists without its proof.
- **BLOCKED**: a concrete missing extraction, semantic bridge, or
  probabilistic/numerical result prevents composition.
- **DEFERRED/paper boundary**: the obligation was time-boxed, remains
  unproved, and is intentionally not pursued through additional wrappers.

```text
Implementation-EUF-CMA                                      [SPECIFIED]
├── ImplementationSecurityComposition                      [SPECIFIED]
│   ├── FC-KeyGen / delta_KeyGen                            [PARTIAL]
│   │   ├── existing mode2 first-attempt relation           [PROVED]
│   │   ├── existing FFT-input bound and score guard        [PROVED]
│   │   ├── generated _pack_sk_m23 prefix                   [PROVED]
│   │   ├── generated _keypair_full_m23 return prefix       [PROVED/partial]
│   │   └── retry termination and distribution              [BLOCKED]
│   ├── FC-Sign / delta_Sign                                [PARTIAL]
│   │   ├── raw generated SHAKE helper chain                [PROVED]
│   │   ├── raw wrapper mu64->mu32 prefix                   [PROVED]
│   │   ├── exact _sf_mu_rawpre control adapter             [PROVED/raw]
│   │   └── sampler/rejection/hint/packing                   [BLOCKED]
│   ├── FC-Verify / delta_Verify                            [PARTIAL]
│   │   ├── raw generated SHAKE helper chain                [PROVED]
│   │   ├── challenge suffix absorb                         [PROVED]
│   │   ├── exact __verify_hash_mu raw-branch adapter       [PROVED/raw]
│   │   └── parse/norm/hint/final accept                    [BLOCKED]
│   ├── delta_Encoding                                      [PARTIAL]
│   │   ├── actual mode-2 signature prefix inverse         [PROVED/partial]
│   │   └── suffix/canonical parsing/full encoding          [BLOCKED]
│   └── raw API accepted-path memory/composition             [PARTIAL]
│       ├── generated VK/SK export/import helpers           [PROVED]
│       ├── canonical int/W64 address binding               [PROVED]
│       ├── actual raw KeyGen sequential export             [PROVED/partial]
│       ├── actual raw Sign exact mu trace                  [PROVED]
│       ├── actual raw/cryptolab Verify exact trace         [PROVED]
│       ├── actual Verify accept => tail_reached            [PROVED]
│       ├── accepted Verify hash-input binding              [PROVED]
│       ├── accepted generated hash/suffix adapters         [PROVED]
│       ├── OBL-SIGN-OUTPUT-FRAME                           [PROVED]
│       ├── OBL-RAW-MU-REGION-LOCALITY                      [PROVED]
│       ├── OBL-DIRECT-OBSERVED-MU                          [PARTIAL]
│       │   └── OBL-MU-PRODUCT-REPLAY                      [DEFERRED/boundary]
│       ├── direct Sign/Verify observed_mu equality         [PARTIAL]
│       └── Sign-write key-region frame/stability           [PROVED]
└── Paper-EUF-CMA                                           [PARTIAL]
    ├── MLWE                                                [ASSUMPTION INTERFACE]
    ├── BST-MSIS                                            [ASSUMPTION INTERFACE]
    ├── ROM                                                 [ASSUMPTION INTERFACE]
    ├── exact challenge/accepted distributions              [BLOCKED]
    ├── two-transcript forking extraction                   [BLOCKED]
    └── exact byte-level Sig_ROM instance                   [BLOCKED]
```

## First composition seam

```text
generated _pack_sk_m23
  ├── initial VK byte-copy invariant                       [PROVED]
  ├── _pack_vec_eta_to frame on [0,992)                    [PROVED]
  ├── _pack_vec2_eta_to frame on [0,992)                   [PROVED]
  └── key write starts after byte 992                       [PROVED]
        └── generated _keypair_full_m23 return prefix       [PROVED/partial]
              └── actual internal KeyGen return reaches
                  concrete VK stores/raw premises            [PROVED/partial]

actual generated raw SHAKE helpers
  ├── SK-prefix absorb = raw VK-memory absorb               [PROVED]
  ├── identical pre/message raw absorbs                     [PROVED]
  ├── Keccak init/permutation/finalize                       [PROVED]
  ├── squeeze64[0,32) = squeeze32                           [PROVED]
  └── local raw top wrappers produce mu prefix               [PROVED]
        ├── exact Sign generated-to-wrapper adapter         [PROVED]
        ├── exact Verify raw-branch-to-wrapper adapter       [PROVED]
        └── OBL-MU-TOPLEVEL-CONTROL                         [PROVED/raw]
              _sf_mu_rawpre ~ __verify_hash_mu directly
              └── actual challenge mu32 absorb at pos 64    [PROVED]
                    └── generated_raw_mu_to_challenge_suffix_zero_loss
                                                               [PROVED]

packed highbits || packed LSB || mu32
  ├── list-level challenge-input congruence                  [PROVED]
  └── OBL-HIGH-LSB-PACK                                     [BLOCKED]
        └── full challenge-call / ROM query adapter          [BLOCKED]

actual public API copy helpers
  ├── __kp_api_copy_2080_to_addr VK[0,992) export           [PROVED]
  ├── __kp_api_copy_2752_to_addr SK[0,1408) export          [PROVED]
  ├── Sign raw importer preserves SK[0,992)                 [PROVED]
  ├── Verify raw importer preserves VK[0,992)               [PROVED]
  └── OBL-API-KEY-MEMORY-RAW                                [SPLIT/Week 5]
        ├── preserve VK region across disjoint SK export    [PROVED]
        ├── bind W64 exporter address to int importer       [PROVED]
        ├── actual raw KeyGen ~ export trace                [PROVED]
        ├── actual KeyGen external prefix postcondition     [PROVED/partial]
        ├── actual raw Sign ~ mu trace                      [PROVED]
        ├── actual raw/cryptolab Verify ~ guarded mu trace  [PROVED]
        ├── actual Verify accept => tail_reached            [PROVED]
        ├── accepted Verify actual hash-input binding       [PROVED]
        ├── external buffers -> sk_memory_prefix, no stores [PROVED]
        ├── OBL-SIGN-OUTPUT-FRAME                           [PROVED]
        ├── OBL-RAW-MU-REGION-LOCALITY                      [PROVED]
        ├── OBL-DIRECT-OBSERVED-MU                          [PARTIAL]
        │   └── OBL-MU-PRODUCT-REPLAY                      [DEFERRED/boundary]
        └── OBL-API-KEY-MEMORY-RAW-ACCEPT                   [PARTIAL]
              ├── accepted generated hash-call mu prefix    [PROVED]
              ├── generated position-64 suffix adapter      [PROVED]
              ├── actual Sign→Verify trace/result equality  [PROVED]
              ├── accepted trace input binding              [PROVED]
              ├── direct trace observed_mu prefix           [PARTIAL]
              └── cross-call Sign-write key frame           [PROVED]

accepted Verify security lane
  VerifyAccept
    └── TailRan                                             [PROVED]
          └── ExactMuHashInputs                              [PROVED]
                └── generated mu-prefix adapter              [PROVED]
                      └── API trace-to-trace mu equality      [PARTIAL]

legitimate-signature functional lane
  OBL-SIGN-OUTPUT-TAIL-REACH                                [PARTIAL]
    ├── mode-2 challenge/low prefix inverse                 [PROVED/partial]
    ├── suffix/full pack-unpack inverse                     [BLOCKED]
    ├── norm and hint correctness                           [BLOCKED]
    └── Sign response/arithmetic correctness                [BLOCKED]
          └── OBL-SIGN-VERIFY-CORRECTNESS                   [BLOCKED]
```

`PROVED/partial` on KeyGen means a total Hoare partial-correctness theorem:
every terminating execution has the prefix property. It is not a termination
or losslessness theorem. Likewise, the new zero-loss composition is local to
the generated raw mu tops and challenge suffix. It is
`delta_mu_raw_top = 0`, not a full API delta.

Week 5 proves the actual KeyGen sequential postcondition, exact raw/cryptolab
Verify traces, and the accepted-path control/input-binding edges. Week 6 adds
the actual Sign output frame, region-local generated hash equivalence, and an
exact actual Sign→Verify sequential trace. All three
`cryptolab_haetae_mode2_*_internal` procedures now occur in compiled actual or
exact-to-trace theorems.  This still does not justify
`delta_mu_raw_api_accept = 0`: a direct theorem over the Sign and Verify trace
outputs is missing even though the Sign-write key-buffer frame is now proved.
The only current zero-loss claims at this layer are the accepted trace-bound
generated hash-call and generated position-64 suffix adapters.

## Week 7 additions

```text
OBL-MU-PRODUCT-REPLAY                                  [DEFERRED/paper boundary]
└── direct stored observed_mu equality                 [PARTIAL]

mode-2 signature codec
├── extracted wrapper parameters/layout audit          [PROVED]
├── prefix support theory                              [PROVED]
├── OBL-SIG-PREFIX-CODEC                               [PROVED/partial]
│   ├── actual _pack_sig_prefix layout                 [PROVED]
│   ├── actual _unpack_sig_prefix layout               [PROVED]
│   └── sequential actual-procedure inverse            [PROVED/partial]
├── OBL-SIG-PREFIX-FRAME                               [PARTIAL]
│   ├── unpack low-array tail                          [PROVED]
│   └── pack/challenge array tails                     [BLOCKED]
├── OBL-SIG-SUFFIX-METADATA                            [SPECIFIED]
├── OBL-SIG-SUFFIX-PADDING                             [SPECIFIED]
├── OBL-HBZ-PREPARE-CORRECT                            [PROVED]
├── OBL-HBZ-APPLY-CORRECT                              [PROVED]
├── OBL-HBZ-PREPARE-APPLY-INVERSE                      [PROVED]
├── OBL-HBZ-LEAF-FRAME                                 [PROVED]
├── OBL-RANS-MODE2-HBZ-TABLE-CERTIFICATE               [PROVED]
├── OBL-RANS-PURE-STEP-INVERSE                         [PROVED]
├── OBL-RANS-ENC-NORMALIZE                             [PROVED/actual-loop lift]
├── OBL-RANS-DEC-NORMALIZE                             [PROVED/actual-loop lift]
├── OBL-RANS-NORMALIZE-BYTE-INVERSE                    [PROVED/pure]
├── OBL-RANS-STATE-BOUND-PRESERVATION                  [PROVED/pure]
├── OBL-RANS-ENCODE-REFINEMENT                         [PROVED/partial correctness]
├── OBL-RANS-DECODE-REFINEMENT                         [PROVED/exact-trace partial correctness]
├── OBL-RANS-SUFFIX-COPY                               [PROVED]
├── OBL-RANS-ACTUAL-HARNESS-CONTROL                    [PROVED]
├── OBL-RANS-CORE-INVERSE                              [PROVED/success-conditioned partial correctness]
├── OBL-RANS-ACTUAL-SUCCESS-WITNESS                    [PROVED/fixed-input Hoare partial correctness]
├── OBL-SIG-HBZ-ACTUAL-BOUNDARY                        [PROVED]
├── OBL-SIG-HBZ-ENCODE-DECODE                          [PROVED/success-conditioned partial correctness]
│   ├── signature_pack_unpack_hbz_full_actual_exact    [PROVED]
│   ├── signature_pack_unpack_hbz_full_inverse_mode2   [PROVED/success-conditioned partial correctness]
│   └── actual_hbz_full_encode_decode_inverse_mode2    [PROVED/success-conditioned partial correctness]
├── OBL-SIG-H-ENCODE-DECODE                            [SPECIFIED]
└── OBL-SIG-FULL-CODEC-MODE2                           [BLOCKED]
```

`pack_unpack_sig_prefix_mode2_roundtrip` is a Hoare partial-correctness
theorem whose harness directly calls the generated `_pack_sig_prefix` and
`_unpack_sig_prefix`. Its canonical challenge and signed-byte premises have a
compiled all-zero witness. It proves neither suffix parsing nor the existence
or termination of an accepted Sign execution.

## Week 8 additions

```text
HBZ suffix codec
├── actual prepare correctness                          [PROVED]
├── actual apply correctness                            [PROVED]
├── actual prepare→apply inverse                        [PROVED]
├── actual leaf tail frames                             [PROVED]
├── actual full-procedure identity across focused and
│   signature pack/unpack extractions                   [PROVED]
├── generic mode-2 table arithmetic certificate         [PROVED]
├── concrete actual-array table certificate             [PROVED]
├── pure quotient/slot/fast-step inverse                [PROVED]
├── actual encoded-suffix copy helper                   [PARTIAL]
├── actual encoder normalization-loop refinement        [PARTIAL]
├── actual decoder normalization-loop refinement        [BLOCKED]
├── actual rANS core inverse                            [PARTIAL]
└── actual success-conditioned full HBZ inverse         [PROVED/success-conditioned partial correctness]
```

Week 8 closes the coefficient/symbol leaf layer first:
`Mode2HbzPrepare`, `Mode2HbzApply`, and `Mode2HbzLeafRoundTrip` all
fresh-compile. `Mode2HbzActualBoundary` additionally proves that the focused
HBZ extraction and the Week 7 signature pack/unpack extraction expose the same
actual `_encode_hb_z1_full` and `_decode_hb_z1_full` procedures. The generic
and concrete actual-array certificates both compile, as does the pure
single-step inverse in `Mode2RansCore`.  The graph deliberately stopped
before promoting this mathematical step to an actual loop theorem. Week 14
later closes the production wrapper composition; Week 15 closes the fixed
all-6 success witness, and Week 16 is limited to the `h` codec.

## Week 9 additions

```text
concrete tables + pure step                            [PROVED, Week 8]
            │
            ▼
xs/cuts/bytes trace and state bounds                   [PROVED, pure]
├── 0/1/2-byte normalization readback                  [PROVED, pure]
└── W32 shift/truncate/append and W64 cursor lemmas     [PROVED, word semantics]
            │
            ├──────── actual __copy_encoded_suffix ─── [PROVED]
            │
            ▼
actual _rans_encode control boundary                   [PROVED]
└── output-to-valid-trace refinement                   [PARTIAL]
            │
            ▼
actual encoder → actual copy → actual decoder harness  [PROVED/control only]
            │
            ▼
actual _rans_decode trace consumption                  [PARTIAL]
            │
            ▼
OBL-RANS-CORE-INVERSE                                  [PARTIAL]
└── actual success witness                             [PARTIAL]
```

`Mode2RansActualHarness.run` contains the three actual generated procedure
calls in the requested order and branches only on the actual encoder's
published `bad` value.  Its compiled theorem fixes decoder input fields to
`count=1024`, `size=count-off`, and `m=13` on that branch.  It does **not**
assert decoded-symbol equality, decoder success, final state `2^23`, or exact
consumption.  Those conclusions still depend on the two implementation
refinement edges shown as `PARTIAL`; the pure trace is not used as an external
precondition or an arbitrary witness.

## Week 10 additions

```text
actual BArray symbols
├── symbol_list_of_array / symbol_suffix               [PROVED]
├── segment_matches / prefix_frame algebra             [PROVED]
└── one-symbol encode_trace suffix recurrence          [PROVED, pure]
                         │
literal mode-2 esyms ───┼── actual reciprocal word step
                         │       = pure fast step       [PROVED, word-level]
                         │
actual _rans_encode nested normalization loop
├── finite W32 phase and W64 no-underflow               [PROVED]
├── exact set8 byte prepend and local prefix frame      [PROVED]
└── identify phase with pure 0/1/2 trace bytes          [PARTIAL]
                         │
actual _rans_encode success return
└── 0 <= off <= 1020, 4 <= 1024-off <= 1024            [PROVED/partial correctness]
                         │
whole actual suffix = trace_bytes(actual symbols)       [PARTIAL]
└── OBL-RANS-ENCODE-REFINEMENT                          [PROVED/partial correctness]
                         │
actual decoder trace refinement                         [PARTIAL; untouched Week 10]
└── OBL-RANS-CORE-INVERSE                               [PARTIAL]
```

The direct actual Hoare proof in `Mode2RansEncoderActualInner` now uses
`encoder_inner_segment_inv` for the nested generated loop.  This is stronger
than the Week 9 control boundary, but it is not the requested whole-encoder
trace postcondition.  The missing edge is precisely the actual outer
iteration: bind its loaded/protected table words to
`actual_mode2_encoder_word_step_correct`, install the pure trace-state bound
so the inner phase is the exact 0/1/2 normalization list, and re-establish the
accumulated suffix relation.  The final four-byte serialization leaf is
proved separately but has not yet been composed at the actual procedure
exit.  Accordingly Week 10 is `CONTINUE-ENCODER`, not `GO-ENCODER`.

## Week 11 encoder closure

```text
actual mode-2 symbol array
└── symbol_list_of_array / symbol_suffix                 [PROVED]
    └── encoder_outer_tail_inv                           [PROVED]
        ├── actual nested normalization while
        │   └── encoder_inner_tail_exit_exact             [PROVED]
        ├── generated table loads / protect erasures
        │   └── generated_loaded_nested_word_update       [PROVED]
        ├── one-symbol suffix/state/cursor transition     [PROVED]
        └── actual outer while closure at i=0             [PROVED]
            └── generated four-byte final stores          [PROVED]
                └── actual_rans_encode_trace_closure      [PROVED/partial correctness]
                    └── OBL-RANS-ENCODE-REFINEMENT        [PROVED/partial correctness]
                        ├── OBL-RANS-ACTUAL-SUCCESS-WITNESS [PROVED/fixed-input Hoare partial correctness]
                        ├── OBL-RANS-DECODE-REFINEMENT     [PROVED/exact-trace partial correctness]
                        ├── OBL-RANS-CORE-INVERSE          [PARTIAL]
                        └── OBL-SIG-HBZ-ENCODE-DECODE      [PARTIAL]
```

The encoder theorem's postcondition is a disjunction over the actual returned
`bad`. Success is not assumed. In the success branch the exact returned byte
segment is `trace_bytes(symbol_list_of_array(symbols0))`; no existential or
unrelated trace is used. Hoare semantics supplies partial correctness only,
so termination and actual success reachability remain outside this proved
node. The next graph edge is exclusively the actual decoder trace refinement.

## Week 12 decoder semantic closure

```text
canonical expected symbol array + exact trace_bytes
├── initial LE32 parse = encode_trace state             [PROVED]
├── concrete symbol_words lookup                        [PROVED]
├── concrete dsyms word update                          [PROVED]
├── generated 0/1/2-byte normalization loop             [PROVED]
├── decoded-prefix extension and untouched-tail frame   [PROVED]
└── actual outer-loop exit
    ├── internal state = 2^23                            [PROVED]
    ├── consumed offset = encoded_size                   [PROVED]
    ├── returned bad = 0                                 [PROVED]
    └── actual_rans_decode_trace_refinement              [PROVED/partial correctness]
        ├── actual encoder trace                         [PROVED separately]
        ├── actual suffix copy                           [PROVED separately]
        ├── sequential harness premise transport         [PARTIAL]
        ├── OBL-RANS-CORE-INVERSE                        [PARTIAL]
        └── OBL-SIG-HBZ-ENCODE-DECODE                    [PARTIAL]
```

`actual_rans_decode_trace_refinement` directly targets
`RansDecodeTarget.M._rans_decode`; it is not a pure decoder or observation
wrapper. Its input predicate contains the canonical expected array, the exact
`trace_bytes` segment, concrete state fields `(1024, encoded_size, 13)`, and
the generated mode-2 decode tables. Its postcondition publishes `bad=0`,
`off=encoded_size`, equality of all 1024 decoded symbols, and the
`[1024,2048)` output frame. The internal `x=2^23` fact is proved at the
generated loop exit and discharges the actual final reject check.

The graph stops before `OBL-RANS-CORE-INVERSE`: the already compiled encoder
and copy theorems have not yet been composed into the decoder's pointwise
trace-read premise inside the actual unary harness. This missing adapter is
Week 13's single edge. Termination, encoder-success reachability, the full HBZ
wrapper, and all security consequences remain outside the Week 12 theorem.

## Week 13 actual core composition closure

```text
actual RansEncodeTarget.M._rans_encode
├── failure: encoder_bad != 0
│   ├── decoder_ran = false
│   └── decoded/state results retain their initial values       [PROVED]
└── success: exact segment_matches(trace_bytes(actual symbols)) [PROVED]
    ├── W64 count-off = exact integer trace size                [PROVED]
    ├── actual HbzFullEncodeTarget.M.__copy_encoded_suffix
    │   └── slice_eq + segment_matches
    │       └── copied segment_matches at offset 0              [PROVED]
    ├── configured state fields = (1024,size,13)                [PROVED]
    ├── global trace segment -> every decoder byte read         [PROVED]
    └── actual RansDecodeTarget.M._rans_decode
        ├── bad = 0 and off = encoded_size                      [PROVED]
        ├── decoded[0..1024) = input symbols                    [PROVED]
        └── decoded[1024..2048) frame                           [PROVED]
            └── OBL-RANS-CORE-INVERSE
                [PROVED/success-conditioned partial correctness]
                ├── actual success reachability                 [PARTIAL]
                ├── encoder/decoder termination                 [PARTIAL]
                └── OBL-SIG-HBZ-ENCODE-DECODE                   [PARTIAL]
```

`actual_rans_encode_copy_decode_inverse` is a Hoare theorem over the existing
`Mode2RansActualHarness.run`. The harness directly executes all three pinned
generated procedures; the proof reuses their already compiled top-level
theorems sequentially. Its only semantic input invariant is
`mode2_hbz_symbol_stream` together with exact initial argument binding.
Encoder success, copied trace equality, decoder success, and decoded equality
are not preconditions.

The bridge derives the Week 12 pointwise normalization-byte reads from the
actual encoder segment and actual copy postcondition. Therefore no arbitrary
decoder buffer or replay witness remains at the core boundary. The result is
still a theorem about a proof-authored direct composition, not the production
`_encode_hb_z1_full`/`_decode_hb_z1_full` wrappers. Success reachability and
termination remain separate, so the HBZ parent and all encoding/security
claims remain open.

## Week 14 production wrapper boundary

```text
signature_pack_unpack_hbz_full_actual_exact               [PROVED]
├── production SignaturePack/Unpack direct harness       [PROVED]
├── focused full-HBZ direct harness                      [PROVED]
└── signature_pack_unpack_hbz_full_inverse_mode2         [PROVED/success-conditioned partial correctness]
    ├── size = 0                                          [failure branch]
    └── size <> 0                                         [success branch]
        ├── decoder_ran = true                            [PROVED]
        ├── decoded prefix / tail frame                   [PROVED]
        └── prepared_symbols witness                      [PROVED]
            └── actual all-6 success witness             [PROVED/fixed-input partial correctness]
```

The production wrapper theorem is now closed as success-conditioned partial
correctness. The fixed all-6 theorem excludes failure for terminating runs;
termination, losslessness, and non-vacuous reachability remain open.
The former Week 16 `h`-codec recommendation was superseded by the MINCORE
KeyGen first task.

## Week 16 MINCORE KeyGen first-task boundary

```text
actual KeygenMode2ParentTarget.M._kp_m23_matrix(rows=2, cols=3)
├── actual pre-finalization bp snapshot = res.`1                 [PROVED]
├── mode2_output_repr_bound16(output_row mat p0 p1 p2)          [PROVED]
├── mode2_ntt_repr_bound24(s1hat)                               [PROVED]
└── actual KeygenMode2ParentTarget.M._keypair_finalize_m23(512)
    ├── exact finalize_output                                   [PROVED]
    ├── scalar/HAETAE finalizer semantics                       [PROVED]
    ├── r = b0 + 2*b1, b0 in {-1,0,1}                          [PROVED]
    ├── adjusted_s2 = s2 - b0                                   [PROVED]
    ├── snapshot-only coefficient congruence mod 2q             [PROVED]
    └── initial/snapshot/final/scratch tail frames              [PROVED]

output_row(full_invntt(pointwise_row_ntt(...)))
├── output_row_from_mode2_ntt_words                             [PROVED]
│   └── array256_mont(full_invntt(pointwise_row_words(...)))    [PROVED]
├── actual_m23_matrix_snapshot_rows_explicit                    [PROVED]
│   └── both active rows of actual matrix→finalizer harness     [PROVED]
└── native Rq negacyclic row product                            [STOPPED]
    ├── odd-root orthogonality / full-NTT convolution leaf      [ABSENT]
    ├── Rq.poly -> HAETAE integer-list multiplication adapter   [ABSENT]
    ├── faithful KG-1                                           [NOT PROVED]
    ├── faithful KG-3                                           [NOT PROVED]
    ├── complete KG-4 vector construction                       [PARTIAL]
    └── paper A s = q j (mod 2q)                                [NOT PROVED]
        └── OBL-MINCORE-KEYGEN                                  [PARTIAL / STOP-KG-NTT]
```

`ActualM23MatrixFinalizeSnapshot.run` contains the two actual calls shown
above and only the intervening immutable snapshot assignment.  Its Hoare
precondition has exact initial bindings, the existing matrix/input
representation bounds, centered active `s2`, and canonical active `avec`.
No finalizer result, KG predicate, success result, or desired equation is a
premise.

The compiled `actual_snapshot_mod2q_zero` relation deliberately uses the
actual returned `pre_bp` snapshot.  It must not be relabeled as the paper
matrix-vector equation until the missing `output_row`/full-NTT to
security-model multiplication bridge compiles.  The KG-NTT-MUL continuation
audited that edge and stopped it at the missing odd-root orthogonality/full-NTT
convolution theorem; it did not turn the desired product into a representation
premise.  KeyGen is frozen at KG-2/finalization. The focused
`Mode2SignAcceptedCore` harness now directly composes the three actual Sign
helpers and proves accepted-branch control, but the graph stops at
`STOP-SIGN-CHAL-MODE2`: the full highbits/LSB/mu challenge leaf is absent and
paper S-1/S-4 retain the frozen convolution dependency. The active graph moves
to MINCORE-VERIFY. Sampler distribution, retry termination, packers, public
APIs, and security remain outside scope.
