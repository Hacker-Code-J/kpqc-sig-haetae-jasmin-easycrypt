# Week 7 report

Date: 2026-08-07

## Outcome

Week 7 ends with **FREEZE-A / GO-B**.

- Lane A was time-boxed and frozen at an explicit paper boundary:
  `OBL-MU-PRODUCT-REPLAY` is `DEFERRED`,
  `OBL-DIRECT-OBSERVED-MU` remains `PARTIAL`, and
  `delta_mu_raw_api_accept = 0` is not claimed.
- Lane B closed the actual mode-2 signature-prefix round trip:
  `OBL-SIG-PREFIX-CODEC` is `PROVED` as partial correctness under explicit
  canonical-input premises.
- Suffix metadata, padding, hbz/h rANS inverses, the complete codec, norm gate,
  and Sign-output tail reach remain separate obligations.

The sprint did not start highbits/LSB, full challenge-call equivalence,
distribution proofs, or modes 3/5.

## Baseline

Before Week 7 edits, `scripts/verify-all.sh` passed with 26 authored targets.
The preserved result is `logs/week7-baseline-summary.txt`.

## Lane A — product/replay feasibility

### Compiled prerequisites

- `sign_verify_generated_raw_mu_prefix_regionwise` directly compares actual
  generated `_sf_mu_rawpre` and `__verify_hash_mu` return values under
  region-local memory relations.
- `raw_sign_then_verify_actual_exact_trace` preserves actual sequential
  Sign/Verify results and final memory through the trace pair.
- accepted Verify execution implies `tail_reached` and binds the actual hash
  descriptor inputs.

### Unclosed edge

No permitted proof converted the generated returned-value pRHL theorem into a
post-state equality of
`SignRawApiMuTrace.observed_mu` and
`VerifyCryptolabMuTrace.observed_mu`. The traces contain unequal residual
continuations, and eliminating the Sign continuation one-sidedly would require
the open signing losslessness/termination result. The current traces also do
not retain a hash-time memory snapshot from which a unary replay theorem can
be derived.

The prototype therefore stopped without adding a caller wrapper, observation
wrapper, replay witness, SHAKE-locality axiom, or observation precondition.
The exact decision and rejected approaches are in
`PRODUCT_REPLAY_DECISION.md`.

## Lane B — focused extraction and audited layout

`scripts/extract-signature-codec.sh` extracts and fresh-compiles:

- `pack/SignaturePackMode2Target.ec`, SHA-256
  `cec608044cf12611e5fddce4764bf9b582aa03c3ce69caaeb8d453ed4028f8a9`;
- `unpack/SignatureUnpackMode2Target.ec`, SHA-256
  `8780917ae0788d151cd6ccac6713c80da3b0e75018f22b883bfd58a8064d8adf`.

The actual wrappers fix the shared parameter sequence to:

```text
sigbytes=1474, lcount=4,
hb_count=1024, hb_m=13, hb_offset=6,
h_count=512, h_m=13, h_offset=239,
base_hb=132, base_h=7, payload_limit=416
```

The extracted code gives this byte layout:

| Range | Meaning |
| --- | --- |
| `[0,32)` | 256 challenge bits packed little-endian within each byte |
| `[32,1056)` | 1024 low coefficients, one truncated signed byte each |
| `[1056,1058)` | hb/h encoded-size deltas |
| `[1058,1058+hbsize)` | hbz encoded payload |
| following bytes | h encoded payload |
| through byte 1473 | canonical zero padding after both payloads |

The equality `1056 + 2 + 416 = 1474` is the actual payload boundary. The size
bytes are offsets from `base_hb=132` and `base_h=7`; the unpacker also checks
nonzero/range/total-size conditions before accepting the suffix.

## Fresh-compiled prefix theorems

### Packer layout

`Mode2SignaturePrefixPack.pack_sig_prefix_mode2_layout` opens the actual
generated `_pack_sig_prefix` loops:

```easycrypt
hoare [Pack._pack_sig_prefix :
  cp = cp0 /\ lowp = low0 /\
  lcount = W64.of_int 4 /\ sigbytes = W64.of_int 1474
  ==>
  packed_challenge_prefix res cp0 32 /\
  packed_low_prefix res low0 1024]
```

### Unpacker layout and low-array frame

`Mode2SignaturePrefixUnpack.unpack_sig_prefix_mode2_layout` opens the actual
generated `_unpack_sig_prefix` loops. Given the two packed-layout predicates,
it proves 256 decoded challenge words, 1024 sign-extended low words, and that
the unused low-array words `[1024,2048)` retain their input values.

### Actual sequential round trip

`Mode2SignaturePrefixRoundTrip.PrefixRoundTrip.run` calls, in order, the
actual generated `_pack_sig_prefix` and `_unpack_sig_prefix`. The theorem

```easycrypt
lemma pack_unpack_sig_prefix_mode2_roundtrip
```

proves:

```text
canonical_challenge(cp) /\ canonical_signed_low(low)
  => challenge_prefix_eq(decoded_cp, cp)
     /\ low_mode2_eq(decoded_low, low)
     /\ low_tail_frame(initial_decoded_low, decoded_low)
```

This is Hoare partial correctness. It does not assert whole-Sign termination.
`canonical_challenge` requires each of the 256 input words to be exactly 0 or
1. `canonical_signed_low` requires each of the 1024 words to be the signed
8-bit extension of its low byte, with integer value in `[-128,128)`.
`prefix_codec_preconditions_satisfiable` gives concrete all-zero arrays, so
the premises are non-vacuous.

### Frame boundary

The unpacked low-array tail frame is compiled. A separate theorem that the
packer preserves its input `BArray2948` bytes `[1474,2948)` is not compiled;
nor is a challenge-output-array tail frame. These are recorded as
`OBL-SIG-PREFIX-FRAME`, not hidden inside the inverse claim. No global-memory
write occurs in these standalone array procedures.

## Claim status

| Claim | Status | Exact boundary |
| --- | --- | --- |
| `OBL-MU-PRODUCT-REPLAY` | `DEFERRED / EXPLICIT PAPER BOUNDARY` | returned generated hashes are not transported to stored trace observations |
| `OBL-DIRECT-OBSERVED-MU` | `PARTIAL` | direct post-state `observed_mu` equality absent |
| `OBL-SIG-PREFIX-CODEC` | `PROVED` | canonical mode-2 prefix, partial correctness |
| `OBL-SIG-PREFIX-FRAME` | `PARTIAL` | unpack low tail proved; other output-array tails open |
| `OBL-SIG-SUFFIX-METADATA` | `SPECIFIED` | exact gates/layout audited, no procedure theorem |
| `OBL-SIG-SUFFIX-PADDING` | `SPECIFIED` | exact zero-padding scan audited, no procedure theorem |
| `OBL-SIG-HBZ-ENCODE-DECODE` | `SPECIFIED` | actual pair extracted |
| `OBL-SIG-H-ENCODE-DECODE` | `SPECIFIED` | actual pair extracted |
| `OBL-SIG-FULL-CODEC-MODE2` | `BLOCKED` | suffix inverses/metadata/padding missing |
| `OBL-SIG-CANONICAL-PARSE` | `PARTIAL` | prefix canonicality only |
| `OBL-SIGN-OUTPUT-TAIL-REACH` | `PARTIAL` | full codec, norm, hint, arithmetic missing |
| `OBL-SIGN-VERIFY-CORRECTNESS` | `BLOCKED` | legitimate-output correctness not proved |

## Verification

The final verifier regenerates and hash-checks both codec targets, checks the
actual procedure/theorem surface, fresh-compiles all 30 authored targets with
`-no-eco`, runs hole/axiom/debug/manifest/source-drift scans and all pinned
baselines, and builds the LaTeX notes. The final result is recorded in
`logs/verify-all-summary.txt` and `logs/latex-build.log`.

## Claims not available

Week 7 does not establish `delta_mu_raw_api_accept = 0`, full encoding loss
zero, accepted-signature existence, Sign termination, full Verify correctness,
Sign-output tail reach, or implementation EUF-CMA security.

## Week 8 decision

- Lane A: **FREEZE-A**. Do not add another caller/observation wrapper.
- Lane B: **GO-B**. The single first obligation is
  `OBL-SIG-HBZ-ENCODE-DECODE` for actual
  `_encode_hb_z1_full` / `_decode_hb_z1_full`; only after it closes should the
  h codec and full canonical suffix composition proceed.
