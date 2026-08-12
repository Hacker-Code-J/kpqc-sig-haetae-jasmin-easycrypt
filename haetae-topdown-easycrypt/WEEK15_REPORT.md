# Week 15 report - actual all-6 success witness

Date: 2026-08-11

## Decision

**GO-WITNESS.** `OBL-RANS-ACTUAL-SUCCESS-WITNESS` is now **PROVED (fixed
all-6 input, Hoare partial correctness)**. Every terminating execution from
the displayed fixed precondition returns the stated success result. This does
not prove that such an execution terminates or exists. No `phoare` theorem was
compiled, so fixed-input losslessness, probability-one success, and
non-vacuous reachability remain **PARTIAL**. The decision is not
`GO-WITNESS-LOSSLESS`.

## Baseline and authored scope

Before Week 15 edits, `scripts/verify-all.sh` returned
`RESULT PASS authored-targets=72 cache=-no-eco`. The preserved log is
`logs/verify-all-before-week15.log` (SHA-256
`be9090e879e36559005ffd4341e2397bc8746e1c2515f2c1ff0e29e0a4cabf6b`).
All authored changes remain below `haetae-topdown-easycrypt/`; the upstream
HAETAE, Jasmin, EasyCrypt, and ML-DSA roots remain read-only.

The two new proof targets are:

- `easycrypt/refinement/sign/Mode2RansAllSixBudget.ec`;
- `easycrypt/refinement/sign/Mode2RansActualSuccessWitness.ec`.

`Mode2RansEncoderActualTraceClosure.ec` is minimally strengthened in place so
the existing encoder-loop proof carries its actual failure cause. The old
`actual_rans_encode_trace_closure` surface remains available by consequence;
no second copy of the loop proof was introduced.

## Compiled theorem inventory

| Theorem | File:line | Compiled surface |
|---|---:|---|
| `zero_hbz_get32` | `Mode2RansAllSixBudget.ec:45` | byte-level zero array gives each actual LE32 coefficient load as `W32.zero` |
| `zero_hbz_canonical` | `Mode2RansAllSixBudget.ec:65` | derives canonical mode-2 HBZ without an input premise |
| `prepared_zero_hbz_is_all_six` | `Mode2RansAllSixBudget.ec:146` | prepared prefix over `zero_hbz` implies the first 1024 symbols are 6 |
| `actual_prepare_zero_hbz_all_six` | `Mode2RansAllSixBudget.ec:251` | actual full-wrapper-internal prepare returns `bad=0`, the prepared relation, all-six prefix, and tail frame |
| `symbol6_normalization_len_le1` | `Mode2RansAllSixBudget.ec:309` | for `2^23 <= x < 2^31`, symbol 6 emits 0 or 1 normalization byte |
| `all_six_first_four_no_normalization` | `Mode2RansAllSixBudget.ec:407` | the first four all-six steps emit no normalization byte |
| `all_six_normalization_budget` | `Mode2RansAllSixBudget.ec:419` | `n <= 1024` all-six symbols emit at most `max 0 (n-4)` normalization bytes |
| `all_six_trace_fits_mode2` | `Mode2RansAllSixBudget.ec:486` | first-1024 all-six input gives normalization size at most 1020 and total trace size in `[4,1024]` |
| `actual_rans_encode_failure_trace_cause` | `Mode2RansEncoderActualTraceClosure.ec:617` | actual nonzero `bad` implies normalization trace size greater than 1020 |
| `actual_rans_encode_all_six_success` | `Mode2RansActualSuccessWitness.ec:99` | direct actual rANS core success Hoare theorem |
| `full_rans_encode_all_six_success` | `Mode2RansActualSuccessWitness.ec:160` | exact internal-boundary lift to the rANS procedure inside the full wrapper |
| `actual_encode_hb_z1_full_zero_success` | `Mode2RansActualSuccessWitness.ec:190` | direct actual full-HBZ zero-input success theorem |
| `signature_pack_hbz_zero_success_mode2` | `Mode2RansActualSuccessWitness.ec:391` | compiled exact production `SignaturePack` lift |
| `actual_hbz_full_encode_decode_zero_success_mode2` | `Mode2RansActualSuccessWitness.ec:414` | direct focused full-wrapper zero round trip |
| `signature_pack_unpack_hbz_zero_success_mode2` | `Mode2RansActualSuccessWitness.ec:465` | production pack/unpack zero round trip |

Line numbers refer to the final Week 15 sources.

## Zero HBZ to actual all-six prepare

`zero_hbz` is `BArray8192.init (fun _ => W8.zero)`. The proof of
`zero_hbz_get32` opens `BArray8192.get32d_byte`, each initialized byte, and the
word bit projection before concluding `W32.zero`; coefficient loads are not
assumed from array naming. `zero_hbz_canonical` then checks the signed
coefficient range. The existing actual prepare correctness theorem is lifted
through `proc; sim` identity, and `prepared_zero_hbz_is_all_six` rewrites each
prepared symbol as `hbz_symbol_word W32.zero = W8.of_int 6`.

Thus the actual `_encode_hb_z1_prepare` call—not an arbitrary symbol witness—
supplies `bad=0` and `all_six_prefix` to the full wrapper proof.

## Pure one-byte and 1020-byte budget

The literal mode-2 table proof establishes `hbz_freq 6 = 398` and
`hbz_xmax 6 = 2097152 * 398 = 834666496`. The separate
`symbol6_div256_below_xmax` lemma proves `x %/ 256 < hbz_xmax 6` whenever
`x < 2^31`. Consequently two normalization emissions cannot occur for symbol
6.

EasyCrypt also computes the concrete pure states internally:

```text
8388608 -> 21582496 -> 55528910 -> 142868116 -> 367580518
```

The four corresponding prefixes have zero emitted bytes. Induction then uses
at most one byte for every remaining step, yielding 1020 normalization bytes
at `n=1024`; the four serialized final-state bytes give total size in
`[4,1024]`. The externally expected exact 174/178-byte execution is not used
or claimed as a theorem.

## Actual failure exclusion

The strengthened closure threads the concrete `off < 4` failure guard through
the existing outer/inner tail invariants. Its exported implication is:

```easycrypt
BArray16.get64 res.`2 1 <> W64.zero =>
  1020 < size (encode_trace (symbol_list_of_array symbols0)).`2
```

For `all_six_prefix symbols0 1024`, the pure theorem gives the opposite bound
`<= 1020`. `actual_rans_encode_all_six_success` eliminates failure by this
contradiction; no success, offset, buffer-fit, trace-size, or exact-output fact
appears in its precondition.

## Exact core pre/postcondition

The direct target is `RansEncodeTarget.M._rans_encode`.

Precondition:

```easycrypt
encp = enc0 /\ statep = state0 /\ symsp = symbols0 /\
esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
count = W64.of_int 1024 /\
all_six_prefix symbols0 mode2_hbz_count
```

Postcondition:

```easycrypt
BArray16.get64 res.`2 1 = W64.zero /\
0 <= W64.to_uint (BArray16.get64 res.`2 0) <= 1020 /\
4 <= 1024 - W64.to_uint (BArray16.get64 res.`2 0) <= 1024 /\
segment_matches res.`1 (W64.to_uint (BArray16.get64 res.`2 0))
  (mode2_trace_bytes all_six_symbols) /\
W64.to_uint (BArray16.get64 res.`2 0) +
  size (mode2_trace_bytes all_six_symbols) = 1024 /\
prefix_frame enc0 res.`1 (W64.to_uint (BArray16.get64 res.`2 0))
```

## Full and production pre/postconditions

`actual_encode_hb_z1_full_zero_success` directly targets
`HbzFullEncodeTarget.M._encode_hb_z1_full`. Its precondition binds
`outp=out_initial`, `hp=zero_hbz`, the literal encoder table, and
`(count,mhb,offset)=(1024,13,6)`. Its postcondition gives:

- nonzero returned size and `4 <= to_uint(size) <= 1024`;
- exact equality with `size (mode2_trace_bytes all_six_symbols)`;
- exact output segment at offset zero and `[size,2048)` output frame;
- an existential `prepared_symbols` captured from the actual prepare call,
  with `prepared_hbz_prefix`, `all_six_prefix`, and the same exact
  size/segment relation.

`signature_pack_hbz_zero_success_mode2` has the same input bindings and the
same nonzero-size, bound, exact-trace, and frame postcondition for
`SignaturePackMode2Target.M._encode_hb_z1_full`; it is obtained through the
compiled exact equivalence `pack_target_encode_hb_z1_full_exact_focused`.

The optional success-only corollaries also compile. The focused harness
`actual_hbz_full_encode_decode_zero_success_mode2` directly calls the actual
full encoder, observes its size, and calls the actual full decoder on the
nonzero branch. The production corollary
`signature_pack_unpack_hbz_zero_success_mode2` is lifted through
`signature_pack_unpack_hbz_full_actual_exact`. Their precondition is only the
exact initial tuple `(out0, zero_hbz, decoded0, bad0)`. Their postcondition
includes nonzero size, `decoder_ran=true`, decoder `bad=0`, zero decoded HBZ
prefix, coefficient and encoded tail frames, and the exact all-six trace.

## Verification

- Baseline: `RESULT PASS authored-targets=72 cache=-no-eco`.
- Individual fresh `-no-eco` compiles: pure budget, strengthened closure, and
  the combined core/full/production witness target all returned exit code 0.
- Final: `RESULT PASS authored-targets=74 cache=-no-eco`.
- The baseline and final logs are preserved as
  `logs/verify-all-before-week15.log` and `logs/verify-all-week15.log`.
- The final run also passed the proof-hole/authored-axiom/debug scan, manifest
  completeness checks, extraction and table-certificate drift checks,
  selected upstream baselines, read-only-root integrity check, and the LaTeX
  undefined-reference/citation/error gate.

## Remaining boundary and Week 16

There is no fixed-input `phoare = 1` or losslessness theorem. General rANS
termination, all-canonical-input success, malformed-input rejection,
canonical parsing, encoding delta zero, and implementation security remain
outside Week 15.

The Week 16 single recommended target is `OBL-SIG-H-ENCODE-DECODE`: the
actual mode-2 `h` suffix codec leaf/table/loop/full-wrapper inverse. Do not
widen Week 16 back to general rANS termination or all-input HBZ success.

## Post-report scope override — GO-MINCORE-7D

The preceding recommendation records the Week 15 handoff as originally made.
A later one-week paper deadline supersedes it: `OBL-SIG-H-ENCODE-DECODE` is
deferred, not proved.  The active Week 16 target is the focused KeyGen, Sign,
and Verify core theorem set plus restricted composition at the decoded-object
boundary.  The exact schedule and claim boundary are recorded in
`WEEK16_MINCORE_PLAN.md`.
