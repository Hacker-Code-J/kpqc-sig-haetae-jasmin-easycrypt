# Week 6 report

Date: 2026-08-07

## Objective and baseline

The sprint targeted a post-state theorem for

```text
mu32_prefix(
  SignRawApiMuTrace.observed_mu,
  VerifyCryptolabMuTrace.observed_mu)
```

after executing the actual raw Sign and an accepted actual raw Verify call.
The pre-edit command `./haetae-topdown-easycrypt/scripts/verify-all.sh`
passed with 22 authored targets; its summary is preserved as
`logs/week6-baseline-summary.txt`.

## Compiled Week 6 results

### OBL-SIGN-OUTPUT-FRAME — PROVED as partial correctness

`RawApiSignOutputFrame.ec` proves the generated output copy exactly writes
the first 1474 signature bytes and frames every byte outside that range:

```easycrypt
hoare [Sign._api_copy_2948_to_raw :
  Glob.mem = mem0 /\ dstp = sigu0 /\ srcp = sig0 /\
  len = 1474 /\ valid_region_int sigu0 1474
  ==>
  res = sigu0 /\ signature_prefix Glob.mem sigu0 sig0 1474 /\
  byte_frame_outside mem0 Glob.mem sigu0 1474]
```

The caller theorem
`sign_raw_api_frames_reused_regions` directly targets
`Sign.cryptolab_haetae_mode2_signature_internal`. Under a valid signature
output and explicit disjointness of `[sigu,sigu+1474)` and
`[siglenu,siglenu+8)` from VK/SK/pre/message, it concludes:

- result `W64.zero` for every terminating execution;
- byte stability of VK 992, SK 1408, pre `prelen`, and message `mlen`;
- `loadW64 Glob.mem siglenu = W64.of_int 1474`.

`sign_raw_api_preserves_external_key_prefix` further transports
`external_key_prefix_match mem0 sku vku` through that actual Sign call. The
contract has the concrete witness formalized by
`sign_output_frame_contract_satisfiable`. Signing-loop termination is not
claimed.

### OBL-RAW-MU-REGION-LOCALITY — PROVED

`RegionLocalMuEquivalence.ec` introduces

```easycrypt
region_eq mem1 mem2 base len :=
  forall i, 0 <= i < W64.to_uint len =>
    loadW8 mem1 (W64.to_uint base + i) =
    loadW8 mem2 (W64.to_uint base + i)
```

and proves the actual generated pre/message absorb loops under this local
relation. The key step separately relates Sign's local packed-SK prefix to
Verify's external VK region. Init, absorb, finalize, Keccak permutation, and
64/32-byte squeeze are then composed.

The strongest theorem is
`RegionLocalMuTop.sign_verify_generated_raw_mu_prefix_regionwise`:

```easycrypt
equiv [Sign._sf_mu_rawpre ~ Verify.__verify_hash_mu :
  Glob.mem{1} = sign_mem /\ Glob.mem{2} = verify_mem /\
  skp{1} = sk0 /\ vkp{2} = base /\
  vkbytes{1} = W64.of_int 992 /\ vklen{2} = W64.of_int 992 /\
  equal pre/message pointers and lengths /\ raw_prelen prelen{2} /\
  sk_memory_prefix sk0 verify_mem base /\
  valid pre/message regions /\
  region_eq sign_mem verify_mem prep{2} prelen{2} /\
  region_eq sign_mem verify_mem mp{2} mlen{2}
  ==>
  mu32_prefix res{1} res{2}]
```

Thus whole-memory equality is no longer needed. No SHAKE/locality axiom was
introduced; the proof opens the actual generated load loops.

### Actual sequential trace — PROVED up to the observation relation

`RawApiDirectObservedMu.ec` defines an actual sequence and its exact trace:

```text
actual cryptolab_haetae_mode2_signature_internal
  -> actual cryptolab_haetae_mode2_verify_internal

SignRawApiMuTrace.run
  -> VerifyCryptolabMuTrace.run
```

`raw_sign_then_verify_actual_exact_trace` proves equality of both results and
final `Glob.mem`; both residual computations are retained. On the trace side:

- `sign_then_verify_trace_accept_implies_tail_reached` derives
  `res.`2 = W64.zero => VerifyTrace.tail_reached`;
- `sign_then_verify_accept_binds_observed_inputs` derives both traces' exact
  mode-2 VK/pre/message inputs in the post-state.

Neither theorem mentions `tail_reached` or either `observed_mu` value in its
precondition. `sign_frame_establishes_raw_mu_read_relation` proves that an
imported SK prefix, KeyGen external prefix, and the actual Sign frame imply
the exact region-local relation needed by the generated hash theorem.

## Remaining direct-observation boundary

`OBL-DIRECT-OBSERVED-MU` remains **PARTIAL**. There is no compiled theorem
whose postcondition is

```easycrypt
mu32_prefix(
  SignRawApiMuTrace.observed_mu,
  VerifyCryptolabMuTrace.observed_mu)
```

after the two trace calls. The missing rule is not byte locality, caller input
binding, output framing, or accept-to-tail control; those now compile. It is a
product/replay argument that transports a relational theorem about two hash
procedures to the stored results of two calls already completed inside one
unary sequential trace. Treating the two stored values as preconditions would
repeat the Week 5 adapter and was rejected.

The bounded semantic audit names this residual
`OBL-MU-PRODUCT-REPLAY`. EasyCrypt's `byequiv` pattern does not by itself turn
the existing pRHL procedure judgment into the required unary Hoare
postcondition. A direct full-trace pRHL alignment would also need to discharge
the unpaired post-hash Sign continuation; doing that with a one-sided call
would require the still-open signing rejection-loop losslessness result. That
would improperly fold termination into this partial-correctness sprint.

Consequently:

- `OBL-DIRECT-OBSERVED-MU`: **PARTIAL**;
- `OBL-API-KEY-MEMORY-RAW-ACCEPT`: **PARTIAL**;
- `delta_mu_raw_api_accept = 0`: **not claimed**.

The earlier generated-call equality and position-64 suffix adapter remain
proved, but are weaker than direct trace-output equality.

## Address and non-vacuity audit

`canonical_region(a,n)` permits `a = W64.modulus` when `n = 0`; therefore it
does not alone imply `W64.to_uint(W64.of_int a)=a`. The Week 6 bridge exposes
`canonical_ui64_address` separately for every integer address/length whose
round trip is used. The disjoint frame predicate has a concrete witness, so
the frame theorem is not vacuous.

There is still no witness that a Sign-produced signature passes all Verify
gates. That is exactly `OBL-SIGN-OUTPUT-TAIL-REACH`, which remains
**SPECIFIED**, while `OBL-SIGN-VERIFY-CORRECTNESS` remains **BLOCKED**.

## Verification

- Targeted fresh compilation passed for:
  `RawApiSignOutputFrame.ec`, `RegionLocalMuEquivalence.ec`,
  `RegionLocalMuTop.ec`, and `RawApiDirectObservedMu.ec`.
- All are compiled with `-no-eco` by `scripts/verify-all.sh`.
- The aggregate verifier also checks extraction regeneration/hash drift,
  source/read-only drift, manifest completeness, proof holes, authored axioms,
  debug declarations, `stores mem 0` in Week 6 evidence, baselines, and LaTeX.
- Final aggregate result:
  `RESULT PASS authored-targets=26 cache=-no-eco`, recorded in
  `logs/verify-all-summary.txt`.

## Go/no-go

This is a **no-go for claiming API-level zero loss or starting full
accepted-path highbits/LSB composition**. Week 6 was the last dedicated
caller-plumbing sprint. Week 7 should either validate one explicit
product/replay semantics construction for the stored hash results, or freeze
the compiled generated-hash adapter as the paper boundary and redirect the
main lane. Adding another observation wrapper without that semantic rule is
not justified.
