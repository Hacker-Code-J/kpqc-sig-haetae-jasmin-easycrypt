# Week 2 report

Evidence date: 2026-08-05.

## Sprint goal and outcome

The target seam was:

```text
prefix_992(sk) = vk
  => equal_hash_inputs
  => take_32(mu_sign^64) = mu_verify^32
  => equal_challenge_suffix
```

The sprint closed this seam through actual generated packer/hash/challenge
helpers and explicit local wrappers. It did not yet close the exact generated
top-level control relation for `_sf_mu_rawpre` and the raw branch of
`__verify_hash_mu`.

Final claim status:

- `KG-PREFIX-CALL`: **PROVED as partial correctness**
- `MU32-HASH-RAW-HELPERS`: **PROVED**
- parent `MU32-HASH` raw/internal call site: **PARTIAL**
- public-context variant: **SPECIFIED**
- local wrapper/helper `delta_mu = 0`: **PROVED**
- full public API `delta_Sign`, `delta_Verify`, `delta_Encoding`: not claimed

## Actual packed-key procedure theorems

`easycrypt/refinement/keygen/ExtractedPackedKeyPrefix.ec` fresh-compiles:

```easycrypt
hoare [Parent._pack_sk_m23 :
  vkp = vk0 /\ vkbytes = W64.of_int 992 /\
  mcount = W64.of_int 3 /\ kcount = W64.of_int 2
  ==> vk_prefix_eq res vk0 992]
```

as `pack_sk_m23_mode2_vk_prefix`.

The proof uses:

- a byte-copy invariant `copied_prefix skp vk0 (to_uint i)`;
- `pack_vec_eta_to_prefix_frame`, showing the `3 * 64` eta writes begin at
  offset 992;
- `pack_vec2_eta_to_prefix_frame`, showing the `2 * 96` eta2 writes begin
  after that;
- `mode2_key_index_after_prefix`, showing the final 32-byte key write is also
  outside `[0,992)`.

It is lifted to:

```easycrypt
hoare [Parent._keypair_full_m23 :
  k = 2 /\ m = 3 /\ vkbytes = 992
  ==> vk_prefix_eq res.`2 res.`1 992]
```

and then to `crypto_sign_keypair_internal_mode2_jazz` with a `true`
precondition. These are partial-correctness results: if the retrying KeyGen
returns, its packed pair has the prefix relation. No termination, losslessness,
or output-distribution conclusion follows.

## Raw/internal mu hash path

`easycrypt/refinement/composition/ExtractedMuHashPrefix.ec` fresh-compiles the
following generated-procedure relations:

- `sign_verify_keccak_init_from_same_state`
- `sign_verify_keccakf1600_from_same_state`
- `sign_verify_finalize_from_same_state`
- `sign_verify_absorb_addr_from_same_state`
- `sign_sk_verify_vk_absorb_mode2`
- `sign_verify_final_squeeze_mu32_prefix`
- `sign_verify_raw_mu_core_prefix`
- `sign_verify_raw_mu_top_wrappers_prefix`

The key theorem assumes:

- the same raw pre and message pointers and lengths;
- the same relevant global-memory bytes;
- a concrete 992-byte `sk_memory_prefix`;
- `to_uint(base) + 992 < W64.modulus`.

It concludes bytewise:

```text
forall i, 0 <= i < 32 =>
  sign_mu64[i] = verify_mu32[i]
```

The proof does not assume an abstract SHAKE prefix property. It links the
actual extracted SK/raw-memory absorb loops, identical raw-address absorb
loops, finalize code, Keccak permutation, Sign's word-oriented 64-byte squeeze,
and Verify's byte-oriented 32-byte squeeze. The squeeze proof uses the pinned
little-endian lane lemmas `rate_lane_byte_get8`, `drop_bytes0`, and
`drop_bytes_succ`.

### Exact remaining raw/internal boundary

The local `SignRawMuTop` and `VerifyRawMuTop` wrappers reproduce the generated
helper sequence and initialization. The exact refinement from generated
`_sf_mu_rawpre` and the raw branch of `__verify_hash_mu` to those wrappers has
not fresh-compiled. It is named `OBL-MU-TOPLEVEL-CONTROL`.

The missing proof must expose branch condition, local-variable scheduling,
argument binding, and pointer-protection/memory premises. It may not be
replaced with a SHAKE axiom. Consequently `MU32-HASH` is honestly `PARTIAL`
even though its complete raw helper chain is `PROVED`.

## KeyGen-to-mu reachability and non-vacuity

`Mode2MuChallengeComposition.keygen_prefix_reaches_mu_memory` takes the
returned KeyGen prefix relation and constructs Verify memory with:

```easycrypt
stores mem (W64.to_uint base)
  (take 992 (BArray2080.to_list vk))
```

It then proves the exact `sk_memory_prefix` used by the raw hash theorem.
`mode2_base_zero_no_wrap` gives the concrete witness `base = W64.zero` for the
pointer no-wrap premise. This advances beyond Week 1's generic mu-array
witness: actual KeyGen output establishes the packed relation, and a concrete
memory construction establishes the helper call premise.

## Composition theorem

`Mode2MuChallengeComposition.raw_mu_to_challenge_suffix_zero_loss`
fresh-compiles an equivalence between:

1. the Sign raw-mu wrapper followed by the generated Sign mu32 challenge
   absorb, and
2. the Verify raw-mu wrapper followed by the generated Verify mu32 challenge
   absorb.

With the same pre/message bytes, the constructed 992-byte key memory relation,
equal challenge state, and challenge position 64, the returned challenge state
and position are equal. This composes
`sign_verify_raw_mu_top_wrappers_prefix`,
`sign_verify_mu32_absorb_from_pos64`, and the concrete KeyGen-to-memory bridge.

Therefore the local mu/challenge-suffix seam has no statistical or
cryptographic loss:

```text
delta_mu = 0
```

This equality is scoped to the proved wrappers/helpers. It does not imply that
the full Sign, Verify, or encoding deltas are zero.

## Public-context path

Status: **SPECIFIED**.

The following distinct path was intentionally not conflated with raw/internal
pre-processing:

- Sign: `_sf_prepare_pre_raw` followed by `_sf_mu_preptr`;
- Verify: `__verify_hash_mu` high-bit branch;
- condition: `ctxlen <= 255`;
- encoded pre: one `ctxlen` byte followed by `ctx`.

Its next theorem must prove the branch condition and encoded-pre memory
equality before it can reuse the raw helper result.

## Failed or rejected approaches

- An abstract “SHAKE64 output has SHAKE32 as a prefix” axiom was rejected.
- Treating the Week 1 satisfiable witness as call-site reachability was
  rejected.
- A direct `inline; sim` proof from the generated top procedures stalled on
  generated local/control scheduling and pointer-protection obligations; the
  compiled helper composition was retained and the residual was named.
- Raw/internal and public-context paths were not merged.
- Whole-KeyGen termination was not made a premise of the prefix theorem.

## Extraction and trust boundary

Focused targets are regenerated from pinned source and checked against
`manifests/generated-extractions.sha256`. The actual KeyGen lift imports the
pinned generated parent theory because the focused packer-only target does not
contain `_keypair_full_m23`; its SHA-256 is recorded in
`manifests/sources.sha256`.

Compilation establishes the stated EasyCrypt judgments for translated code.
The Jasmin-to-EasyCrypt translator, EasyCrypt kernel, Why3, and SMT solvers
remain in the trusted computing base.

## Verification

The integrated command is:

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

It checks source and extraction hash drift, all 11 authored targets with
`-no-eco`, hole/axiom/debug scans, manifest completeness, selected baselines,
tracked read-only source invariance, and the LaTeX build. The authoritative
outcome in `logs/verify-all-summary.txt` is:

```text
RESULT PASS authored-targets=11 cache=-no-eco
```

## Throughput and estimate

Functional/procedure work advanced from a generic array witness to:

- three actual KeyGen/packer return-prefix theorems;
- actual SK/VK absorb, Keccak/finalize, and 64/32 squeeze equivalences;
- one security-facing raw-mu/challenge composition theorem.

Distribution/security work did not close a new paper-level reduction. The only
zero-loss result is local deterministic refinement. This asymmetry supports
keeping the next sprint narrow.

## Week 3 go/no-go

The repository is a **go** for another focused SHAKE/control/memory sprint and
a **no-go** for expanding the public-API paper claim. Because the pack prefix
closed while parent `MU32-HASH` remains partial, Week 3 should close
`OBL-MU-TOPLEVEL-CONTROL` and actual caller memory reachability before starting
highbits/LSB or a broader challenge equivalence.
