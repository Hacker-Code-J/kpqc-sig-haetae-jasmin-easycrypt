# Target Mode-2 Key-Generation Parent Extraction

> **Claim boundary:** this gate establishes reproducible extraction and
> `-no-eco` compilation of the actual deterministic mode-2 key-generation
> parent. It does not establish a semantic theorem for that parent or an
> end-to-end refinement result.

## Scope and selected entry

The extraction selects the deterministic mode-2 entry from the pinned target
source:

```text
crypto_sign_keypair_internal_mode2_jazz
```

The entry and its shared mode-2/mode-3 parent occur at these exact ranges:

| Procedure | Target source | Generated range |
| --- | --- | --- |
| `_keypair_full_m23` | `keypair.jazz:1123-1215` | `KeygenMode2ParentTarget.ec:2483-2588` |
| `crypto_sign_keypair_internal_mode2_jazz` | `keypair.jazz:1305-1319` | `KeygenMode2ParentTarget.ec:2589-2601` |

The selected entry invokes `_keypair_full_m23` with the exact arguments:

```text
(k, m, vkbytes, best_count, tau, rem, singular_bound)
= (2, 3, 992, 5, 58, 24, 611098)
```

These constants are visible at `keypair.jazz:1317` and in the generated call at
`KeygenMode2ParentTarget.ec:2598-2599`.

## Control flow present in the generated parent

The generated `_keypair_full_m23` retains the following source-level
orchestration:

| Stage | Source lines | Generated lines | Extracted behavior |
| --- | --- | --- | --- |
| Seed expansion | `keypair.jazz:1160` | `KeygenMode2ParentTarget.ec:2539` | Calls `_kp_expand_seedbuf` once to fill the shared 128-byte seed buffer. |
| Uniform expansion | `keypair.jazz:1161-1162` | `KeygenMode2ParentTarget.ec:2540-2541` | Passes that buffer to `_kp_polymatkm_expand_matA` and `_kp_polyveck_expand_vecA` with `k = 2` and `m = 3`. |
| Eta retry sampling | `keypair.jazz:1164-1173` | `KeygenMode2ParentTarget.ec:2542-2550` | Starts `counter` at zero. Each attempt samples three `s1` polynomials from `counter`, samples two `s2` polynomials from `counter + 3`, and advances `counter` by `3 + 2 = 5`. |
| Matrix step | `keypair.jazz:1175-1177` | `KeygenMode2ParentTarget.ec:2551-2553` | Calls `_kp_m23_matrix` inside the retry loop; Jasmin spill/unspill directives are erased by extraction. |
| Finalization | `keypair.jazz:1179-1193` | `KeygenMode2ParentTarget.ec:2554-2568` | Computes `count = k * 256` and calls `_keypair_finalize_m23`. |
| Singular guard | `keypair.jazz:1195-1206` | `KeygenMode2ParentTarget.ec:2569-2581` | Calls `_singular_full` with `(m, k, best_count, tau, rem)` and retries when the unsigned singular value exceeds `singular_bound`; mode 2 supplies bound `611098`. |
| Output slices and packing | `keypair.jazz:1209-1212` | `KeygenMode2ParentTarget.ec:2583-2586` | Takes the 32-byte slices `rhop = seedbuf[0:32]` and `keyp = seedbuf[96:32]` (bytes 96 through 127), then calls `_pack_vk_m23` and `_pack_sk_m23`. |

For mode 2, the eta calls therefore use counts three and two over consecutive
five-slot retry windows: the first call starts at the current counter, the
second starts three slots later, and the next attempt starts five slots later.
This paragraph describes the extracted `W64` control flow; it is not a proof of
no-wrap arithmetic, sampler termination, or sampler distributions.

## Regeneration and exact inventories

Run commands from the `haetae-ref-easycrypt` project directory:

```sh
./scripts/regenerate-keygen-mode2-parent-extract.sh
```

The effective extraction command is:

```sh
jasmin2ec --array-model=barray \
  --output-array=<temporary-directory> \
  -o <temporary-directory>/KeygenMode2ParentTarget.ec \
  -f crypto_sign_keypair_internal_mode2_jazz \
  ../haetae-ref-jasmin/jasmin/keypair.jazz
```

Generation must produce exactly the 32 theories in
`manifests/keygen-mode2-parent-extract-files.txt` and the 56 procedures in
`manifests/keygen-mode2-parent-procedures.txt`. The selected entry, parent,
seed expansion, sampler callers and leaves, Keccak routines, NTT/matrix
routines, finalization, FFT/singular routines, and packing routines are all in
that recorded closure. Generated files under
`easycrypt/extract/keygen-mode2-parent/` must not be edited manually.

## Drift and compilation checks

```sh
./scripts/check-keygen-mode2-parent-extract-drift.sh
./scripts/verify-keygen-mode2-parent-extract.sh
```

The drift checker regenerates in a temporary directory, checks both exact
inventories, and compares all 32 generated theories byte-for-byte. The verifier
first checks the pinned source hashes, reruns the drift check, compiles all 32
theories with `easycrypt compile -no-eco`, and rejects `admit`/`abort` proof
commands and axiom declarations. It records the full result in
`logs/keygen-mode2-parent-extract-summary.txt`.

The retained verification summary reports zero regeneration drift, 32/32
successful uncached compilations, a 56-procedure closure, and passing proof-hole
and axiom scans. The generated target recorded by that run has SHA-256 digest:

```text
248f8157e348e3f294665d12573a58ee58e860884356bfe82324fda64de5d0b4
```

## Follow-on refinement proofs

The separate refinement in
[`13-target-keygen-mode2-parent-refinement.md`](13-target-keygen-mode2-parent-refinement.md)
uses seven checked equivalences to transport the established seed, sampler
caller, and certificate-conditioned leaf contracts to procedures in the actual
`KeygenMode2ParentTarget.M` module. It then composes those procedures in an
authored proof-only observer with the exact mode-2 dimensions, shared expanded
seed, first eta-attempt schedule, and counter advance.

That observer stops before `_kp_m23_matrix`. It is not
`_keypair_full_m23` or the public mode-2 wrapper, so the extraction claim on
this page remains distinct from the later sampler-prefix semantic claim.

The still later M23 gate in
[`14-target-keygen-m23-matrix.md`](14-target-keygen-m23-matrix.md) separately
relates the actual fixed-parameter `_keypair_full_m23` to a result-carrying
mirror that peels and records its first attempt, then preserves the residual
retry loop and both packing calls. It also proves the recorded first-attempt
sampler, M23, finalizer, canonical, HAETAE, counter, exact singular/FFT
machine-word evaluator, bound, and guard facts, plus totality of the fixed
singular call. Those authored theorems do not enlarge this extraction gate's
claim: the checks on this page establish only reproducible extraction and
compilation.

## What remains unproved

This extraction makes the actual parent control flow available for subsequent
refinement, but extraction and compilation alone prove none of its functional
meaning. The later sampler-prefix and bounded first-attempt proofs narrow that
gap through separate authored theorems. In particular, this extraction gate
itself does not prove:

- a Hoare, pRHL, or losslessness theorem for `_keypair_full_m23` or the selected
  mode-2 entry;
- termination of the eta/singular-value retry loop, nor propagation of finite
  sampler-prefix certificates through that loop;
- correctness of the NTT/matrix operations, `_keypair_finalize_m23`, the
  singular-value computation and guard, or public/secret-key packing;
- source-pointer safety, aliasing, or correspondence between source memory and
  the extracted value-array model; or
- composition of the leaf and caller results into a complete mode-2 keypair
  theorem, correspondence with the security model, or end-to-end public-API
  refinement.

The follow-on proofs explicitly connect the seed and sampler procedures through
an authored prefix and relate the fixed-parameter parent to the peeled
first-attempt mirror. A complete parent result still requires explicit memory
relations, later-attempt certificate propagation, an acceptance and
outer-loop-termination argument, an analytic real/spectral interpretation and
error/range theorem for the exact singular-word evaluator, packing semantics,
and the remaining public-API and security compositions.
