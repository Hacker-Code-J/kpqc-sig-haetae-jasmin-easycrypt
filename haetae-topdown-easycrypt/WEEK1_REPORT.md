# Week 1 report

## Outcome

The sprint produced a reproducible proof workspace rather than a claim of full
verification.  Seven authored EasyCrypt targets compile without cache reuse.
The key new implementation-facing theorem relates the generated Sign and
Verify `mu32` absorb procedures.  Four existing KeyGen first-attempt/FFT/guard
theorems are re-exported through a premise-preserving adapter.  The direct
KeyGen packed-prefix procedure theorem remains open; its pure array lemmas are
closed.

## Checked results

1. `sign_verify_mu32_absorb_from_pos64` — actual extracted Sign/Verify
   procedure equivalence for the last 32 challenge-input bytes.
   `absorb_precondition_has_witness` proves that its position/prefix premises
   have a concrete model and are not contradictory.
2. `challenge_input_eq_from_mu_prefix` and
   `challenge_input_eq_components` — byte-list construction equality.
3. `copied_prefix_step`, `copied_prefix_complete`, and
   `vk_prefix_eq_set_after` — prefix copy and suffix-write frame facts.
4. `imported_mode2_full_first_attempt_equiv`, FFT-input, score-guard, and
   accepted-first-attempt adapters — exact reuse, no strengthened conclusion.
5. Compiled FC/security goal signatures and a restricted cryptographic
   assumption interface.

## Blocking findings

- `_pack_sk_m23` visibly copies the first `vkbytes` bytes from `vkp`, but the
  procedure-level proof must also frame all later eta/key writes and the public
  memory contract.
- Sign hashes the SK prefix and emits 64 bytes; Verify hashes explicit VK and
  emits 32.  SHAKE prefix consistency is not enough until their complete byte
  inputs are proved equal.
- The existing one-shot FIPS202 extraction is not called by these specialized
  API paths, so it cannot close their transcript obligation by itself.
- Existing KeyGen proof covers a peeled first attempt and exact guard facts,
  not actual key distribution, later retries, termination, packing, or the
  FFT numerical tail.
- Existing security compilation is conditional.  Its exact paper bridge,
  challenge distribution, rejection exactness, ROM domains, and forking
  extraction remain open; a coarse rejection loss at least one is vacuous.

## Throughput

- **Functional/extraction track:** one non-trivial cross-extraction procedure
  equivalence, seven new byte/prefix/non-vacuity lemmas, four checked reuse adapters, and
  precise maps of all three public APIs.
- **Distribution/security track:** zero new distributional or reduction
  theorems closed; one security-facing transcript seam was reduced to three
  named byte/hash obligations.  This disparity is material for scheduling.

## Status by API

- **KeyGen: PARTIAL.** First attempt, selected sampler/M23/NTT/singular/FFT
  inputs and score guard are reusable.  Full distribution, retries,
  termination, numerical bad event, TieMin, packing, and API refinement remain.
- **Sign: PARTIAL.** Focused transcript extraction and the `mu32` absorb loop
  are checked.  Parse, hyperball, challenge sampling, response/hint, rejection,
  packing, and public API remain.
- **Verify: PARTIAL.** Focused hash/challenge extraction and one cross-path
  absorb equivalence are checked.  Parsing, reconstruction, norm/hint,
  canonicality, transcript head, and final event equivalence remain.
- **Implementation security: BLOCKED.** No justified numerical deltas yet.
- **Paper reduction: PARTIAL/conditional.** Compiled theorem families retain
  open paper-correspondence premises.

## Evidence-based estimate

At the observed rate, a single-researcher mode-2 functional proof is roughly
12–20 researcher-weeks: the byte transcript seam is tractable, but Sign and
Verify arithmetic/encoding loops are largely unextracted.  Distributional,
numerical, and paper-faithful security closure is another 24–40+ weeks, with
FFT tails, accepted rejection distribution, and forking as high-variance work.
The full composed result is therefore about 36–60 researcher-weeks (roughly
9–15 calendar months for one researcher), not one follow-on sprint.  A small
team could parallelize arithmetic, transcript/encoding, and security tracks,
but 6–10 months remains a defensible range.

For publication, the current evidence supports a first paper scoped to
mode-2 public-API functional refinement plus transcript/packing correctness.
Paper-faithful EUF-CMA composition and numerical/distributional closure are
better treated as a second contribution unless the next two sprints close the
hash/packing seam substantially faster than this baseline.

## Next week

Close the exact SK/VK 992-byte prefix procedure theorem, then prove the SHAKE
32-byte prefix theorem for equal complete inputs and compose it with the
already checked absorb equivalence.  Do not spend the next sprint deepening an
unconnected arithmetic branch before this API seam is closed.

## Verification record

```text
./haetae-topdown-easycrypt/scripts/verify-all.sh
  RESULT PASS authored-targets=7 cache=-no-eco

./haetae-topdown-easycrypt/scripts/verify-baselines.sh
  PASS security fresh targets=16
  PASS NTT target refinement
  PASS FIPS202 generated extraction target
  PASS KeyGen mode-2 parent composition
  PASS KeyGen M23 first-attempt head
  RESULT PASS selected-baselines=20 read-only=true
```

Both commands rechecked source hashes and the tracked read-only roots.  The
baseline script executes equivalent fresh compile heads rather than the
upstream wrapper scripts because those wrappers write logs inside the
read-only source tree.
