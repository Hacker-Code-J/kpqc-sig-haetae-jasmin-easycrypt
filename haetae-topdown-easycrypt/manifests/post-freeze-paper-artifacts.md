# Post-freeze paper contribution ledger

This ledger is the canonical claim boundary for work after commit `4bde120`
(`PAPER-FROZEN`) on branch `post-freeze-kg-rq-haetae-bridge`.  It supplements,
and does not rewrite, `manifests/paper-artifacts.md`.  A result marked
`PROVED` means that its named EasyCrypt theorem compiles with the premises in
its statement.  It does not promote a local or conditional theorem to an
end-to-end HAETAE claim.

## Inventory

- 82 authored EasyCrypt targets remain in the frozen paper manifest.
- `manifests/post-freeze-proof-targets.txt` adds exactly 167 targets: 163
  theories under `post-freeze/` and four shared NTT/Rq theories under
  `haetae-ntt-verify/easycrypt/`.
- The numerical layer contains nine Python checkers, seven JSON certificates,
  and two non-invasive C trace extractors under `post-freeze/`.
- `manifests/post-freeze-claim-map.tsv` maps every one of these 185 proof and
  executable artifacts to one contribution ID, evidence status, and permitted
  paper use.  Its current partition is C1=53, C2=36, C3=80, S2=10, S3=6.
- `scripts/verify-post-freeze.sh` is the aggregate reproduction boundary for
  the 167 targets and the executable certificates.  It is intentionally
  separate from the frozen 82-target verifier.

## Contribution matrix

| ID | Status | Defensible contribution | Exact boundary |
| --- | --- | --- | --- |
| `C1-FAITHFUL-REFINEMENT` | `PROVED` as deterministic/Hoare refinement slices | Full-NTT Montgomery spectral action, generic and mode-2 row products, `Rq`--HAETAE coefficient representation, a faithful 2-by-6 KeyGen carrier satisfying the paper `A s = q j (mod 2q)` equation for the checked parent, and an exact actual Verify trace through unpack, matrix/CRT, recovery, norm, and tail to the public accepted path | No KeyGen sampler distribution or unbounded retry termination; no full Sign refinement; the Verify result is an exact implementation trace, not equality with the legacy paper challenge abstraction |
| `C2-CHALLENGE-MODEL` | `PROVED`, with an explicit XOF randomness premise for the distributional lift | Byte-faithful Sign/Verify challenge input coupling, deterministic squeeze/rejection/shuffle replay, canonical equal accepted challenges of exact weight 58, exact uniform 58-subset point mass `1 / binomial(256,58)` under the uniform-byte contract, and a mode-2 ROM carrier/programming interface | Deterministic SHAKE output is not proved uniform; the raw Sign API is not refined to an abstract signing oracle; no adversary-wide EUF-CMA advantage bound |
| `C3-QUANTITATIVE-KEYGEN` | `PROVED-CONDITIONAL` | First-attempt score/reject equivalence, later-retry semantic snapshots, finite-budget outcome-mass decomposition and exhaustion accounting, exact ideal eta laws, eighth-moment FFT certificates, an actual-sample accumulator unsafe bound below `1/2 + delta_xof`, and an accepted ordered-trace P8 mass bridge at `epsilon_p8 + delta_xof` | Progress defects, the first-attempt score tail, the ideal accepted-trace P8 mass, and `delta_xof` are not numerically discharged; no unbounded-loop termination or full `HAETAE.kg` distribution equality |
| `S1-FROZEN-CORPUS` | `PROVED` at the frozen claim boundary | The 82-target byte/word-level corpus: API key transport, raw mu traces, signature-prefix codec, HBZ/rANS refinement, and selected KeyGen/Sign/Verify procedure slices | See `manifests/paper-artifacts.md`; none of its partial parents is silently upgraded here |
| `S2-SIGN-ROM` | `PROVED` as an operational interface | Raw Sign challenge observation, exact mode-2 carrier validity, transcript/site logging, and freshness/non-reprogramming invariants for repeated programmed calls and explicit ROM queries | The patched abstract transcript is not claimed to be the raw signature, to verify, or to instantiate the full security game |
| `S3-PUBLIC-KEY-NMA` | `PROVED` as a public-view adapter | Faithful checked public-key sources and exact NMA wrapper/direct-game equalities | No secret-key semantics, CMA signing interface, total KeyGen, or equality with the original `HAETAE.kg` distribution |

The matrix is a readable summary.  The TSV claim map is the exhaustive source
of artifact-to-claim membership; adding, removing, duplicating, or leaving an
artifact unmapped makes the aggregate verifier fail.

## Headline evidence

### C1: faithful deterministic refinement

- `NTTFullSpectralAction.full_ntt_montgomery_spectral_action` and
  `full_ntt_montgomery_row_product` close the full-transform convolution and
  arbitrary-column row-product foundation without using the incomplete legacy
  `Rq.ntt` object.
- `RqHAETAEBridge.rq_poly_mul_repr` and `rq_poly_dot3_repr` transport checked
  native-ring multiplication into HAETAE coefficient semantics.
- `KgFaithfulAugmentedModel.checked_mode2_parent_m23_finalize_faithful_augmented_paper_as_qj`
  proves the coefficientwise faithful augmented equation for the actual
  checked parent.  The security-facing BArray-free packaging is continued by
  `Mode2FaithfulSecurityKeygenRelationPostFreeze` and
  `Mode2FaithfulSecurityKeygenPaperLiftPostFreeze`.
- `VerifyActualFullFunctionalRawPostFreeze.actual_verify_full_mode2_exact_flat_trace`
  binds the actual full mode-2 Verify procedure to the complete staged trace.
  `VerifyActualFullAcceptApiRawPostFreeze.actual_verify_cryptolab_accept_exact_flat_trace`
  transports the accepted result through the raw/public caller boundary.

### C2: challenge semantics and model correction

- The generated Verify rejection sampler is decomposed into accepted-index,
  stream replay, reservoir, subset, and binomial layers.  Under the explicit
  uniform-byte contract,
  `VerifyChallengeM23XofRandomnessBoundaryPostFreeze.parametric_xof_support_point_256_58`
  gives the exact point probability.
- Accepted actual Verify traces expose canonical equal parsed and recomputed
  challenges with exact support cardinality 58 through
  `VerifyActualAcceptChallengeEqualityRawPostFreeze`,
  `VerifyActualAcceptChallengeWeightPostFreeze`, and
  `VerifyActualChallengeSupportPostFreeze`.
- `KgActualAvecQjBlocker.security_named_qj_is_not_paper_qj` records that the
  pre-existing synthetic security object is not the paper correction: its
  distinguished coefficient is 401, while paper `qj[0][0]` is 64513 and the
  deterministic actual zero-seed row begins with 44985.
- `VerifyActualChallengeAlgebraBridgePostFreeze` records that the historical
  structural `challenge_from_seed` shortcut does not implement the actual
  SHAKE/rejection/shuffle sampler.  These negative results are proof-soundness
  findings, not assumptions to be hidden.

### C3: finite retry and certified accumulator risk

- The checked retry chain proves one-step semantic correctness, rejected-tail
  state preservation, bounded-driver termination under explicit progress
  windows, adjacent-budget exhaustion monotonicity, and exact sampled outcome
  mass partitions.
- `Mode2FaithfulSecuritySampledFirstAttemptDSeedScoreTailPostFreeze.sampled_bounded_keygen_success_lower_bound_from_dseed_score_tail_certificate`
  exposes the finite-budget success lower bound in terms of the progress
  defect, first-attempt score tail, and accumulated one-step defect.
- The accumulator chain proves exact eta byte/polynomial/vector laws,
  context-dependent final-`s2` bias decomposition, centered moments through
  order eight, root-sensitive FFT profiles, and exact rational P8 checks.
- For the deterministic accepted context, the all-slot coordinate certificate
  is approximately `0.00094162110313979575 < 1/1024`.  Removing the redundant
  lower-prefix envelope yields an exact component union approximately
  `0.4060052607303988 < 1/2` while the deterministic energy/error budget is
  approximately `32670.86893216008 < 32768`.
- `Mode2FaithfulSecurityIdealAccumulatorUpperPrefixComponentP8CertificatePostFreeze.ideal_mode2_accumulator_unsafe_mu_lt_one_half_closed`
  closes the fixed-context ideal theorem.
  `Mode2FaithfulSecurityActualAccumulatorUpperPrefixTransportPostFreeze.checked_snapshot_accumulator_unsafe_mu_lt_one_half_plus_gap`
  transports it only with the explicit all-event `delta_xof` gap.
- The follow-up accepted-context feasibility audit proves that context validity
  alone admits every scalar class 0 through 5 and identifies the missing
  bridge from accepted first-attempt snapshots to an admissible ordered
  class-trace set.  Its first reproducible accepted first-attempt fixture is
  seed index 27 with score 533485; the existing fixed caps give an exact
  diagnostic union `0.3611855361011244... < 1/2`.  This single fixture is not
  a uniform theorem and is marked `FOLLOWUP-ONLY` in the claim map.
- `Mode2FaithfulSecuritySampledFirstAttemptClassTracePostFreeze` adds the
  distribution-route carrier requested by that audit.  It preserves the full
  ordered 2-by-256 trace in `(accepted, score, trace)`, proves exact event
  equality with the existing sampled-`dseed` first-attempt program, and
  factors the summary distribution through the existing correlated
  `((pre_bp, avec), (s1, sampled_s2))` joint carrier under the explicit checked
  snapshot premise.  The existing all-event `delta_xof` gap is transported
  through this summary map by data processing.  It introduces no independence
  or conditional-law claim.
- `Mode2FaithfulSecuritySampledFirstAttemptAcceptedClassTraceP8PostFreeze`
  instantiates that carrier for the unconditional event
  `accepted /\ P8_bad(ordered trace)`.  An explicit ideal-summary mass
  certificate at `epsilon_p8` transports to the sampled-`dseed` program with
  only the existing additive `delta_xof` gap.  The theorem supplies the exact
  distribution-weighted bridge but does not invent a numeric `epsilon_p8`;
  that value still requires a new ideal accepted-trace mass certificate.

## Explicit limitations and prohibited promotions

The following statements are **not** established and must not appear as paper
claims without new proofs:

1. End-to-end functional correctness of all KeyGen, Sign, and Verify public
   APIs.
2. Implementation-level EUF-CMA security or a completed paper reduction.
3. Equality of deterministic SHAKE/XOF output with the ideal uniform-byte or
   iid-eta laws, or the assignment `delta_xof = 0`.
4. Unbounded retry termination, a numeric whole-KeyGen acceptance bound, or
   equality with the full `HAETAE.kg` distribution.
5. A raw-memory refinement from the actual Sign API to the patched abstract
   signature/ROM signing oracle.
6. A context-free or random-context accumulator bound.  The checked
   zero-seed accepted trace has `accepted_attempt = 2` and counters 10 through
   15; it is not a first-attempt witness, whose checked counter is 5.
7. Reuse of the synthetic security `qj` or historical structural
   `challenge_from_seed` object as if either were the actual implementation
   semantics.
8. A numeric value for the ideal mass of
   `accepted /\ P8_bad(ordered trace)`.  The program-level bridge is proved,
   but its `epsilon_p8` premise still requires a new ideal-summary
   distribution certificate.

## Paper positioning

The defensible umbrella claim is:

> A machine-checked, byte-to-game audit and refinement spine for HAETAE-2 that
> connects selected actual Jasmin procedures to faithful algebraic,
> distributional, and numerical semantics while making every unresolved
> randomness, retry, and model-correspondence loss explicit.

The three contribution sentences are:

1. We provide a machine-checked deterministic refinement spine that closes a
   faithful augmented KeyGen equation and the actual mode-2 Verify accepted
   trace without conflating implementation objects with legacy security-model
   shortcuts.
2. We derive the exact mode-2 challenge carrier and uniform 58-subset law
   under an explicit XOF contract, integrate it with ROM programming
   interfaces, and mechanically expose two concrete abstraction mismatches
   that make the corresponding direct promotions invalid.
3. We give compositional finite-retry and FFT-accumulator risk analyses with
   executable exact certificates, terminating at an honest
   `1/2 + delta_xof` actual-transport boundary rather than assuming the missing
   coupling.

Claims of novelty or priority relative to external literature require a
separate literature review; this ledger certifies only what the repository
currently proves.

## Reproduction and trust boundary

Run:

```sh
./haetae-topdown-easycrypt/scripts/verify-post-freeze.sh
```

The terminal success line is:

```text
RESULT PASS post-freeze-theories=167 checkers=9 certificates=7 cache=-no-eco
```

Logical checking trusts EasyCrypt, Why3, and the selected SMT prover.  The
implementation link additionally trusts Jasmin and `jasmin2ec`.  The exact
numeric/trace layer uses Python's exact integer/rational arithmetic, the host C
compiler for the non-invasive trace harness, SHA-256 source pinning inside the
checkers, and EasyCrypt premises that identify the checked external
certificate.  No newly authored `axiom`, `admit`, or proof escape is permitted
on this surface.

Nine generated extraction families reuse the hashes in
`manifests/generated-extractions.sha256`.  The sole new generated family,
`VerifyUnpackMode2Target`, is separately pinned by
`manifests/post-freeze-generated-extractions.sha256`; the verifier checks both
hash manifests before compiling any post-freeze theory.
