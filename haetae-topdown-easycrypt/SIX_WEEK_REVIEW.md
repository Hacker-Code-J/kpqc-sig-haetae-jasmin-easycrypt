# Six-week checkpoint

Date: 2026-08-07

## Major fresh-compiled results

- Week 1: top-level FC/security signatures, byte/list transcript lemmas,
  position-64 mu absorb equivalence, and an import-only KeyGen first-attempt
  adapter.
- Week 2: actual packer and terminating-KeyGen 992-byte VK/SK prefix
  partial correctness; generated absorb/finalize/Keccak/squeeze mu-prefix
  chain.
- Week 3: direct generated `_sf_mu_rawpre ~ __verify_hash_mu` raw-branch
  control and generated challenge-suffix composition.
- Week 4: int/W64 address bridge, actual raw-ABI focused extraction, copy
  helpers, and stores-free external-buffer relations.
- Week 5: actual raw KeyGen sequential export, exact Verify trace on all
  branches, `accept => tail_reached`, and accepted hash-input binding.
- Week 6: actual raw Sign signature/siglen frame, actual generated region-local
  mu equivalence, exact actual Sign→Verify sequential trace, and accepted
  post-state input binding.

The final manifest contains 26 authored targets. The aggregate verifier reports
`RESULT PASS authored-targets=26 cache=-no-eco` in
`logs/verify-all-summary.txt`.

## API status

| API/lane | Status | Strongest compiled boundary | Main residual |
|---|---|---|---|
| KeyGen functional | PARTIAL | terminating internal/raw KeyGen returns/exports `prefix_992(sk)=vk` | retry termination, complete paper refinement, distribution, packing/public contract |
| Sign procedural | PARTIAL | exact raw trace; imported SK/input binding; actual output frame | signature-core functional correctness and termination |
| Verify security control | PROVED on accepted path | exact all-branch trace; `accept => tail_reached`; actual hash descriptor binding | no accepted-signature existence claim |
| Generated raw mu | PROVED | actual generated calls under region-local VK/pre/message relation | public-context branch excluded |
| Direct trace mu | PARTIAL | actual sequential trace and all premises compile | product/replay transport to stored `observed_mu` outputs |
| Product/replay transport | SPECIFIED | `OBL-MU-PRODUCT-REPLAY` names the exact semantic gap | justified unary product/replay rule without assuming Sign-loop losslessness |
| Sign-output tail reach | SPECIFIED | theorem signature/dependencies only | pack/unpack inverse, norm, hint, response arithmetic |
| Sign/Verify correctness | BLOCKED | top-level signature only | all preceding functional obligations |

## Throughput assessment

Functional/procedure work produced concrete progress in each sprint: focused
extraction, exact caller mirrors, loop invariants for copies/absorbs, branch
control, and partial-correctness frame/export theorems. The most effective
unit of work has been a small generated procedure plus one explicit memory or
control invariant.

Distribution/security work progressed more slowly. The project has a sound
accepted-event control adapter and exact generated transcript subrelations,
but has not proved sampler distributions, accepted rejection distributions,
challenge entropy, forking extraction, or an end-to-end advantage bound. A
compiled deterministic seam is not a distribution theorem.

## TCB, assumptions, and contracts

The trusted computing base contains EasyCrypt, Why3 and selected provers,
`jasmin2ec` extraction, the pinned generated theories, and the imported
HAETAE/Keccak specification surfaces explicitly listed in the manifests.
Extraction hashes detect drift but do not prove translator soundness.

Permitted final cryptographic assumptions remain MLWE, BST-MSIS, and ROM.
Memory validity, canonical int/W64 conversion, cross-invocation stability,
alias/disjointness, and termination are runtime/refinement obligations, not
cryptographic assumptions. No Week 6 implementation semantics is hidden in an
authored axiom, and no Week 6 API proof uses `stores mem 0 ...`.

## Minimal publishable claim today

A defensible narrow result is:

> For pinned mode-2 raw/internal Jasmin procedures, the KeyGen VK/SK prefix,
> Sign output frame, accepted Verify tail/input binding, and region-local
> generated Sign/Verify mu hash equivalence have machine-checked
> partial-correctness proofs, with explicit memory and canonical-address
> premises.

The paper must separately state that direct equality of the two completed
caller traces' stored mu observations is not yet proved. Therefore it must not
claim `delta_mu_raw_api_accept=0`, full challenge equality, full functional
correctness, or public-API EUF-CMA security.

## Non-vacuity

The frame/disjointness contract has a concrete address witness, and raw length
predicates have concrete witnesses. The actual accepted-path implication is
semantically correct (`accept => tail_reached`), but an accepted execution
witness for a Sign-produced signature is not yet available. This is an open
functional-correctness obligation rather than a hidden premise.

## Next six weeks

1. Spend at most one bounded sprint on an explicit product/replay semantics
   rule that connects the region-local pRHL theorem to the two stored trace
   outputs. Require a compiled prototype before extending the architecture.
2. If that prototype fails, freeze the Week 5/6 generated hash-call adapter as
   the explicit paper boundary; do not add more caller-observation wrappers.
3. Start the functional lane for `OBL-SIGN-OUTPUT-TAIL-REACH` with exact
   signature pack/unpack inverse and norm-gate conditions.
4. Only after a direct or explicitly bounded adapter decision, begin
   accepted-path highbits/LSB and full challenge-entry extraction.
5. In parallel as a separate research lane, plan rejection distribution and
   challenge entropy/forking obligations; do not mix them with procedural
   correctness percentages.
6. Re-estimate full public-API EUF-CMA completion only after at least one
   distribution theorem compiles.

## Lanes to stop or redesign

- Stop adding proof-only observation wrappers around the same caller seam.
- Redesign the direct-output proof around a justified product program,
  deterministic functional hash specification, or explicit replay theorem.
- Do not enter highbits/LSB under an asserted API zero-loss claim while
  `OBL-DIRECT-OBSERVED-MU` is partial.
- Keep KeyGen retry/FFT numerical tails and Sign rejection distributions in
  independent lanes with separate progress accounting.
