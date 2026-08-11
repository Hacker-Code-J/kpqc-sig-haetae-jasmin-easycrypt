# Week 5 report - accepted-path composition and residual boundaries

Evidence date: 2026-08-07.

## Outcome

Week 5 closes the sequential KeyGen export boundary, the accepted Verify
tail-boundary, the accepted-path hash-call adapter, and the generated helper
suffix adapter. It does **not** close a direct
`mu32_prefix(SignTrace.observed_mu, VerifyTrace.observed_mu)` theorem across
the actual caller executions, and it does **not** compile a Sign-output
frame/stability theorem strong enough to promote the accepted-path adapter to
`delta_mu_raw_api_accept = 0`.

The operational status therefore changes as follows:

- `OBL-API-KEY-MEMORY-RAW-ACCEPT` stays **PARTIAL**.
- `OBL-SIGN-OUTPUT-TAIL-REACH` is now **SPECIFIED** as the next long-term
  gate.
- `OBL-SIGN-VERIFY-CORRECTNESS` is now **BLOCKED** on that gate and the
  remaining packing/norm/challenge equalities.

## Proof inventory

### KeyGen sequential export — PROVED

`RawApiKeygenSequentialExport.keypair_raw_api_exports_matching_prefixes`
fresh-compiles for the actual
`RawKeygenApiTarget.M.cryptolab_haetae_mode2_keypair_internal` caller under
the displayed canonical-region and disjoint-output premises.

The theorem composes:

- the exact 992-byte VK exporter trace;
- the exact 1408-byte SK exporter trace;
- the actual KeyGen caller trace; and
- the returned-array prefix theorem from the generated exporter composition.

The result is the actual caller claim:

```text
res = W64.zero /\
RawApiMuReachability.external_key_prefix_match Glob.mem sku0 vku0
```

This is the first week where the sequential export boundary is proved directly
for the real caller instead of a helper-only witness.

The first strengthened exact-trace proof used a single `proc; sim` while
requiring final `Glob.mem` equality. Fresh replay rejected it because the two
ghost observation assignments prevented automatic equality-set inference.
The compiled proof splits the common prefix from the exporter tail with
`seq 18 20`, then aligns the two actual copy calls under explicit
`={Glob.mem,dstp,srcp,len} ==> ={Glob.mem,res}` contracts. This preserves the
real exporter effects rather than abstracting the intermediate memory.

### Verify accept boundary — PROVED

`RawApiVerifyAcceptTrace` proves the exact early-reject tree:

```text
siglen <> 1474
  -> immediate reject
siglen = 1474
  -> unpack bad flag -> reject before tail
  -> norm rejection  -> reject before tail
  -> tail_reached and hash-input binding
     -> challenge mismatch -> reject after tail
     -> challenge match    -> accept
```

The accepted-path theorem surface is:

- `verify_full_m23_trace_accept_implies_tail_reached`
- `verify_raw_api_trace_accept_implies_tail_reached`
- `verify_cryptolab_trace_accept_implies_tail_reached`

and the corresponding input-binding theorems are:

- `verify_tail_trace_binds_hash_inputs`
- `verify_full_m23_trace_accept_binds_hash_inputs`
- `verify_full_mode2_trace_accept_binds_hash_inputs`
- `verify_internal_mode2_trace_accept_binds_hash_inputs`
- `verify_raw_api_trace_accept_binds_hash_inputs`
- `verify_cryptolab_trace_accept_binds_hash_inputs`

The actual caller lift is:

```text
actual_raw_verify_accept_binds_hash_inputs
```

which states that an accepted actual raw Verify execution exposes the tail
and the exact descriptor inputs:

- `vku = vku0`
- `preu = preu0`
- `prelen = prelen0`
- `mu = mu0`
- `mlen = mlen0`
- `siglen = 1474`

### Accepted-path hash-call adapter — PROVED

`RawApiAcceptedMuComposition.raw_api_accepting_execution_hash_mu_zero_loss`
is the accepted-path adapter that matters for the Week 5 boundary. It does
not claim equality of the two trace modules' stored `observed_mu` fields. It
does claim that the exact Sign trace observations and the exact accepted
Verify trace observations instantiate the generated hash-call theorem:

```text
equiv [Week3Sign._sf_mu_rawpre ~ Week3Verify.__verify_hash_mu :
  ...
  ==> ExtractedMuHashPrefix.mu32_prefix res{1} res{2}]
```

The theorem keeps the actual trace observations explicit:

- Sign-side observed SK and VK-byte length;
- Sign-side pre/message pointers and lengths;
- Verify-side `tail_reached`;
- Verify-side observed VK pointer and descriptor fields;
- canonical raw/pre-message region premises; and
- the raw prelength guard.

That is the strongest compiled statement for the accepted raw API path at the
hash-call level.

### Generated helper suffix adapter — PROVED

`RawApiAcceptedMuComposition.raw_api_accepting_execution_generated_challenge_suffix_zero_loss`
extends the accepted trace-bound premises to the generated Sign/Verify
challenge suffix helpers. This instantiates the position-64 helper
composition, but does not prove that the actual full callers reach the same
challenge-entry state.

The theorem needs:

- the same raw-key and Verify-tail accepted-path premises as above;
- `challenge_pos = 64`; and
- the actual generated helper modules.

Its conclusion is exact equality of the generated helper results, not a
public-API functional correctness claim.

## Diagram

```text
Actual KeyGen caller
  -> sequential export theorem PROVED
  -> external VK/SK prefix relation available

Actual Sign caller
  -> exact trace PROVED
  -> accepted-path hash-call adapter available
  -> direct sign-output frame/stability theorem still missing

Actual Verify caller
  -> siglen = 1474 gate
  -> unpack / norm / mismatch early-reject tree
  -> accepted path only
  -> tail_reached PROVED
  -> descriptor bindings PROVED
  -> accepted-path hash-call adapter PROVED
  -> generated helper suffix adapter PROVED

Open boundary
  -> direct mu32 equality on actual caller stored mu fields
  -> delta_mu_raw_api_accept = 0
```

## Exact premises and procedure boundary

| Result | Actual procedure surface | Premises retained in the compiled theorem |
| --- | --- | --- |
| KeyGen sequential export | `RawKeygenApiTarget.M.cryptolab_haetae_mode2_keypair_internal` | valid 32-byte seed read; canonical VK region of 992 bytes; canonical SK region of 1408 bytes; disjoint VK/SK output regions |
| raw Verify exact trace | `RawVerifyApiTarget.M._api_verify_mode2_raw` | equality of initial memory and all raw ABI arguments; no tail premise |
| cryptolab Verify exact trace | `RawVerifyApiTarget.M.cryptolab_haetae_mode2_verify_internal` | equality of initial memory and all public wrapper arguments; no tail premise |
| accept implies tail | actual full/internal/raw/cryptolab Verify and the matching trace | actual result is `W64.zero`; the trace equivalence itself has no accept or tail precondition |
| accepted hash binding | actual raw or cryptolab Verify and the matching trace | mode-2 signature length 1474 and equality of the caller VK/pre/message arguments; observations are concluded only under actual success |
| accepted generated mu adapter | actual generated `_sf_mu_rawpre` and `__verify_hash_mu` | canonical/no-wrap VK address; common hash-memory snapshot; imported SK prefix; external VK/SK prefix match; caller-trace observations; mode-2 length 992; equal pre/message pointers and lengths; `raw_prelen`; valid pre/message regions |
| generated suffix adapter | generated hash calls followed by generated mu32 absorb helpers | the preceding mu premises plus equal challenge state/position and position 64 |

The KeyGen theorem is partial correctness. The Verify acceptance theorems are
conditional event implications. No theorem assumes KeyGen termination or
asserts that every signature reaches the tail.

## Alias, ownership, and cross-call stability

| Buffer pair | Classification for the Week 5 sequence | Reason |
| --- | --- | --- |
| `vku` / `sku` | MUST-DISJOINT | the SK export must frame the earlier 992-byte VK export |
| `seedu` / `vku` or `sku` | MAY-ALIAS-BECAUSE-COPIED-FIRST | KeyGen imports all seed bytes before writing either output; the initial seed read must still be valid |
| `sku` / `sigu` | MUST-DISJOINT for key reuse | local Sign import occurs first, but later composition still needs the exported SK stable |
| `sku` / `siglenu` | MUST-DISJOINT for key reuse | the final length write may otherwise corrupt the reusable SK buffer |
| `vku` / `sigu` or `siglenu` | MUST-DISJOINT for Sign-to-Verify composition | Verify must read the KeyGen-exported VK after Sign publishes its output |
| `sigu` / `siglenu` | MUST-DISJOINT | the length publication must not corrupt the signature |
| `preu` / message | READ-ONLY-ALIAS-ALLOWED | both are read streams; equality and lengths define the intended transcript |
| `rndu` / `sigu` | MAY-ALIAS-BECAUSE-COPIED-FIRST | Sign copies randomness before signature publication |
| `preu` or message / `sigu` | MAY-ALIAS locally; MUST-DISJOINT for reuse | local mu reads occur first, but Verify later needs the same transcript bytes |

All unlisted pairs remain `UNKNOWN`. EasyCrypt's total `global_mem_t` is not
a memory-safety proof. Cross-call stability is an experiment/runtime contract
until a Sign-output frame theorem derives it from the displayed disjointness.

## Specified functional obligation

The following is a theorem signature for later work, not a compiled Week 5
lemma and not a premise of the accepted-path results:

```easycrypt
hoare [LegitimateRawSignVerifyTrace.run :
  canonical_and_valid_regions /\
  sign_uses_keygen_exported_sk /\
  verify_uses_keygen_exported_vk /\
  same_pre_message /\
  sign_execution_returns_success
  ==>
  verify_tail_reached]
```

This is `OBL-SIGN-OUTPUT-TAIL-REACH`. It depends on signature pack/unpack
inverse and the norm-gate facts. `OBL-SIGN-VERIFY-CORRECTNESS` additionally
depends on response, hint, arithmetic, and final challenge equality.

## Reachability and non-vacuity

- The address/region contracts are jointly satisfiable by the existing
  adjacent-region witness, and `raw_prelen` has the concrete zero-length
  witness. The actual KeyGen theorem supplies the external prefix relation on
  every terminating execution.
- The accept-to-tail Hoare precondition is `true`; no contradictory tail
  premise is used. Week 5 does not construct a concrete accepted signature,
  so reachability of the accept antecedent remains tied to the separate
  functional-correctness lane. The implication is nevertheless the correct
  security-facing event inclusion used conditionally on a forgery success.
- The accepted generated hash adapter has satisfiable memory/address
  premises, but a single actual Sign-to-Verify execution has not yet been
  shown to preserve them across the Sign output writes. This is why the
  parent remains partial.
- No authored axiom, abstract SHAKE-prefix rule, boolean residual placeholder,
  or Week 5 `stores mem 0 ...` API witness supplies any of these edges.

## Failed approaches and residuals

- A one-sided Sign continuation/losslessness approach was not promoted. The
  direct relational attempt would require losslessness of the signing
  rejection continuation in order to discard it against the finite Verify
  continuation. That losslessness is unproved. The exact Sign trace theorem
  is compiled, but it also does not provide the missing Sign-output
  frame/stability theorem needed to connect the actual caller trace state
  directly to the Verify acceptance trace.
- The accepted-path adapter does not use a `stores mem 0` witness. It reuses
  the actual trace observations and the existing generated hash theorem.
- The challenge-suffix theorem stops at the generated helper boundary. It
  still needs actual Sign-core/Verify-tail challenge-entry state and the
  `challenge_pos = 64` premise.

## Implications

- `OBL-API-KEY-MEMORY-RAW-ACCEPT` remains partial because the actual caller
  trace modules are not yet connected by a direct stored-mu equality.
- `OBL-SIGN-OUTPUT-TAIL-REACH` must be solved before `OBL-SIGN-VERIFY-CORRECTNESS`
  can move from blocked to proof work.
- `delta_mu_raw_api_accept = 0` is **not** recorded. The report only records
  the accepted-path hash-call adapter and the generated helper suffix
  adapter.
- The compiled week-5 boundary is narrow: actual caller KeyGen export,
  accepted Verify tail reach, and the generated helper suffix chain. It does
  not include public full-caller correctness or a Sign-output acceptance
  theorem.

## Verification record

The pre-edit Week 5 baseline was preserved verbatim in
`logs/week5-baseline-summary.txt`:

```text
RESULT PASS authored-targets=19 cache=-no-eco
```

The final integrated command was:

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

Its final summary in `logs/verify-all-summary.txt` is:

```text
PASS source drift
PASS proof-hole scan
PASS proof target manifest
PASS authored axiom scan
PASS debug/temporary declaration scan
PASS focused extraction regeneration drift
PASS fresh compile ... RawApiKeygenSequentialExport.ec
PASS fresh compile ... RawApiVerifyAcceptTrace.ec
PASS fresh compile ... RawApiAcceptedMuComposition.ec
PASS baseline verification
PASS LaTeX research notes build
PASS read-only roots unchanged after verification
RESULT PASS authored-targets=22 cache=-no-eco
```

The selected read-only baseline reports
`RESULT PASS selected-baselines=20 read-only=true`. `latex/main.pdf` contains
19 A4 pages. The undefined-reference/citation/error scan is empty. The Week 5
sections introduce no overfull boxes; older Week 1--4 sections retain their
historical long-identifier warnings. No new dependency was installed.
