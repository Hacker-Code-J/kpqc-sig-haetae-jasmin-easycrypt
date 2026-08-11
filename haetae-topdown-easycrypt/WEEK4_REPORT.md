# Week 4 report — raw ABI key-memory reachability

## Outcome

Week 4 made the external-buffer boundary substantially more concrete, but did
not close `OBL-API-KEY-MEMORY-RAW`. Its evidence-based status is **PARTIAL**.
Highbits/LSB work therefore remains a no-go for the next sprint.

The completed part no longer constructs a memory with `stores mem 0 ...`:
`RawApiMuReachability.raw_api_key_memory_reaches_mu_zero_loss` consumes an
actual external memory, a Sign importer postcondition, external VK/SK byte
agreement, and a canonical address. It derives the exact
`sk_memory_prefix` premise used by the Week 3 generated hash theorem.

The parent remains open for two independent reasons:

1. the real KeyGen caller's two exporter calls have exact control and isolated
   procedure theorems, but their single sequential Hoare postcondition did not
   finish normalization in EasyCrypt;
2. the Verify raw/public caller may reject during signature unpacking or norm
   checks before `_sign_verify_tail_m23` calls `__verify_hash_mu`. No theorem
   yet proves that a corresponding Sign output reaches that branch.

Consequently `delta_mu_raw_api = 0` is **not claimed**. The already proved
`delta_mu_raw_top = 0` remains valid only below these caller-reachability
gates.

## Baseline and extraction

Before Week 4 edits, `scripts/verify-all.sh` passed with 14 authored targets
and 20 selected read-only baselines. The preserved summary is
`logs/week4-baseline-summary.txt`.

The new focused extraction roots are the actual ABI procedures:

| Role | Procedure | Generated target | SHA-256 |
| --- | --- | --- | --- |
| KeyGen | `cryptolab_haetae_mode2_keypair_internal` | `RawKeygenApiTarget.ec` | `70716a5cf03d343b958e90ed070940739391c88c93e29bb687b2b64636df4565` |
| Sign | `cryptolab_haetae_mode2_signature_internal` | `RawSignApiTarget.ec` | `5f632a19c7db616ca75f4f2f0b319b1a8ba821f0bd552613f0c77290b19ef02f` |
| Verify | `cryptolab_haetae_mode2_verify_internal` | `RawVerifyApiTarget.ec` | `b745f8919f2ce8c2ff80e63a2330da6cdcc6cad414f341fe90081b886825142b` |

The generated closures contain the requested exporters/importers, internal
mode-2 callers, `_sf_mu_rawpre`, `_sign_verify_tail_m23`, and
`__verify_hash_mu`. Regeneration and hash checks are integrated into
`verify-all.sh`.

## Fresh-compiled Week 4 theorems

### Address correspondence — PROVED

`RawApiAddressBridge` defines exactly:

```easycrypt
canonical_ui64_address a = 0 <= a < W64.modulus
canonical_region a n = 0 <= a /\ 0 <= n /\ a + n <= W64.modulus
```

The following compile without axioms:

- `canonical_ui64_address_roundtrip`:
  `canonical_ui64_address a => W64.to_uint (W64.of_int a) = a`;
- `canonical_region_valid_region_int`;
- `canonical_region_valid_region_w64`;
- `importer_exporter_address_equality` and
  `importer_addr_to_exporter_w64`;
- `mode2_vk_region_bridge`, `mode2_sk_region_bridge`, and
  `mode2_sig_region_bridge` for 992, 1408, and 1474 bytes.

Thus `OBL-API-ADDRESS-BINDING` is **PROVED**. Equality is deliberately confined
to the canonical range; modular reduction outside it is not ignored.

### KeyGen raw caller — PARTIAL

Compiled facts include:

- exact pRHL identity for the raw-closure and helper-closure exporter
  procedures;
- `raw_keypair_internal_mode2_return_prefix` for the actual raw extraction's
  mode-2 internal KeyGen;
- `raw_keygen_export_vk_mode2_prefix`;
- `raw_keygen_export_sk_mode2_prefix_frames_vk`;
- `keypair_raw_api_exact_export_trace`, whose left procedure is the actual
  `Raw.cryptolab_haetae_mode2_keypair_internal` and whose postcondition proves
  equality of the actual and trace memories;
- `keypair_raw_api_exports_matching_prefixes_from_copy_posts`, which composes
  the real exporter postconditions and the returned-array prefix theorem.

The attempted single Hoare theorem over the actual caller reached the final
post-export continuation but repeatedly stalled while normalizing the large
existential/array postcondition. Replacing it with a proof-only constructed
memory would violate this sprint's goal, so the exact residual is named
`keypair_raw_api_exports_matching_prefixes_residual`. Therefore
`OBL-API-KEYGEN-EXPORT-CALLER` is **PARTIAL**, not PROVED.

### Sign raw caller — PROVED to a trace mirror

`RawApiCallerMuTrace` fresh-compiles:

- `sign_internal_exact_mu_trace`;
- `sign_raw_api_exact_mu_trace`, directly comparing the actual
  `cryptolab_haetae_mode2_signature_internal` with a trace-carrying mirror and
  preserving final memory and return value;
- `sign_raw_import_mode2_sk_prefix`, which proves the 1408-byte import and the
  992-byte prefix used by mu;
- `sign_raw_api_trace_imports_mode2_sk`;
- `sign_raw_api_trace_binds_hash_inputs`, fixing `vkbytes=992` and passing the
  raw API's pre/message addresses and lengths unchanged.

The mirror executes the actual `_sf_signature_core_mode2` continuation and
preserves the original result component; it is not an independent observer
that stops after hashing. This closes the Sign-side trace boundary, conditional
on the displayed valid-region and external-memory stability contracts.

### Verify caller — PARTIAL

`RawApiVerifyMuTrace` fresh-compiles exact refinements for:

- `_sign_verify_tail_m23` to `VerifyTailMuTrace.run`;
- `_verify_full_m23` to `VerifyFullM23MuTrace.run`;
- `_verify_full_mode2` to `VerifyFullMode2MuTrace.run`;
- `sign_verify_internal_mode2_jazz` to
  `VerifyInternalMode2MuTrace.run`.

It also compiles the 992-byte VK importer theorem and descriptor/raw-prelen
binding. The lift through `_api_verify_mode2_raw` and
`cryptolab_haetae_mode2_verify_internal` remains named by
`verify_raw_api_exact_mu_trace_residual_obligation` and
`cryptolab_verify_internal_exact_mu_trace_residual_obligation`. The blocker is
semantic, not a missing hash helper: `siglen=1474` is necessary but not
sufficient because unpacking, norm rejection, and the final mismatch path may
return before the tail.

### Stores-free key-memory bridge — PROVED conditionally

`RawApiMuReachability` fresh-compiles:

- `raw_sign_hash_extraction_identity` and
  `raw_verify_hash_extraction_identity`, proving that the raw-ABI and focused
  hash extractions are interchangeable by pRHL, rather than by name;
- `stable_region_refl`, `stable_region_trans`, and
  `external_prefix_survives_stability`;
- `raw_api_key_memory_reaches_mu_zero_loss` and
  `raw_api_region_reaches_mu_zero_loss`.

The core theorem's premises are:

```text
canonical_ui64_address(vku)
imported_prefix(sk_local, mem, sku, 992)
external_key_prefix_match(mem, sku, vku)
```

and its conclusion is:

```text
W64.to_uint(W64.of_int(vku)) = vku
and sk_memory_prefix(sk_local, mem, W64.of_int(vku)).
```

This exactly supplies the Week 3 generated mu theorem's key-memory premise,
but it does not itself prove that the unresolved KeyGen/Verify public callers
reach those premises.

## Alias and ownership matrix

The labels distinguish source-ordered copying from conservative cross-call
ownership. `MUST-DISJOINT` below means necessary for the stated multi-call
claim, not necessarily rejected by the Jasmin machine semantics.

| Buffer pair | Classification | Reason |
| --- | --- | --- |
| `vku` / `sku` | MUST-DISJOINT | SK export must preserve the earlier 992-byte VK export. |
| `seedu` / `vku` | MAY-ALIAS-BECAUSE-COPIED-FIRST | KeyGen imports all 32 seed bytes before either output write; caller still owes a valid initial seed read. |
| `seedu` / `sku` | MAY-ALIAS-BECAUSE-COPIED-FIRST | Same source-order argument as above. |
| `sku` / `sigu` | MAY-ALIAS-BECAUSE-COPIED-FIRST locally; MUST-DISJOINT for key reuse | Sign imports SK and computes mu/core before exporting the signature, but a later Verify/composition needs the key buffer stable. |
| `sku` / `siglenu` | MAY-ALIAS-BECAUSE-COPIED-FIRST locally; MUST-DISJOINT for key reuse | The 8-byte length write occurs after signing; it can destroy a reusable SK. |
| `vku` / `sigu` | MUST-DISJOINT for the composed Sign→Verify experiment | Signature export must not overwrite the VK later read by Verify. |
| `vku` / `siglenu` | MUST-DISJOINT for the composed experiment | Same cross-call stability requirement. |
| `preu` / `message` | READ-ONLY-ALIAS-ALLOWED | Hashing reads both regions; equality/length premises describe the intended byte streams. |
| `rndu` / `sigu` | MAY-ALIAS-BECAUSE-COPIED-FIRST | Sign copies randomness before signature output. |
| `rndu` / `sku` | READ-ONLY-ALIAS-ALLOWED for one Sign call | Both are imported/read before output, subject to valid ranges. |
| `preu` or `message` / `sigu` | MAY-ALIAS-BECAUSE-COPIED-FIRST for local mu; MUST-DISJOINT for cross-call reuse | Signature output occurs after mu/core reads, but later Verify needs stable transcript bytes. |
| `sigu` / `siglenu` | MUST-DISJOINT | The final length write must not corrupt the exported signature. |

All unlisted pairs remain `UNKNOWN` unless the source-order proof or a caller
contract above covers them. EasyCrypt's total `global_mem_t` is not interpreted
as a C/Jasmin memory-safety theorem.

Cross-call stability belongs in the experiment/caller contract: after KeyGen,
both key regions must remain stable until the corresponding Sign import and
Verify VK read; after Sign, pre/message and VK plus the produced signature must
remain stable until Verify consumes them.

## Failed approaches and non-vacuity

- A direct KeyGen caller Hoare proof successfully used the actual internal
  KeyGen theorem and both exporter frame theorems, but the last `auto`/`wp`
  normalization over the generated local arrays did not terminate in bounded
  runs. It was not replaced by `stores mem 0 ...`.
- Three Verify public-lift decompositions (`sim`, explicit call alignment, and
  trace-state reshaping) stopped above the early-reject control flow. An
  unconditional hash-reach theorem would be false without a tail-reach
  premise.
- The final stores-free bridge is satisfiable: the existing adjacent-region
  witness supplies valid/disjoint key regions, canonical round-trip lemmas
  have concrete 992/1408/1474 instances, and `stable_region mem mem` is proved.
- No new axiom, `admit`, `abort`, `sorry`, or SHAKE idealization was added.
- A local implication theorem is not promoted to public-ABI reachability;
  hence the parent stays PARTIAL and no `delta_mu_raw_api=0` is recorded.

## Verification record

The final integrated command is:

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

It checks raw extraction drift, every manifested target with `-no-eco`, proof
holes, authored axioms, debug declarations, target completeness, source/read-
only drift, selected baselines, actual-caller theorem surfaces, absence of a
constructed Week 4 `stores mem 0` witness, and the LaTeX build. The definitive
counts and result are in `logs/verify-all-summary.txt`:

```text
PASS baseline verification
PASS LaTeX research notes build
PASS read-only roots unchanged after verification
RESULT PASS authored-targets=19 cache=-no-eco
```

The managed Codex filesystem sandbox terminates a Why3 server started as a
background child, so a sandboxed self-start attempt failed before any proof
check.  The complete self-contained command above was therefore rerun through
the already approved unsandboxed verification prefix and passed.  An
independent run using an explicitly supplied live `WHY3_SERVER_SOCKET` also
passed all of the same checks.  This is an execution-environment distinction,
not an EasyCrypt proof failure.

## Go/no-go for Week 5

**No-go for highbits/LSB.** Week 5 should stay on actual caller reachability:

1. redesign the KeyGen sequential export proof boundary so the final caller
   Hoare postcondition does not trigger whole-array WP normalization;
2. formulate and prove a tail-reach predicate for Sign-produced, canonically
   packed signatures, or instrument `_api_verify_mode2_raw` with an exact trace
   that preserves early-reject results while recording whether the tail ran;
3. compose the exact Sign caller trace, key-buffer stability, Verify descriptor
   binding, and Week 3 generated hash theorem only after both lifts compile.

If the next attempt again cannot lift the actual callers, the extraction and
trace-instrumentation strategy must be redesigned rather than adding another
helper-only wrapper.
