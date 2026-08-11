# Assumptions, contracts, and proof obligations

## Permitted final cryptographic assumptions

- **MLWE:** hardness of the concrete HAETAE-2 public-key game instance.
- **BST-MSIS:** hardness of the concrete balanced/self-target module-SIS
  instance produced by the exact extraction theorem.
- **ROM:** the explicitly domain-separated random-oracle game used by the
  paper reduction.

These are interfaces in `easycrypt/security/SecurityAssumptions.ec`. Declaring
an interface neither instantiates its game nor proves the reduction.

## Idealizations

- uniform independent random tape only at explicitly modeled RNG calls;
- random-oracle idealization only after byte transcripts/domains are proved;
- real/ideal FFT comparison only through an explicit numerical-error relation
  and bad event.

No SHAKE-output-prefix idealization was introduced in Weeks 2 or 3. The mu theorem
uses the extracted Keccak, absorb, finalize, and squeeze procedures.

## Runtime/API contracts

- valid, sufficiently sized public buffers and descriptors;
- separation only where a later write must preserve an earlier exported
  region; read-only import calls do not require mutual separation merely for
  proof convenience;
- no harmful input/output aliasing at still-uncomposed public call sites;
- canonical lengths and mode-2 constants;
- RNG availability and deterministic interpretation of fixed random tape;
- retry termination/losslessness.

These are not cryptographic assumptions. They are public-API refinement
premises or separate memory-safety/termination theorems.

`canonical_region(a,n)` alone permits the boundary case `a = 2^64, n = 0`.
Accordingly, any theorem that needs the exact conversion
`W64.to_uint(W64.of_int a) = a` also requires
`canonical_ui64_address(a)` (and likewise for an integer length). Week 6 does
not infer this round trip from a possibly empty region.

## Week 2 closed obligations

- `OBL-SKPK-PREFIX-CALL`: **PROVED as Hoare partial correctness** for generated
  `_pack_sk_m23`, `_keypair_full_m23`, and the mode-2 internal entry. It does
  not claim termination.
- `OBL-HASH-MEM-BRIDGE-LOCAL`: **PROVED** for a concrete Verify memory made by
  storing the returned packed VK and the matching Sign packed-SK prefix.
- `OBL-MU-SQUEEZE-PREFIX`: **PROVED** for the generated Sign 64-byte and Verify
  32-byte squeeze implementations, including little-endian byte order.
- `OBL-MU-RAW-HELPERS`: **PROVED** for the full generated helper chain inside
  explicit raw top wrappers.
- `OBL-MU-CHALLENGE-SUFFIX`: **PROVED with zero loss** for those raw wrappers
  followed by the generated position-64 mu32 absorb procedures.

## Week 3 status and remaining named proof obligations

- `OBL-MU-TOPLEVEL-CONTROL`: **PROVED for the raw/internal path** by the two
  exact-to-wrapper adapters and `sign_verify_generated_raw_mu_prefix`.
- `OBL-MU32-HASH`: **PROVED for raw/internal generated calls**; public context
  and public API memory marshalling are deliberately not included.
- `OBL-MU32-HASH-CONTEXT`: context-path encoding and high-bit branch.
- `OBL-API-KEY-MEMORY-RAW`: **PARTIAL**. The actual generated KeyGen VK/SK
  exporters and Sign/Verify raw importers have compiled prefix theorems, and
  the disjoint SK-write frame preserves an already exported VK region. Local
  byte adapters reach `sk_memory_prefix`. Remaining work is actual-caller
  composition of both exports, concrete `W64.to_uint` exporter-address to the
  generated importer `int` binding, and public caller ownership/alias
  orchestration.
- `OBL-FIPS202-TRANSCRIPT`: complete paper-level byte transcript, domain,
  padding, endianness, and ROM-query correspondence. Week 2 proves the local
  generated-procedure equality, not the full paper adapter.
- `OBL-HIGH-LSB-PACK`: exact Sign/Verify highbits and LSB packed bytes.
- `OBL-KG-TERMINATION`, `OBL-KG-DIST`: retry losslessness, actual KeyGen
  distribution, and singular rejection effect.
- `OBL-FFT-TAIL`, `TieMin`: numerical error probability and tied-minimum
  mismatch policy.
- `OBL-SIGN-ACCEPTED-DIST`: accepted-output distribution and statistical loss.
- `OBL-CHALLENGE`: support, cardinality, point probability, and min-entropy.
- `OBL-FORK`: two fresh transcripts extract the exact BST-MSIS instance.
- `OBL-PACK-CANON`: packing/parsing round trips and malformed rejection.
- `OBL-VERIFY-EVENT`: Jasmin accept iff the paper forgery predicate accepts.
- `OBL-SIGROM-ADAPTER`: exact public APIs instantiate the security scheme.

None is hidden behind a newly authored implementation axiom.

## Trusted computing base

- EasyCrypt kernel/type checker and imported standard libraries;
- Why3 and the invoked SMT provers;
- Jasmin parser/compiler and `jasmin2ec` translation;
- pinned Jasmin, generated extraction, and reused EasyCrypt artifacts;
- host filesystem/hash/LaTeX tools used by reproduction scripts.

Extraction compilation shows translation acceptance. Semantic trust in
`jasmin2ec` remains in the TCB unless separately validated.

## Separate auxiliary tracks

Memory safety, SCT/constant-time, cache/power/EM leakage, fault resistance, and
physical RNG quality are not consequences of EUF-CMA. They remain separate
claims.

## Non-vacuity policy and Week 2 check

- No total-correctness claim may depend on a hidden progress witness.
- KeyGen prefix theorems are explicitly partial correctness; termination is
  not smuggled into a precondition.
- Week 8 HBZ results are success-conditioned partial correctness only:
  canonical HBZ inputs do not imply that the fixed 1024-byte rANS buffer
  always succeeds. Any final HBZ round-trip theorem must expose the actual
  encoder-success branch (`size <> 0`) or an equivalent disjunction, rather
  than treating nonzero size or decoder success as an assumption.
- Mode-2 rANS table compatibility is not an assumption:
  `actual_mode2_hbz_tables_certified` fresh-compiles against the literal
  `esyms`, `symbol_words`, and `dsyms_words` arrays.  The deterministic
  generator merely emits proof text and remains outside the logical TCB
  because EasyCrypt rechecks every generated leaf.
- The compiled pure fast-step inverse does not idealize the generated loops.
  Reverse normalization-byte publication, forward consumption, final-state
  equality, consumed-size equality, and the `size = 0` branch remain named
  implementation proof obligations.
- The all-zero HBZ witness establishes only leaf-premise satisfiability.  No
  actual successful full encoder/decoder witness has yet been proved, so the
  parent success-conditioned theorem is not treated as non-vacuous evidence.
- Week 9's `valid_rans_trace` is a defined pure object, not an assumption.
  The actual encoder must derive it in a postcondition before the decoder may
  consume it; no theorem accepts trace validity as an external premise for the
  full core composition.
- Week 10's `symbol_list_of_array`, `segment_matches`, `prefix_frame`, finite
  encoder phase, concrete word-step operation, and LE-store operation are
  definitions verified by EasyCrypt lemmas, not axioms.  In particular,
  `encoder_inner_segment_inv` is installed inside a Hoare proof of the actual
  generated `_rans_encode`; it is not an assumed trace relation.
- The current actual inner phase bound `0..4` follows only from W32 finiteness
  and positive `x_max`.  It must not be silently identified with the stronger
  pure mode-2 `0..2` normalization trace until the actual outer invariant binds
  its entry state and symbol to `encode_trace`.
- `actual_rans_encode_success_size_bound` is partial correctness.  It keeps the
  returned failure disjunct and says nothing about termination or reachability
  of actual success.  The all-6 success witness therefore remains an open
  proof obligation, not a runtime or cryptographic assumption.
- Exact equality between the returned actual byte suffix and
  `trace_bytes(symbol_list_of_array(symbols0))` is a compiled Week 11
  postcondition, not an assumption. Week 12 consumes the same mathematical
  trace only under an explicit decoder-buffer relation.
- The actual suffix-copy theorem assumes explicit integer bounds
  `0 <= off`, `0 <= n`, and `off+n <= 2048`.  Deriving these bounds from the
  actual encoder's success result remains an implementation obligation, not a
  runtime idealization.
- The older encoder/decoder control theorems prove only concrete parameter
  binding and `bad in {0,1}`. They are not cited as semantic refinements.
  The later direct Hoare theorems separately prove exact encoder suffix output
  and exact-trace decoder recovery; neither proves losslessness or termination.
- `Mode2RansActualHarness` branches on the returned encoder `bad` and therefore
  does not assume encoder success. Its decoder branch is reachable only
  conditionally; an EasyCrypt witness for that branch remains open as
  `OBL-RANS-ACTUAL-SUCCESS-WITNESS`.
- `keygen_prefix_reaches_mu_memory` constructs the helper-level memory premise.
- `mode2_base_zero_no_wrap` proves a concrete address premise is satisfiable.
- A security inequality with loss at least one is recorded as vacuous.
- Challenge well-formedness is not support/cardinality/min-entropy.
- The structural `HAETAE_Algebra.challenge_hash` ignores its highbits argument,
  so it is not accepted as the byte-faithful challenge target.

## Week 3 non-vacuity and zero-loss boundary

- `raw_prelen_zero` is a concrete witness, while
  `raw_prelen_shr63_zero` proves the exact word shift used by Verify is zero.
- `keypair_internal_return_reaches_generated_raw_mu_preconditions` consumes
  the actual generated internal KeyGen return theorem and constructs the joint
  no-wrap/raw/memory premises; the generated cross-procedure theorem is not
  justified by a generic hash-output witness. This remains partial correctness
  and does not assert KeyGen termination.
- `valid_region_w64 W64.zero (W64.of_int 992)` and
  `valid_region_int 0 1408` are concrete witnesses for the two API address
  models. The selected KeyGen exporter extraction retains `W64.t`, whereas
  the selected Sign/Verify `ui64` importer parameters are translated to
  mathematical `int`; the missing call-site bridge must relate them rather
  than assume them equal.
- `disjoint_regions` is consistent (for example, adjacent VK/SK regions), but
  it is needed only when sequential writes must preserve both exported
  regions. Stronger all-buffer separation is neither proved nor adopted as a
  cryptographic assumption. Aliasing across unextracted public callers remains
  unanalyzed and explicit.
- `delta_mu_raw_top = 0` denotes only the actual generated raw mu procedures
  followed by the position-64 mu32 challenge absorb. It is not promoted to
  `delta_Sign`, `delta_Verify`, `delta_Encoding`, or the public-context path.

## Week 4 historical snapshot (superseded by Week 5)

The statuses in this subsection record the end-of-Week-4 boundary.  Current
statuses are stated in the Week 5 subsection below.

- `OBL-API-ADDRESS-BINDING`: **PROVED** under
  `canonical_ui64_address`/`canonical_region`. This is an arithmetic pointer
  representation theorem, not a physical memory-safety theorem.
- `OBL-API-KEYGEN-EXPORT-CALLER`: **PARTIAL at Week 4; PROVED in Week 5**.
  At the Week 4 boundary, the actual raw caller was exactly related to a trace,
  its internal return prefix was proved, and both exporters had prefix/frame
  theorems, while the single sequential caller Hoare postcondition was still
  open. Week 5 discharges that exact postcondition.
- `OBL-API-SIGN-MU-REACHABILITY`: **PROVED through an exact trace refinement**.
  The caller contract still requires a valid SK region and stable key,
  pre/message, randomness, signature and length regions according to the
  Week 4 alias matrix.
- `OBL-API-VERIFY-MU-REACHABILITY`: **PARTIAL at Week 4; PROVED on the
  accepted/tail path in Week 5**. Internal exact trace theorems do not imply
  that every raw Verify call executes `__verify_hash_mu`;
  unpack/norm/mismatch gates can reject first. Tail reach is a proof
  obligation, not an assumption.
- `OBL-API-KEY-MEMORY-RAW`: **PARTIAL at Week 4; SPLIT in Week 5**. The stores-free theorem
  `raw_api_key_memory_reaches_mu_zero_loss` proves that actual external-memory
  facts imply the Week 3 hash premise. It does not manufacture those facts or
  discharge the two caller residuals.
- Cross-call key-buffer stability is a runtime/experiment contract: neither
  the environment nor Sign outputs may change `[vku,vku+992)` or the SK bytes
  before their corresponding reads. This is separated from local
  source-order alias permissions such as seed/output and randomness/signature
  aliasing after the inputs have been copied.
- `delta_mu_raw_api = 0` remains unavailable. Only the previously proved
  `delta_mu_raw_top = 0` may be used until the actual caller residuals close.

## Week 5/6 accepted-path contracts and residual obligations

- `OBL-API-KEYGEN-EXPORT-CALLER`: **PROVED as partial correctness**.  The
  actual raw caller establishes `external_key_prefix_match Glob.mem sku vku`
  for every returning execution under a valid seed read, canonical VK/SK
  regions, and disjoint output regions.  Retry termination remains
  `OBL-KG-TERMINATION`, not a premise disguised as progress.
- `OBL-API-VERIFY-TRACE`: **PROVED**.  The raw and cryptolab exact trace
  equivalences preserve both the actual return value and final `Glob.mem` on
  all branches.  Ghost observations are meaningful only when
  `tail_reached` holds.
- `OBL-API-VERIFY-ACCEPT-TAIL`: **PROVED**.  Wrong length, unpack failure, and
  norm failure return nonzero before the tail; challenge mismatch returns
  nonzero after the tail.  Therefore success (`W64.zero`) implies
  `tail_reached`.  Neither `siglen=1474` nor an arbitrary signature implies
  tail reach.
- `OBL-API-VERIFY-MU-REACHABILITY`: **PROVED on the accepted/tail path**.
  Accepted traces bind the exact VK/pre/message pointers and lengths passed to
  `__verify_hash_mu`.  `raw_prelen`, canonical addresses, and valid regions
  remain explicit composition contracts.
- The former `OBL-API-KEY-MEMORY-RAW` is **SPLIT**, not silently weakened.
  `OBL-API-KEY-MEMORY-RAW-ACCEPT` remains **PARTIAL** until a compiled theorem
  directly relates `SignRawApiMuTrace.observed_mu` and
  `VerifyCryptolabMuTrace.observed_mu`. The exact Sign output frame and
  region-local generated hash relation are proved in Week 6; they are not
  assumptions. The remaining gap is the product/replay connection from two
  completed trace calls to their stored observation fields.
- `OBL-SIGN-OUTPUT-TAIL-REACH` is a separate **SPECIFIED** functional
  obligation.  It requires pack/unpack inverse, norm, hint, response, and
  arithmetic correctness.  It is not an axiom and is not a premise of the
  accepted-forgery path.
- `OBL-SIGN-VERIFY-CORRECTNESS` remains **BLOCKED** until that functional lane
  and the final challenge comparison are proved.
- Cross-call stability is a runtime/refinement contract over concrete memory
  snapshots: the key buffers must keep the KeyGen-exported bytes until Sign
  and Verify read them, and signature/pre/message buffers must remain stable
  across their designated reads. The actual raw Sign caller now discharges
  its VK/SK/pre/message stability from explicit output disjointness. External
  mutation between separate ABI invocations remains a runtime contract.
- No Week 5 or Week 6 API theorem uses a constructed `stores mem 0 ...`
  witness. The older local witness remains historical evidence for the
  generated-array seam only.
- `delta_mu_raw_api_accept = 0` is **not yet available**.  What is proved with
  zero deterministic loss is narrower: accepted caller trace facts
  instantiate the actual generated hash-call mu-prefix theorem and the
  generated position-64 challenge-suffix helper theorem.  This is not a full
  Sign/Verify, encoding, or EUF-CMA delta.

## Week 7 additions

- `OBL-MU-PRODUCT-REPLAY` is not converted into an assumption. The Week 7
  result is an explicit paper boundary, not a hidden replay axiom.
- `canonical_challenge` and `canonical_signed_low` are functional input
  invariants for the mode-2 signature prefix codec, not cryptographic
  assumptions.
- `prefix_codec_preconditions_satisfiable` proves those functional invariants
  are jointly satisfiable, and the actual `_pack_sig_prefix` /
  `_unpack_sig_prefix` round trip now compiles as partial correctness. This
  does not assume or prove Sign termination.
- The unpack low-array tail frame is proved. Pack/challenge array-tail frames,
  metadata reconstruction, canonical zero padding, and hbz/h suffix inverses
  remain separate proof obligations and are not assumed implicitly.
- No codec result establishes zero loss for `delta_Encoding`: malformed-reject
  completeness, full canonical parsing, norm, hint, and arithmetic relations
  remain open.

## Week 11 encoder boundary

- Exact successful encoder suffix equality is no longer an assumption or open
  adapter: `actual_rans_encode_trace_closure` proves it directly for generated
  `RansEncodeTarget.M._rans_encode` under the concrete mode-2 table and
  canonical 1024-symbol premises.
- The theorem is Hoare partial correctness. It does **not** assume success,
  but it also does not establish local losslessness, termination, or that the
  success disjunct has an actual terminating witness. Those remain proof
  obligations, not cryptographic assumptions.
- `mode2_hbz_symbol_stream` is a functional representation precondition over
  the actual input array. Concrete table identity is discharged by the pinned
  generated target and table certificate; it is not an authored axiom.
- Actual decoder trace consumption, the encoder→copy→decoder inverse, full
  HBZ wrapper composition, canonical parsing, and encoding/security deltas
  remain open. No Week 11 result is promoted to a security zero-loss claim.

## Week 12 decoder boundary

- `actual_rans_decode_trace_refinement` proves semantic recovery for the
  actual generated `RansDecodeTarget.M._rans_decode`; decoder correctness is
  no longer supplied by the old control-only theorem or by an assumption.
- `actual_mode2_decoder_trace_input` is a functional representation contract:
  it binds a canonical 1024-symbol array, the exact `trace_bytes` buffer,
  encoded-size bounds, state fields `(1024, encoded_size, 13)`, and the actual
  mode-2 decode tables. It does not contain decoder success, output equality,
  or a post-state observation.
- The theorem is Hoare partial correctness. It proves that every terminating
  exact-trace execution returns `bad=0`, consumes exactly `encoded_size`,
  recovers the 1024 symbols, and preserves the output tail. It proves neither
  termination nor losslessness.
- The exact input relation is satisfiable as a pure/array trace relation and
  is the relation produced mathematically by the Week 11 encoder success
  theorem. This does not establish that the actual encoder success branch is
  reachable; `OBL-RANS-ACTUAL-SUCCESS-WITNESS` remains `PARTIAL`.
- `OBL-RANS-CORE-INVERSE` remains `PARTIAL` until an actual unary harness
  transports the encoder segment and actual copy-helper result into every
  decoder byte-read premise. This is an implementation composition
  obligation, not a trusted adapter.
- No Week 12 result implies the full HBZ wrapper inverse, canonical parsing,
  zero implementation encoding loss, Sign losslessness, or any EUF-CMA bound.

## Week 13 core-composition boundary

- `OBL-RANS-CORE-INVERSE` is **PROVED as success-conditioned Hoare partial
  correctness**. The theorem's precondition contains only exact harness
  argument binding and `mode2_hbz_symbol_stream`; encoder success, decoder
  success, copied-buffer equality, and decoded equality are derived after the
  actual calls rather than assumed.
- The decoder pointwise read relation is no longer an external composition
  premise. `segment_matches_implies_exact_decoder_segment_input` proves it
  from the single global `segment_matches` fact obtained by composing the
  actual encoder and actual copy-helper postconditions.
- `encoder_success_size_word_bridge` discharges the W64 modular-subtraction
  boundary only under the actual successful encoder's proved offset/length
  bounds. No general identification of W64 subtraction with integer
  subtraction is assumed.
- The precondition is satisfiable via the existing zero-valued canonical
  symbol-array witness. This establishes harness-precondition non-vacuity,
  not reachability of the success disjunct.
- Encoder success reachability, encoder/decoder losslessness and termination,
  malformed-input rejection, canonical parsing, and all encoding/security
  deltas remain proof obligations. `OBL-RANS-ACTUAL-SUCCESS-WITNESS` remains
  `PARTIAL`. `OBL-SIG-HBZ-ENCODE-DECODE` is now
  `PROVED (success-conditioned partial correctness)` via
  `signature_pack_unpack_hbz_full_actual_exact`; the unconditional round-trip
  statement still depends on the witness.
- The Week 14 wrapper theorem is a proof-authored production full-HBZ
  boundary and is not added to the cryptographic assumption or runtime-
  contract interfaces.
