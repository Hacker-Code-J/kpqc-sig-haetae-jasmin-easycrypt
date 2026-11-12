# HAETAE Jasmin / EasyCrypt

This workspace proves component-level functional correctness for programs extracted
directly from the [current Jasmin implementation](../haetae-jasmin/README.md). It
preserves the specifications, theorems, and dependency theories actually checked
by EasyCrypt, separately from KAT execution results.

The current proof scope covers **CDT, fixed-point multiplication and polynomials,
a single Gaussian attempt, the exact outputs, acceptance order, and sum of squares
of finite consumers, the complete signing Gaussian stream function, fixed-length
SHAKE initialization and repeated blocks, the complete signing Hyperball function
and modes 2·3·5, NTT, and actual API memory helpers**. The basic theorems for the
complete Gaussian and Hyperball functions are Hoare theorems about the word
results of terminating executions. For Gaussian, termination of the actual
complete buffer function is also proved under the premise that a finite input
segment contains sufficiently many accepted candidates. Correctness proofs for
complete KeyGen/Sign/Verify and the Sign→Verify composition remain incomplete.

The 83-bit CDT has a separate mathematical distribution theorem. **Under uniform
83-bit input, the statistical distance between the output distribution of the
actual Jasmin CDT and the nonnegative discrete Gaussian (σ=16) is less than
2^-78.** The target distribution is defined from the formulas in the official
specification and references; its infinite normalization, tail bounds, and
numerical certificates are also checked. See the
[specification correspondence and scope](docs/cdt-distribution-correspondence.md).

The range of the actual exponent argument is also proved for every sigma76 input.
The normalized output of the actual Jasmin `approx_exp` is connected to
`exp(-xi/2^48)` with an error **at most 27/2^48 and less than 2^-43**.
The conditional acceptance probability for uniform 48-bit rejection input at a
fixed candidate is also checked. The
[exact comparison target and bounds](docs/approx-exp-mathematical-bound.md)
document quantization, rounded-zero behavior, and remaining distribution obligations.

The error between the actual argument and the Gaussian exponent before rounding
is **at most 2^-49**. The interval where the zero test on the rounded candidate
differs from the zero test before rounding is also computed exactly. In one
actual attempt with fixed CDT bytes and explicitly independent uniform 72-bit
noise and 48-bit rejection input, the difference from the averaged Gaussian
acceptance formula before rounding is **less than 29/2^48, hence less than
2^-43**. The [new formulas and proof scope](docs/raw-gaussian-acceptance.md)
state the exceptional inputs and randomness premises.

The actual single-attempt experiment, now also drawing the CDT's 83 bits
uniformly, compares the joint acceptance-and-output probability for **every set
S of integer outputs**. Its difference from the ideal experiment using an
independent infinite Gaussian CDT and mathematical rounding is **less than
29/2^48+2^-78, hence less than 2^-43**. This result precedes division by the
acceptance probability. See the [joint output probability proof](docs/joint-accepted-output.md).

The actual and ideal acceptance probabilities are then proved to be ≥1/7 and
≥1/8, respectively, and each distribution is normalized by its own acceptance
probability. Both conditional distributions of accepted sample magnitudes have
mass 1, with **statistical distance ≤16·(29/2^48+2^-78)<2^-39**.
The [conditional distribution proof](docs/conditional-accepted-output.md) compares
against the previous ideal experiment conditioned on acceptance. Identification
with a separately defined Gaussian probability mass formula is proved in the
next result.

For the independently defined `Pr[G=k]=exp(-k²/2^153)/sum_j exp(-j²/2^153)`,
`k∈Z`, the ideal conditional distribution is **exactly the distribution of
floor((|G|+32768)/65536)**. Convergence and normalization of the infinite sum,
the weight at zero, and probabilities of rounding intervals are all proved.
Thus the statistical distance between the actual accepted sample magnitude and
this explicit Gaussian target is also **less than 2^-39**.
See the [mass-function identification and scope](docs/gaussian-magnitude-identification.md).

The experiment that repeatedly calls the actual attempt with independent
uniform 83·72·48-bit inputs **terminates with probability 1**, and its first
accepted value has exactly the previous conditional distribution. The entire
accepted list is a list of independent samples from that distribution. Its
distance from the Gaussian target is **<2^-31 for 256 samples** and
**<257·2^-39 for 257 samples**. Generating the 257th value and then retaining
only the first 256 preserves the joint distribution of those 256 values.
[Retries, finite lists, and the stream connection](docs/gaussian-retries-and-batches.md)
state the candidate encoding, finite-prefix sufficiency, and proof boundary
with concrete SHAKE.

The complete iid byte-buffer model calls the actual sign-copy, carry, and finite
Gaussian consumer. It handles the five unused high bits of a uniform 26-byte
candidate exactly and connects the distributions of the initial 49 blocks and
136-byte refills. Under `gib_bounds` alone, it proves probability-1 termination,
the **exact independent joint distribution of the 256 stored magnitudes**, and
distance **<2^-31** from the Gaussian target. A request for 257 accepts the
dummy as well before reading the same 256 values. No additional premise requires
a sufficient input segment or a canonical initial square word.
The [complete iid buffer proof](docs/gaussian-iid-buffer.md) distinguishes word
accumulators from their mathematical integer interpretation.

The [signed-output stage](docs/gaussian-signed-output.md) proves that 32 bytes
from the actual iid buffer produce 256 independent fair sign bits, independent
of the entire sample-array and square-word state. It connects the exact
distribution law of actual return observations defined by `±W64.to_uint(word)`
and their **distance <2^-31** from an independent signed Gaussian target.
The target is `sign(G)·floor((|G|+32768)/65536)`: zero remains zero, and ±32768
round to ±1, respectively. The actual sign computation after scaling is exact
at word level; its signed32 interpretation retains the condition that each
rounded magnitude is ≤2147483647. Final integrated results, target counts,
and hashes appear in the [verification record](VALIDATION.md) and manifests.

The [Hyperball candidate-sequence replay proof](docs/hyperball-actual-witnesses.md)
connects fixed candidate bytes to the actual finite consumer's samples and sum
of squares, including two dummies, and then to the actual Newton, scaling, and
norm calls. `HyperballWitnessReplay.run`, whose only input is a mode, terminates
with probability 1 for all three modes and returns acceptance value 1 even
though the integer norm of the returned array exceeds the radius bound.
Intermediate values are not supplied as assumptions about the result. This
execution supplies candidate buffers directly; SHAKE seeds, reachability in
the original complete seeded Hyperball function, and exception probabilities
are separate matters.

The [Hyperball safe input domain](docs/hyperball-safe-domain.md) proves the
safety of the actual numerical computation under `hbs_good` alone. Its premises
are mode 2/3/5, initial low limb<2^48, and `3D*2^74≤S≤5D*2^74`, where D is
the number of stored samples+2. For arbitrary sample and sign arrays, it derives
actual rounded magnitudes≤2^26, signed32 fit, N<2^64, the exact integer
interpretation of the norm word, and acceptance iff N≤the mode bound.
Neither output bounds nor convergence are assumed. This is a conditional
guarantee for a sufficient input interval, not a claim of unconditional
acceptance or termination of the outer retry. The probability of that interval,
SHAKE, and the ideal distribution remain obligations.

<!-- gaussian-payload:overview:start -->
[The complete accepted payload and sum of squares](docs/gaussian-payload-and-squares.md)
prove the **exact joint distribution** of the visible vector and S in a Gaussian
batch driven by explicit iid bytes. The accepted history of D=1538·2306·2818
values for modes 2·3·5 has law `dlist gpd_accepted D`. The same history omits the
two dummies only from the visible vector and accumulates every raw square.
`hips_actual_joint_law`, `hips_actual_square_law`, and `hips_actual_safe_probability`
state the exact joint law, integer sum, and probability formula for the safe-domain
event; `hips_actual_terminates` states probability-1 termination of that iid
batch. Raw squares are not the squares of rounded samples.

The initial sum of squares is zero. Zero initialization of the sample and sign
arrays in `hip_initial` is also stated as a modeling choice. Production code
initializes only the sum of squares to zero; this stage does not claim equivalence
with the entire production stack state or a concrete SHAKE execution. It connects
the actual Gaussian call order, offsets, visible outputs, and S, and ghost removal
within the iid model preserves all three returned arrays. At that stage, a
numerical bound on leaving the safe interval, the ideal law of S, and the outer
Hyperball retry were left as subsequent obligations.
<!-- gaussian-payload:overview:end -->

<!-- hyperball-tail:overview:start -->
The [iid sum-of-squares tail bound](docs/hyperball-iid-tail-bound.md) checks
exponential moments of the actual accepted raw square q=floor(Z²/Q), Q=2^76.
At exponent arguments 19/200 and -15/98, it obtains respective upper bounds
10/9+2^-18 and 7/8+2^-18, and connects normalization factors 3947/4000 and
1963/2000 through checked exponential-interval and power certificates.
Consequently, the probabilities that the full S lies outside [3DQ/4,5DQ/4]
for modes 2·3·5 are respectively **less than 2^-29·2^-44·2^-54**.

`ht_iid_unsafe_acceptance` gives the same bounds, in one attempt connecting
the actual iid Gaussian batch to the actual numerical computation, for the
event that the attempt accepts while the integer squared norm of the returned
signed32 coefficients exceeds the mode bound. This is an unconditional joint
event, not `Pr[bad | accepted]`. The existing scratch-initialization model and
explicit uniform bytes are retained. A chi-square law for ideal S, the entire
outer retry, concrete SHAKE, and the complete API remain separate obligations.
<!-- hyperball-tail:overview:end -->

## Verified core results

| Target | Result |
| --- | --- |
| 83-bit CDT | Matches the actual threshold count; return range 0…166; returns 166 on maximum input; termination |
| Mathematical CDT distribution | Exact probability masses of the uniform 83-bit input experiment; statistical distance <2^-78 from the official nonnegative Gaussian (σ=16), and a probability-difference bound for every output set |
| `smulh48` | On all inputs, equals the 64-bit representation of `ceil(signed(a) × unsigned(b) / 2^48)` |
| `approx_exp` | Matches the degree-10 Horner computation independently extracted from C; connects each multiplication to integer ceiling semantics |
| Numerical exponential error | Actual sigma76 argument lies on the [0,2/3] grid; signed64 semantics for Horner prefixes and ceiling multiplication; error≤27/2^48<2^-43 relative to real exp, and termination |
| Conditional acceptance probability | Actual sigma call with a fixed candidate and only the 48 rejection bits drawn uniformly; probability difference≤α·28/2^48<2^-43 using the actual quantized exponent and rounded-zero correction |
| Exponent before rounding | Square limbs match floor(Z²/2^76); error≤2^-49 between the actual exponent and the Gaussian density-ratio exponent |
| Zero correction and average acceptance probability | The two zero rules differ at CDT=0 and noise 1…32767; average acceptance-probability error<29/2^48<2^-43 for an actual attempt with explicitly uniform 72+48 bits |
| Joint acceptance-and-output probability for every output set | Difference<29/2^48+2^-78<2^-43 between the actual sigma experiment with independent uniform 83+72+48 bits and the ideal experiment with an infinite Gaussian CDT and unbounded integer rounding; before normalization after acceptance |
| Conditional distribution after acceptance | Actual and ideal acceptance probabilities≥1/7 and ≥1/8; native conditional distributions have mass 1 and statistical distance≤16·(29/2^48+2^-78)<2^-39 |
| Gaussian mass-function identification | Ideal conditional distribution=distribution of the integer Gaussian's absolute value rounded by 16 bits; independent infinite normalization, zero weight, rounding PMF, and actual distribution error<2^-39 |
| Repeated actual attempts with independent randomness | Calls the actual extracted attempt each time; probability-1 termination, exact conditional distribution of the first accepted value, and Gaussian distance<2^-39 |
| Joint distribution of the accepted list | Exactly a list of n independent samples; distance<2^-31 for 256 values and <257·2^-39 for 257; preserves the first-256 projection after consuming the last value |
| Finite candidate-stream sufficiency | The 26-byte concatenation of 203-bit candidates matches the acceptance order; probability of fewer than n acceptances in n·t candidates≤n·(6/7)^t, with insufficiency probability→0 for all prefix and block lengths |
| Uniform byte input | The complete uniform 208-bit candidate and the previous 203-bit model have exactly the same observation distribution; clearing the five unused bits preserves all four return words |
| Complete iid byte buffer | Probability-1 termination of the model calling actual consumption, carry, and sign-copy functions, and the exact independent joint distribution of 256 visible magnitudes; Gaussian distance<2^-31 for requests of either 256 or 257 |
| Sign bits and signed target | 256 fair bits from 32 uniform bytes; symmetry, zero mass, and both tie cases for the rounded signed Gaussian target |
| Independent sign vector | Coordinatewise combination of independent fair signs and a magnitude list yields a list of iid signed conditional samples; distance<2^-31 from the signed target |
| Signed composition of the actual iid buffer | Independence of signs from the entire sample-array and square-word state, and the joint law of 256 visible `±W64.to_uint` observations |
| Scaling-sign connection | Exact word-level sign computation; signed32 semantics under rounded magnitudes≤2147483647; local→global connection has sample_offset=8·sign_offset conditions |
| Single Gaussian attempt | For every 26-byte input, the sample, square limbs, and acceptance bit match the specification; termination |
| Sample rounding | Actual result equals the integer formula, with `0…12033618204333965312 < 2^64`; includes CDT 166 |
| Finite Gaussian consumer | Entire return value after processing 26-byte candidates equals the specification fold; acceptance count, stored acceptance order, dummy-slot preservation, and termination |
| Sum of squares | Exact integer sum of accepted candidates' square limbs when both initial limbs are in the 48-bit range and the request is at most 512; actual square-high `<2^38` |
| Signing offset consumer | Connects outputs, order, and the integer sum of squares to actual `__sample_gauss_at`; preserves the region outside the request |
| Refill boundary | Actual carry preserves remaining bytes and terminates; combined layout of carry and a new 136-byte block |
| Single SHAKE block | Actual signing code's 24-round word permutation, 136-byte serialization of the return state, preservation outside the output region, and termination |
| SHAKE seed initialization | Equality of the entire 200-byte state for the 64-byte seed, low 16 nonce bits, and domain/padding; termination |
| Complete signing Gaussian function | Composes the actual `_sf_sample_gauss_N_full_at` initial 49 blocks, 32 sign bytes, and repeated refills with a continuous-stream specification; on termination for `n=256/257`, samples, signs, integer sum of squares, and preservation of external regions |
| Conditional termination of signing Gaussian | Termination, exact outputs, sign copying, sum of squares including dummies, and external-region preservation under a finite-prefix premise providing enough accepted candidates in the actual seed's stream; sufficiency for all seeds remains separate |
| Hyperball accumulator | Establishes the 48-bit range of both limbs for at most 2,818 accepted candidates, connecting successive Gaussian calls |
| Hyperball iid tail and single attempt | Moments of the actual accepted raw squares and safe-domain escape probabilities <2^-29/2^-44/2^-54; the same unconditional bounds for acceptance AND excessive integer squared norm in one iid attempt with actual numerical calls |
| Complete Hyperball iid payload and sum of squares | Exact joint distribution of the D=1538/2306/2818 accepted history, visible vector, and raw sum of squares in the actual Gaussian-call model; both dummies are included in S; safe-domain event probability formula and probability-1 batch termination |
| Hyperball safe input domain | Derives actual Newton6, scale, rounded magnitudes≤2^26, and N<2^64 from canonical input sum S∈[3D/4,5D/4]·2^76; acceptance iff the integer radius condition for arbitrary samples/signs |
| Actual calls for Hyperball numerical counterexamples | Consumption including both dummies, Newton6, scaling, and norm terminate with exact results on the chosen candidates; acceptance1 despite excessive actual integer norm. Excludes SHAKE seeds and the entire seeded path |
| Fixed point and scaling | Actual word multiplication, normalization, halving, six Newton updates, signs and signed32 outputs, preservation, and termination; numerical fit is an explicit condition |
| Complete signing Hyperball | Connects the actual complete function and modes 2/3/5 to the batch stream, first-acceptance history, modular norm, final bytes, and counters; uniqueness of return values |
| NTT and inverse NTT | 256-point mathematical transforms, result bounds, and termination under explicit coefficient ranges |
| Actual API helpers | Signing-context prefix, backward copying with safe overlap, zero initialization on verification failure, and preservation of external memory |

The main sampler theorems are also connected to internal functions of a separately
extracted actual signing program. Exact theorem names, premises, and unfinished
items are in [CLAIMS.md](CLAIMS.md); verification results are in
[VALIDATION.md](VALIDATION.md).

## Reproduction

The current extraction baseline is Jasmin / `jasmin2ec` 2026.09.0 and EasyCrypt
r2026.09. It requires Jasmin's EasyCrypt library, Why3, and configured SMT provers.
Binary hashes and extraction settings are recorded in
[toolchain.json](manifests/toolchain.json). When multiple versions are installed,
select executables from the same tool installation through `PATH`, `JASMIN2EC`,
and `EASYCRYPT`.

The 2026.09 extractor generates only files required by the selected array model.
The current generated artifacts comprise 48 barray extraction files, including
six programs, and five proof-support arrays. `Array5`, `Array24`, `Array25`,
`Array256`, and `WArray1024`, used by the existing SHAKE/NTT theories, are
regenerated in `generated/support/` through a separate warray extraction of the
same actual Jasmin inputs. Programs from that auxiliary extraction are not used:
the actual programs being verified retain the barray model. The support arrays
are also included in fresh-extraction equality checks and verification with
each file as a primary target.

The existing [verification-results.json](manifests/verification-results.json) is
a **historical record from the 2026.03 tool environment**, not a PASS for the new
environment. Its corresponding tools, inputs, and extraction baseline are
preserved in [history/2026.03/](manifests/history/2026.03/README.md).
The 260 targets in [2026.09-all-targets.txt](manifests/2026.09-all-targets.txt)
(53 generated files, 195 local non-NTT theories, and 12 NTT theories) were each
checked as primary targets in the full 2026.09 rerun, yielding **260/260 PASS**.
The run retained `-no-eco`, `Proofs:check`, the EOF-completion check, and default
prover selection; every recorded primary-target hash matches the current source.
The [current verification manifest](manifests/2026.09-migration.json) links the
full inventory and hashes to the [preserved full execution record](../evidence/toolchain-migration/haetae-full-proof-result.json).
For old `/tmp` paths in diagnostic logs, the [preservation index](../evidence/toolchain-migration/index.json)
provides the public copies' paths and hashes.

The original NTT/SHAKE provenance TSVs remain unchanged. The verifier first
checks their old pins, then additionally accepts only the exact reviewed
old/current SHA-256 pairs for the five support files. Changing the descriptive
migration manifest cannot authorize other contents for those five files.
The 26 gate regressions also passed, covering this entry point and rejection
of simultaneous source, statement, import, and TSV tampering.

```sh
make -C haetae-easycrypt verify
```

This command proceeds as follows.

1. Check hashes of the pinned official distribution, Jasmin inputs, extracted artifacts, and NTT support theories.
2. Re-extract from the current Jasmin sources and compare all generated files; regenerate and compare C constants and mathematical interval certificates.
3. Check for proof-skipping pragmas, new assumption declarations, unfinished proofs, and debugging commands.
4. Execute `-no-eco` and `Proofs:check` with **each generated artifact and project theory as a primary verification target**.

Each check uses a same-named temporary copy with a final checking lemma appended.
If EasyCrypt returns success at EOF while a proof is still open, this lemma
forces the check to fail. Original files and extraction artifacts remain unchanged.

By default, EasyCrypt does not recheck proof bodies in files that are only
imported. This gate therefore does not substitute success of a single final
theorem file for verification of its dependencies. It also freshly checks the
NTT support theories, so the complete run takes time.

Individual groups can also be checked. A group's PASS applies only to the
selected group.

```sh
make -C haetae-easycrypt verify-new        # Local specifications and proofs outside NTT
make -C haetae-easycrypt verify-ntt        # NTT support theories and current implementation theorems
make -C haetae-easycrypt verify-generated  # Extraction loading/type checks
make -C haetae-easycrypt test-gate         # Reject unfinished proofs and altered numerical certificates/comparison tables
make -C haetae-easycrypt test-hyperball-boundary  # Replay the C/Jasmin numerical boundary on constructed candidate sequences
```

Logs, per-run SHA-256 hashes, and exit codes are written to `logs/`.
`latest-<group>.json` becomes RUNNING when execution starts; preflight failures
are also recorded as FAIL. Git excludes `.eco` files and logs. If a sandbox
prevents Why3 from using local Unix sockets, the verification process needs
permission to run; this error is not treated as a successful proof.

## File layout and trust boundaries

- `generated/`: programs and array theories automatically extracted from the original Jasmin sources. Do not edit them directly.
- `theories/`: specifications and required NTT mathematical theories. Independent generators import the CDT and coefficients from C.
- `proofs/`: Hoare/pHoare theorems for actual extracted procedures and mathematical distribution/error theorems.
- `scripts/`: re-extraction, constant generation, integrity checks, and the verification gate.
- `manifests/`: provenance and hashes of inputs, extracted artifacts, verification targets, and earlier NTT theories.

Verification concerns Linux x86-64, `barray`, and Jasmin's `normal` semantic
model. EasyCrypt/SMT, the Jasmin extractor, and its model library are trusted
tools. The NTT support retains documented arithmetic assumptions, so the whole
project is not described as axiom-free verification. See the
[NTT assumption inventory](manifests/ntt-assumptions.md) for details.

Memory theorems are contracts over a total byte map and extracted array objects.
They do not separately verify actual operating-system memory allocation and
accessibility, the C descriptor wrappers, or the generated assembly itself.
The SHAKE theorems cover absorption/padding of a fixed-length seed and nonce and
a word-permutation stream; they do not include a separate equivalence to the
FIPS bit specification or a sponge theorem for arbitrary-length inputs.
Uniform input is explicit in the CDT distribution experiment and is not assumed
as a property of actual SHAKE. Pointwise exponential error and conditional
acceptance probability are connected through the exponent before rounding and
the difference in zero correction. For the full Gaussian distribution, the CDT
distribution and output rounding are connected through joint probabilities of
every output set. Normalization and error of the conditional accepted
distribution are also proved, as is its identification with an explicit rounded
Gaussian mass formula. Composition extends to termination and the visible
magnitude distribution in the independent uniform byte-buffer model.
The subsequent sign stage proves fair bits, an independent sign vector,
independence from the complete sample-array and square-word state, and composition with actual return
observations. That state includes both the sample array and square
words. A signed observation is not a signed cast of a W64 bit pattern: it reads
the magnitude as an integer and then applies the sign. Connecting concrete
SHAKE to the randomness model and proving complete signature correctness and
security remain open.

The scaling word theorem concerns the modular representation of sign application.
Interpreting it as a signed W32 integer requires the fit condition that each
rounded magnitude is ≤2147483647. Sign bit i of a local sample window corresponds
to global index `8*sign_offset+i`, so connecting it to the same sample coordinate
in scaling additionally requires `sample_offset=8*sign_offset`. This condition
concerns the local→global connection; it is not an extra premise for the iid
buffer's local signed observation.

Hyperball's acceptance norm is a 64-bit modular sum. A mathematical sum-of-squares
radius guarantee requires additional no-overflow conditions. The same wrapping
behavior in C and Jasmin was replayed on constructed candidate sequences;
reachability from an actual SHAKE seed is not claimed.
Exact cases and verification commands are in the
[numerical boundary record](docs/hyperball-numerical-boundary.md).
