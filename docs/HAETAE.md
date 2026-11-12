# HAETAE working baseline

## Provenance and scope

During the reorganization on 2026-09-17, the existing `HAETAE/` working
directory was adopted unchanged as the baseline. The project version in
`reference_implementation/CMakeLists.txt` is `1.2.0`. It includes the reference
implementation, test/benchmark sources, KATs, and the MIT license, but no
optimized implementation.

The [official HAETAE distribution page](https://kpqc.cryptolab.co.kr/haetae)
identifies changes to the reference implementation's hyperball sampler and the
corresponding specifications 260825 and 260904.

- [Official distribution file](https://drive.google.com/file/d/1pW6YS1wZ1gm8Neb8pY5EyYTkkdRIDmJ6/view)
- Announced SHA-256 of the official distribution ZIP:
  `e54f8f962eefadbb2929bca292797bc7ca18769fb9a273c10204f3887fd83e84`
- [Corresponding specification 260904](https://drive.google.com/file/d/1H2SFqZFG5BcWH--bJKssvXaSG0Sd3mUx/view)
- [UPSTREAM-SHA256SUMS](UPSTREAM-SHA256SUMS): SHA-256 values for the 67 files
  supplied in this repository. This per-file integrity record is distinct from
  the hash of the ZIP itself.

The ZIP was downloaded from the official link and verified against the
announced hash. All 67 supplied files matched the files at the same paths in
that ZIP byte-for-byte. The distribution ZIP and macOS metadata are not
stored redundantly in the source tree.

## Items to recheck first

Comparison of the earlier `haetae-ref` with the new reference sources revealed
the following changes. Earlier paths are available through the
[preservation tags](../archive/README.md).

| Item | Earlier implementation | Current baseline sources |
| --- | --- | --- |
| Gaussian CDT | 16-bit, 64 entries | `src/sampler.c`: 83-bit, 166-entry `sample_gauss83` |
| Input to one sampling attempt | 17 bytes | `src/sampler.c`: `GAUSS_RAND_BYTES = 26` |
| Exponential approximation | Earlier polynomial | `src/sampler.c`: degree-10 `approx_exp` and new integer coefficients |
| Multiplication rounding | Earlier rule | `include/fixpoint.h`: ceiling rounding in `smulh48` |
| Sample-value rounding | Earlier combined shift | `src/sampler.c`: separate high/low limb computation |

All paths above are under `HAETAE/reference_implementation/`. The earlier
Jasmin sampler's 17-byte input, stride, buffer sizes, and dependent proofs must
be ported to the new implementation and rechecked. Byte equality of `params.h`
with the earlier reference alone does not establish equivalence of sampler
distributions or the complete algorithm. `mode2`/HAETAE-2 names a parameter set,
not a distribution version.

## Implementation status and subsequent work

A separate [Hyperball arithmetic hardening variant](../haetae-hardened/README.md)
was added starting on 2026-09-27. The original Jasmin, EasyCrypt, and reference
implementations are preserved; code rejecting conversion-range violations and
norm-accumulation overflow is extracted and verified separately. The property
that an accepted return vector's integer sum of squares is at most the mode
bound does not assume a safe input interval or absence of norm overflow. This
variant changes acceptance of the specified counterexamples; it is not an
official new version or a claim of equivalence with the original on every
input. The [validation record](../haetae-hardened/verification-results.json)
distinguishes the scope of new proofs and rerun tests.

The new implementation is in [haetae-jasmin](../haetae-jasmin/README.md). It
ports the sampler changes above and the randomness-consumption/refill rules,
and connects 8 public/internal APIs, the official mode 2·3·5 KATs, and
differential/interoperability tests against the actual C sources. The
[validation record](haetae-jasmin-validation.md) provides reproduction commands
and limitations.

The new [EasyCrypt project](../haetae-easycrypt/README.md) verified theorems for
CDT, ceiling multiplication, Horner evaluation, a single Gaussian attempt,
acceptance order and sum of squares of the finite consumer, the actual signing
offset consumer, SHAKE initialization and streams, the actual complete signing
Gaussian function, NTT, and API helpers. It then connected the actual complete
Hyperball function and modes 2·3·5 to word specifications. The basic
whole-function theorems apply to terminating executions. Gaussian also has a
termination theorem under the premise of a sufficiently long finite prefix of
a concrete input stream. [CLAIMS.md](../haetae-easycrypt/CLAIMS.md) states the
verified scope and remaining premises. Work toward complete implementation
correctness proceeds as follows.

1. Maintain the baseline checks below and map functions to specification 260904.
   CDT was connected to the Gaussian definition in specification §5.1.1 and
   reference [21]. A theorem bounds statistical distance between an independent
   infinite-distribution definition and the actual Jasmin experiment on uniform
   83-bit input by less than 2^-78. Sources, numerical certificates, and exact
   randomness scope are in the [CDT specification correspondence](../haetae-easycrypt/docs/cdt-distribution-correspondence.md).
   For the exponential approximation in Listing 1, the actual input interval
   and signed Horner semantics were connected to prove normalized output
   error≤27/2^48<2^-43. Conditional acceptance probability retaining the actual
   quantized exponent and rounded-zero behavior is also covered; see the
   [numerical proof boundary](../haetae-easycrypt/docs/approx-exp-mathematical-bound.md).
   The error≤2^-49 between actual xi and the Gaussian exponent before rounding,
   and exceptional intervals for the two zero rules, were also connected.
   An explicit uniform 72+48-bit single attempt has average acceptance-probability
   difference<29/2^48<2^-43; see the [connection to the acceptance formula before rounding](../haetae-easycrypt/docs/raw-gaussian-acceptance.md).
   The actual uniform 83+72+48-bit experiment was then compared with the infinite
   Gaussian CDT target: for every output set, the joint acceptance/output
   probability difference is <29/2^48+2^-78. The [joint output probability](../haetae-easycrypt/docs/joint-accepted-output.md)
   theorem is before normalization following acceptance.
   Lower bounds 1/7·1/8 on actual/ideal acceptance probabilities were proved,
   and comparing the acceptance-conditioned distributions yields statistical
   distance<2^-39. The target in the [conditional-distribution scope](../haetae-easycrypt/docs/conditional-accepted-output.md)
   normalizes the earlier ideal experiment. The subsequent
   [Gaussian mass identification](../haetae-easycrypt/docs/gaussian-magnitude-identification.md)
   connects it exactly to the rounded-absolute-value distribution of the
   integer Gaussian defined by exp(-k²/2^153). The actual conditional
   distribution's distance<2^-39 also applies directly to this explicit target.
   Termination with probability 1 of the experiment repeatedly invoking the
   actual attempt with independent uniform inputs, and the exact conditional
   law of its first accepted value, were also proved. Joint laws of 256·257 accepted
   lists and their connection to finite candidate streams are in the
   [retry and list proofs](../haetae-easycrypt/docs/gaussian-retries-and-batches.md).
   The [complete iid buffer model](../haetae-easycrypt/docs/gaussian-iid-buffer.md)
   composes uniform byte supply with the actual consumer and carry functions,
   proving termination with probability 1 and the exact joint law of the 256 stored
   magnitudes, with Gaussian distance<2^-31, without a sufficient-prefix premise.
   The subsequent [signed-output stage](../haetae-easycrypt/docs/gaussian-signed-output.md)
   proves independence of 256 fair signs from the complete sample array and
   squared-word state in the explicit iid byte model. Observing actual return
   values as `±W64.to_uint` connects them to target
   `sign(G)·floor((|G|+32768)/65536)`, giving distance<2^-31 for the 256-element
   vector. 0 remains 0, and ±32768 round to ±1 respectively. Sign
   operations after actual scaling are also word-exact; signed32 interpretation
   retains an explicit fit condition. Transferring these probabilistic
   guarantees to concrete SHAKE remains a separate obligation.
2. The single Gaussian attempt was connected through the finite consumer's
   complete output, accepted sample sequence, and sum-of-squares accumulation
   fold. Exact premises, including initial limb ranges, are stated in the theorems.
3. The actual `_sf_sample_gauss_N_full_at` seed/nonce initialization, 49 blocks,
   sign bytes, and repeated refill were connected to a continuous word-stream
   specification. Initial sum-of-squares conditions for multiple Gaussian calls
   were composed with Hyperball fixed-point arithmetic, scaling, modular norm,
   and retry. Integer-radius guarantees are distinct from word acceptance.
   Constructed candidate sequences exhibiting wrap and their premises are in
   the [numerical boundary record](../haetae-easycrypt/docs/hyperball-numerical-boundary.md).
   The sign-stage connection to scaling covers exact word sign computation and
   signed32 interpretation when rounded magnitudes are at most 2147483647.
   Connecting a local Gaussian window to global scaling indices explicitly
   requires `sample_offset=8*sign_offset`. Real-approximation error, distribution,
   and termination of the complete Hyperball function are separate obligations.
   The [actual-helper counterexample proofs](../haetae-easycrypt/docs/hyperball-actual-witnesses.md)
   compose the actual consumer, accumulation of two dummy squares, Newton6,
   scaling, and norm on specified candidate sequences. All three modes are
   proved to return acceptance 1 despite an integer-radius violation.
   Corresponding SHAKE seeds, reachability through the complete seeded Hyperball
   path, and probabilities of exceptional events remain separate.
   The [safe input interval](../haetae-easycrypt/docs/hyperball-safe-domain.md)
   derives actual Newton/scaling coefficients≤2^26 and absence of integer-norm
   overflow from canonical sum of squares S∈[3D/4,5D/4]·2^76. This proves
   acceptance⇒radius bound for arbitrary samples/signs. The probability of the
   interval, actual seeds, the outer retry, and an ideal distribution remain separate.
4. Retrieve NTT, codecs, and other reuse candidates from the tags as needed and
   compare them with the current sources. Then proceed with KeyGen/Sign/Verify
   composition while distinguishing termination, distribution, and security obligations.

Earlier verification logs are not used as proof results for new Jasmin sources.
Reused NTT support theories were also rechecked individually as main targets in
the new directory.

<!-- gaussian-payload:milestone:start -->
The subsequent [complete accepted-payload and sum-of-squares stage](../haetae-easycrypt/docs/gaussian-payload-and-squares.md)
connects complete Gaussian batches for modes 2·3·5 under explicit iid bytes and
initial sum of squares 0. It invokes the actual sign-copy, carry, and finite
consumer along requests `257, 257, 256, ...`, sample offsets `256*i`, and sign
offsets `32*i`. Initialization of samples/signs to 0 in `hip_initial` is a
modeling choice. Production code initializes the sum-of-squares array; no
equivalence to the complete production state or seeded execution is claimed.

In the accepted-payload histories of D=1538·2306·2818 events, positions
256·513 counted from 0 are omitted only from the visible vector, while every raw square
remains in S. Projection of this same history proves the joint law of the
visible vector and S and an exact probability expression for the safe-interval
event. At that stage, a numerical upper bound on interval escape, an ideal
Gaussian/chi-square law for raw squares, and connections to SHAKE, the outer
Hyperball retry, and the complete API were left as subsequent obligations.
KATs were not rerun at that stage because production code was unchanged.
<!-- gaussian-payload:milestone:end -->

<!-- hyperball-tail:milestone:start -->
The subsequent [iid sum-of-squares tail and single-attempt bound](../haetae-easycrypt/docs/hyperball-iid-tail-bound.md)
proves safe-interval escape probabilities below 2^-29·2^-44·2^-54 respectively
for D=1538·2306·2818 actual accepted payloads. It uses the exponential moment of
q=floor(Z²/2^76), checked real-exponential coefficients, and integer-power
certificates. q is not the square of a rounded sample. The same bounds apply to
the joint event of acceptance and integer squared-norm violation in one iid
attempt composing the actual Gaussian batch and actual Newton, scaling, and
norm calls.

The initial sum of squares is 0. Initializing samples/signs to 0 in the existing
`hip_initial` is a modeling choice; production code initializes only the sum
of squares. This result does not give an acceptance-conditioned probability,
a guarantee for the complete outer retry, or a probabilistic guarantee for
concrete SHAKE/seeded Hyperball. It is a subsequent result resolving the earlier
numerical tail-bound obligation in the iid model. KATs were not rerun at this
stage because these proofs added no production changes.
<!-- hyperball-tail:milestone:end -->

## Reproduction and verification limits

```sh
# From the repository root
bash scripts/check-baseline.sh
```

On the baseline before the 2026-09-17 reorganization, all 6 `.req`·`.rsp` files
for `ref` mode 2·3·5 KATs matched, and the distribution's `kat/SHA256SUMS` check
passed. The `kat.sh update` command, which generates and overwrites KAT files,
is not used for this validation.

KAT agreement checks reproducibility of the supplied C implementation. It does
not replace sampler-distribution correctness or Jasmin/EasyCrypt verification.
In particular, `test/test_sampler.c` is not included in the default CMake test
targets and contains its own approximation functions, so it is not counted as
evidence for the production sampler. `test/main.c` can also print a failure
and then exit with code 0; a successful exit code alone is not sufficient.

Historical proof results and unresolved items at the reorganization point are
preserved in `archive`. The earlier complete EasyCrypt verification was not
rerun as part of this structural reorganization.
