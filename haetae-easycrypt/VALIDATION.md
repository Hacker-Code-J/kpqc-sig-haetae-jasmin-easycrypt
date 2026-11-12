# Verification record

## Reproducing the current public sources

Results for the current sources are established by the per-run summaries, logs,
and source hashes produced by `bash scripts/reproduce.sh quick` and `full`.
Run commands at the repository root and follow the
[environment guide](../env/README.md) to prepare the tools. Distinguish quick
regression checks from the complete specification/proof checks.

For the later completed full-runner execution and its exact source identity,
see the [recorded reproduction summary](../docs/release.md#recorded-reproduction).
The sections below preserve the boundaries of the earlier execution stages.

Later NTT composition proofs, directory renaming, and publication-documentation
changes are not automatically included in the historical executions below.
A record of a full PASS at that time does not establish that the entire current
public tree has the same hashes or has been reverified. The current targets are
`manifests/proof-targets.txt` and the actual source inventory collected by the verifier.

## Preserved toolchain-migration execution

During migration to Jasmin 2026.09.0 and EasyCrypt r2026.09, **260/260 primary
targets** in the original project (207 specifications/proofs and 53 generated
files) passed, as did **290/290 primary targets** in the complete matrix combining
the original and hardened projects. The run used `-no-eco`, `Proofs:check`,
the EOF-completion check, and default prover selection. These counts and checked
hashes record that execution snapshot.

- [Full execution result](../evidence/toolchain-migration/haetae-full-proof-result.json)
- [Per-primary-target summary](../evidence/toolchain-migration/proofs/summary.json)
- [In-repository evidence index](../evidence/toolchain-migration/index.json)
- [Preservation scope and interpretation of original paths](../evidence/toolchain-migration/README.md)
- [Original migration manifest](manifests/2026.09-migration.json)

The evidence index points to files within the public repository. Old absolute
paths in the original JSON/logs are preserved as part of the original evidence;
they are not interpreted as paths required for a current execution. The preserved
final-run evidence and all historical failure diagnostics are not claimed to
have the same coverage.

The final provenance check and **26** gate regressions also passed at that time.
The historical NTT/SHAKE TSV pins were retained, with exact reviewed pre-migration/
post-migration hash pairs for support files and checks rejecting tampering with
those pairs. Approval of later control-code or target changes is established
through separate review, execution, and hash records.

## Executions at earlier research stages

The 2026-09-17~22 narrative below and the PASS entries in
`manifests/verification-results.json` are historical records from the Jasmin
2026.03.0 environment. The corresponding tool, input, and extraction hashes are
preserved unchanged in `manifests/history/2026.03/`.

During the 2026-09-17~22 work, extraction was rerun from the then-current Jasmin
sources and EasyCrypt was actually executed. Verification logs from older
versions or KAT results were not substituted as evidence for new proofs.

| Category | Newly checked targets | Result |
| --- | --- | --- |
| Extracted artifacts | 102 array theories and current programs | All passed at the preceding stage; fresh extraction equality checked at this stage |
| Non-NTT specifications/proofs | 195 files in `verify-new` | All passed in a fresh integrated run with EOF checks |
| NTT | 11 required support theories and 1 current implementation theorem | Each passed as a primary target at the preceding stage; unchanged hashes checked at this stage |
| Verifier regressions | 14 existing EOF, constant, and Gaussian-certificate checks plus 4 exponential-polynomial certificate checks | All 18 PASS |
| Mathematical CDT distribution | Actual Jasmin uniform 83-bit input distribution and nonnegative Gaussian (σ=16) | Probability difference <2^-78 proved for every output set |
| Numerical exponential error | Actual exponent-argument range and actual approximation function for all sigma76 inputs | Normalized-output error≤27/2^48<2^-43 and termination proved |
| Conditional acceptance probability | Actual sigma call with fixed candidate and uniform 48-bit rejection input | Probability difference≤α·28/2^48<2^-43 relative to the actual quantized exponent/rounded-zero rule |
| Exponent before rounding | Actual square/exponent and independent Gaussian density ratio | Exponent error≤2^-49 for every 26-byte input |
| Zero-correction difference | Actual rounded-zero and zero before rounding | Differ only at x=0 and 1≤y<32768; average factor effect<2^-58 under uniform 72 bits |
| Average acceptance against the pre-rounding reference | Actual sigma call with fixed CDT bytes and independent uniform 72+48 bits | Probability difference<29/2^48<2^-43 from average raw Gaussian acceptance |
| Joint probability for every output set | Actual uniform 83+72+48-bit attempt and the infinite-Gaussian-CDT/unbounded-integer-rounding target | Joint acceptance-and-output probability difference<29/2^48+2^-78<30/2^48<2^-43 for every S; before normalization |
| Conditional distribution after acceptance | Native dcond/integer-projection distributions of the actual and preceding independent ideal experiments | Actual acceptance≥1/7 and ideal≥1/8; both conditional distributions have mass 1 and statistical distance≤16·(29/2^48+2^-78)<2^-39 |
| Explicit Gaussian mass formula | Independent normalization of exp(-k²/2^153) over all integers and the rounded-absolute-value PMF | Exactly matches the ideal conditional distribution; statistical distance<2^-39 from actual accepted magnitudes, including zero and interval boundaries |
| Uniform bytes and complete iid buffer | Actual-call model's 49 blocks, carry, consumption, and 136-byte refills | Probability-1 termination under `gib_bounds`; joint distribution of the visible 256 values for requests 256/257 and Gaussian distance<2^-31 |
| Signs and sample/square-word state | Actual iid buffer's sign window and entire sample/square-word state | Independence of 256 fair bits; Gaussian distance<2^-31 for signed observations |
| Actual sign application | XOR/add and W32 truncation after scaling/rounding | Exact word result; scalar/vector signed32 semantics under rounded magnitudes≤2147483647 |
| Hyperball iid tail/single attempt | Actual accepted raw-square moments, checked exponential/power certificates, and actual numerical tail | Safe-interval escape and single-attempt acceptance AND excessive integer-norm probabilities <2^-29/2^-44/2^-54 for modes 2/3/5 |
| Joint Hyperball iid payload/S distribution | Actual Gaussian-buffer calls with mode-specific requests/offsets and initial sum of squares 0 | Exact joint distribution of the complete D=1538/2306/2818 accepted list, visible vector, and raw sum of squares; safe-interval probability identity and probability-1 termination |
| Hyperball safe input domain | Actual numerical calls with canonical S∈[3D/4,5D/4]·2^76 | M≤2^26, N<2^64, exact norm word, and acceptance iff the radius condition for arbitrary samples/signs; excludes the probability of reaching the interval |
| Actual-helper Hyperball counterexamples | Fixed candidates→actual consumption/accumulation of both dummies→Newton6→scaling→norm | Termination, acceptance1, and integer radius violation by the returned array in all three modes; excludes SHAKE-seed reachability |
| Hyperball numerical replay | C/Jasmin execution on fixed candidate sequences for modes 2·3·5 | Preserves the counterexample stage's 09-22 replay PASS; no implementation changes at this stage |

All 207 local specifications/proofs were checked as primary verification targets
at their respective stages. Imported proof bodies were not assumed to be
automatically rechecked. The new code gate uses `-no-eco` and explicit
`Proofs:check`; the original NTT-support replay also ran each target separately
in the default strong-checking mode with `-no-eco`.

<!-- hyperball-tail:verification:start -->
This iid sum-of-squares tail-bound stage added 15 specification/proof files.
The 180 unchanged non-NTT files and 15 frozen new files were each checked as
primary targets, yielding **195/195 PASS**. The run used `-no-eco`, explicit
`Proofs:check`, the EOF-completion safeguard, and a final comparison of the
complete inventory and hashes. The complete local inventory contained 207 files;
the previous 12 NTT files retained their results and identical source hashes
and were not rerun at this stage. The gate timestamp is `20260922T065900.431316Z`.

Hashes of 496 pinned sources, including the previous 192 local specifications/
proofs, and four tool executables were unchanged. The 18 verifier regressions
passed, and 102 fresh extraction files matched. The new
`hyperball-tail-certificate.py --check` confirms byte-for-byte reproduction
against a record pinning the generator and certificate hashes. Inequalities in
the generated numerical data are proved through separate EasyCrypt integer
checks and connections to the actual exponential and powers. There are no new
axioms or numerical oracles. Production, reference, archive, and existing
verifier/test files were not changed; KATs were not rerun.

Actual accepted moments for q=floor(Z²/Q), Q=2^76 were proved to be
≤10/9+2^-18 and 7/8+2^-18, then composed with centered factors 3947/4000 and
1963/2000. `ht_iid_list_tail` and `ht_iid_square_tail` bound the probabilities
that the full raw sum of squares for D=1538·2306·2818 lies outside [3DQ/4,5DQ/4]
by strictly less than 2^-29·2^-44·2^-54, respectively. Both dummy squares remain
in the sum. `ht_iid_unsafe_acceptance` gives the same bounds for acceptance AND
excessive integer squared norm of returned coefficients in one iid attempt
calling the actual Gaussian batch and actual numerical helpers.

The initial sum of squares is zero. Zero initialization of samples/signs in
`hip_initial` is a proof-model choice; production code initializes only the sum
of squares. The probability concerns an unconditional single-attempt event in
an explicit uniform-byte model. Conditional unsafe probability given acceptance,
bounds for the complete outer retry, an ideal Gaussian/chi-square law for actual
S, concrete SHAKE, and the complete API are excluded.
The [exact events and proof connections](docs/hyperball-iid-tail-bound.md)
record the formulas and public contracts.

The earlier-stage records below preserve their original scopes and verification
counts. The numerical tail-bound obligation left open then is discharged in
the explicit iid model above, without extending the result to the seeded setting.
<!-- hyperball-tail:verification:end -->

<!-- gaussian-payload:verification:start -->
The preceding complete accepted-payload/sum-of-squares stage added 12
specification/proof files. It first freshly checked the 168 unchanged non-NTT
files, then checked the 12 frozen new files using the same EOF-completion
safeguard, `-no-eco`, and explicit `Proofs:check`. After comparing the final
complete inventory and source hashes, the integrated result was **180/180 PASS**.
The complete local inventory contained 192 files; the previous 12 NTT files
retained their results and identical hashes and were not rerun at this stage.
The gate timestamp is `20260922T054034.419769Z`, and the evidence is recorded
in the [verification manifest](manifests/verification-results.json).

All 484 pinned sources, including the previous 180 local specifications/proofs,
were byte-identical. Production, reference, archive, existing extraction, and
verifier/test files were not changed. The 18 verifier regressions passed, and
102 fresh extraction files matched. As production code was unchanged, KATs were
not rerun at this stage. No new project axioms or external numerical oracles
were added.

`gpe_history_law` and `gpd_buffer_draw` connect the full accepted-payload history,
including dummies, to an independent list from the conditional distribution.
`gpt_buffer_total` proves visible values, integer sum of squares, and canonical
form for the complete buffer under an accumulation budget.
`hip_batch_history_law` and `hip_payload_observe_total` prove composition of
mode-specific requests `257,257,256,...` and sample/sign offsets
`256*i`/`32*i`. The initial sum of squares is zero. Setting sample/sign arrays
to zero as well is a proof-model choice in `hip_initial`; production `sign.jazz`
initializes only the sum of squares to zero. Actual Gaussian call order is
connected to visible outputs and S; within this iid model, ghost removal preserves
all three returned arrays.

`hips_actual_joint_law` obtains the exact joint distribution of the visible
vector and S as projections of the same D=1538·2306·2818-element history.
Zero-based positions 256·513 are omitted only from visible values;
S in `hips_actual_square_law` includes every raw square. Raw squares are not
the squares of rounded samples. `hips_actual_safe_probability` states the exact
probability formula for the safe-input-interval event, and
`hips_actual_terminates` states probability-1 termination of this iid Gaussian
batch. A numerical escape-probability bound, an ideal Gaussian/chi-square law for
S, unsafe-acceptance probability, concrete SHAKE/seeded Hyperball, outer Hyperball
retry, and the complete API remained unfinished.
The [payload and sum-of-squares record](docs/gaussian-payload-and-squares.md)
states the exact projections and contracts.

The numerical-safe-domain and earlier distribution records below preserve the
scope and verification counts at each stage.
<!-- gaussian-payload:verification:end -->

The preceding safe-input-domain stage added eight specification/proof files.
The public premise hbs_good contains only mode 2/3/5, input low<2^48, and
S∈[3D*2^74,5D*2^74]. S is the integer value of raw square limbs including both
dummies, and D=number of stored samples+2. A canonical input at the center
S=D*2^76 establishes that the interval is nonempty.

Actual multiplication is connected to floor(XY/Q)…floor+1 and squaring to the
exact floor(X²/Q). The required headroom for additions, high shifts, and final
normalization is proved, while masked-shift wrapping is retained. Allowing
low<2R after the initial subtraction, an integer cubic margin and rounding errors
preserve upper bounds across six updates. hbs_safe_newton derives the final
reciprocal's canonical form and upper bound from the input conditions.

Under the same input conditions, hsc_full_magnitude proves actual rounded
magnitude≤2^26 for arbitrary W64 samples. hsc_total proves termination of the
actual half/Newton/mul-high/scale-check/norm calls, and signed32 coefficient
bounds, N<2^64, exact norm-word interpretation, and acceptance iff the integer
radius condition for arbitrary sample/sign arrays. hsc_accepted_radius_total
states that acceptance implication directly. Output fit and norm bounds are
not assumed again.

The existing 160 non-NTT files were freshly checked first; the eight new files
were frozen and checked with the same EOF-protected verifier. After comparison
of the final complete inventory and hashes, 168/168 PASS was recorded.
The previous 172 local specifications/proofs and production, reference, archive,
extraction, and existing verifier/test files were unchanged. The 18 verifier
regressions passed, and 102 extraction files matched fresh output.
The 12 NTT files retained results and hashes from the preceding stage and were
not included in this rerun. KATs were not rerun because production code had not
changed. There are no new axioms or numerical oracles.

The input interval is a sufficient condition, not a newly added runtime guard.
It does not imply unconditional acceptance or termination of the outer retry.
Interval probability, connection to actual SHAKE/seeded Hyperball, final
inverse-square-root error, the ideal distribution, and the complete API remain
open. The [safe-input-domain record](docs/hyperball-safe-domain.md) gives the
numerical values and exact contracts.

`CDTGaussianApproximation.uniform83_jasmin_half_gaussian_error` concerns an
experiment passing uniformly drawn 83-bit input to actual
`SamplerTarget.M.sample_gauss83_jazz`. Its target is
`P(k)=exp(-k²/512)/sum_{j≥0}exp(-j²/512)`, `k≥0`.
The statistical distance between this implementation-independent infinite
distribution and the actual output distribution is proved **less than 2^-78**;
the probability difference for every output set has the same bound.
Normalization, the infinite tail, exponential intervals, and numerical certificates
were checked rather than left as assumptions. Official-PDF and reference
provenance and formula correspondence appear in a
[separate record](docs/cdt-distribution-correspondence.md).

`ApproxExpNumericalCorrectness.sigma76_approx_exp_numerical_total` discharges
the range condition for actual argument `xi` on every 26-byte input and proves
error≤27/2^48<2^-43 between the actual signer's normalized output and
`exp(-uint(xi)/2^48)`. It combines coefficient-polynomial grid error≤24/2^48
with execution rounding-up error≤3/2^48. Signed64 interpretation of every
Horner prefix and ceiling-multiplication result is also justified.

`SigmaExpAcceptanceCorrectness` compares the acceptance probability of an actual
sigma call varying only the rejection bytes uniformly. It proves an exact
probability formula including saturation, even comparison, and actual rounded-zero
correction, and error≤α·28/2^48<2^-43 relative to the real exponential.
This conditional theorem retains the actual quantized exponent and rounded-zero
rule. Formulas, sources, and actual-procedure connections are in the
[numerical proof record](docs/approx-exp-mathematical-bound.md).

`SigmaRawExponentCorrectness.sigma_raw_exponent_exact` proves that actual xi
equals `floor((y(y+2^73x)+2^104)/2^105)`. It uses the exact integer square formula
established by `SigmaSquareExact` and byte/CDT ranges, so the final 26-byte
theorem has no additional fit premise. Normalized exponent error is at most
2^-49; `SigmaRawDensityIdentity` proves that the comparison exponent represents
a ratio of unnormalized Gaussian weights.

`SigmaRawZeroCorrectness` proves the exact interval where the two zero-test
rules differ. Fixed-candidate error retains the half correction for this exception.
`SigmaRawAverageCorrectness.sr_average_acceptance_error_strict` proves that,
when `SigmaNoise72Experiment` passes independent uniform 72-bit noise and
48-bit rejection randomness to the actual extracted procedure, the difference
between average Gaussian acceptance before rounding and actual acceptance
probability is less than 29/2^48 and less than 2^-43. CDT input is fixed; no
uniformity premise for concrete SHAKE is required. This is a single-attempt
average-acceptance theorem. The conditional distribution after acceptance is
compared separately by subsequent normalization theorems. Detailed formulas and
sources appear in the [pre-rounding acceptance connection](docs/raw-gaussian-acceptance.md).

`SigmaJointCorrectness.sj_joint_output_error_strict` compares the event
`accepted /\ S(output)` between actual `SigmaJoint203Experiment` and independent
`SigmaJointIdeal` for every set S of integer outputs. The difference is less
than 29/2^48+2^-78 and also less than 30/2^48 and 2^-43.

Actual samples are read as unsigned W64 values. The ideal CDT is a Gaussian over
all nonnegative integers, and ideal rounded values are not wrapped to 64 bits.
The implementation error is first multiplied by the output-set indicator and
averaged over noise; the expectation difference of a [0,1] kernel is then bounded
by CDT statistical distance. This order avoids imposing the implementation range
x≤166 on the ideal infinite tail. The result is not divided by acceptance
probability. The conditional distribution after acceptance is connected by the
normalization theorems below, and rejection retries with independent randomness
are addressed in subsequent theorems. Detailed experiments, formulas, and proof
connections are in the [joint output probability record](docs/joint-accepted-output.md).

`SigmaAcceptanceLowerBound` first fixes CDT/noise candidate bytes and proves
acceptance probability at least 1/7 when the 48 rejection bits are redrawn
uniformly, then averages over 72·83 bits to obtain the same bound for the actual
complete experiment. It transfers a lower bound of 1/8 to the ideal experiment
through the joint-probability error, without applying the implementation's finite
exponent range to the ideal infinite tail.

`SigmaConditionalCorrectness.sc_conditioned_distributions_correct` proves
that the native integer distributions obtained by conditioning the actual and
preceding independent ideal experiments on their own acceptance events both
have mass 1 and statistical distance<2^-39. Keeping the two denominators distinct,
it first applies the common bound 16·(29/2^48+2^-78), accounting for numerator
and denominator errors, to every event and then to statistical distance.
All positivity premises are discharged in the final theorem. The target at that
stage was the previous ideal experiment's conditional distribution; subsequent
theorems below identify it with an explicit rounded Gaussian probability mass
formula. Detailed distributions, formulas, and verification scope are in the
[conditional-distribution record](docs/conditional-accepted-output.md).

`Gaussian76Properties` uses a geometric upper bound to prove convergence of
Z, the sum of rho(k)=exp(-k²/2^153), k∈Z, and Z≥1. The normalized distribution
has mass 1 and assigns positive probability to every integer. Z is not defined
from an acceptance probability or implementation table.

`Gaussian76Identification.g76_ideal_conditioned_eq` proves that the previous
ideal conditional distribution is exactly the distribution obtained by rounding
G's absolute value as (|G|+32768) div 65536. It composes quotient/remainder
reindexing of infinite sums, Gaussian-weight cancellation for every x≥0,
symmetric folding counting zero once, and acceptance probability Z/(2·N·H16).
`g76_actual_gaussian_correct` transfers mass 1 and statistical distance<2^-39
between actual accepted magnitudes and this explicit target. No new
approximation error is added.

`Gaussian76Rounding.g76_rounded_mass` expresses the probability of each ideal
output exactly as a finite sum of Gaussian weights over its rounding interval.
`g76_actual_rounded_mass_error` proves that the difference between the actual
post-acceptance probability of that value and this expression is less than 2^-39.
Zero includes |G|≤32767, and both ±32768 map to 1. This identifies the mathematical
absolute-value distribution. The identification theorem alone does not prove
actual sign handling or rejection retries; retries are addressed subsequently.
Exact mass formulas and scope are in the [Gaussian identification record](docs/gaussian-magnitude-identification.md).

`GaussianRetryActual.gr_actual_retry_ll` and `gr_actual_retry_law` prove
probability-1 termination and the exact conditional distribution of the
independent-randomness loop calling the actual extracted attempt each time.
The Gaussian distance remains <2^-39 without new error.
`GaussianRetryBatchCorrectness.gra_batch_joint_law` identifies the complete
accepted-list law as `dlist(sc_actual_conditioned p,n)`. The procedure generating
the 257th value first and then retaining the first 256 also terminates with
probability 1 and preserves their distribution.

`GaussianRetryInputs` connects 26-byte candidates containing canonical 203-bit
inputs to a continuous candidate stream. The five unused high bits are zero.
`GaussianRetryPrefixCorrectness` uses the same shortfall event as the actual
buffer proof's `gr_adequate` condition to prove shortfall probability≤n·(6/7)^t
for n·t candidates and convergence to zero for all candidate/block lengths.
No distribution over uniform infinite functions is introduced.

`GaussianRetryStreamTermination.gr_sample_gauss_N_prefix_total` proves
termination and the prefix specification of actual `_sf_sample_gauss_N_full_at`
for requests 256/257 under the existing offset/initial-limb ranges and a sufficient
finite segment of the concrete SHAKE stream. A decreasing quantity is defined
using the maximum compatible block index in a finite range, so no one-to-one
correspondence between SHAKE states and block indices is assumed. It retains
32 sign bytes, the first 256 outputs, the integer sum of square limbs including
the 257th dummy, and external-region preservation. This conditional SHAKE theorem
does not prove independence of concrete SHAKE or termination for every seed.
The probability law of an explicit iid byte buffer is connected separately in
subsequent theorems. [Retry, list, and buffer scope](docs/gaussian-retries-and-batches.md)
records the distinctions and theorem map.

`GaussianIidBufferPath.gib_actual_functional` connects the operational model
calling actual production helpers to a byte-list representation through equivalence
of the entire return tuple under the same random draws.
`GaussianIidProgress.gip_refill_progress` obtains progress probability≥1/7 from
an intact candidate in the new 136-byte block even after arbitrary already known
remaining bytes. The independent termination proof in `GaussianIidTermination`
and expectation upper bounds for events and complements in `GaussianIidEventLaw`
combine into an exact distribution law. The completion distribution for fixed
remaining bytes serves as an invariant; those bytes themselves are not assumed
to be fresh uniform randomness.

The earlier single-iid-buffer stage permits arbitrary word values in the initial
square array, so equivalence of the complete return tuple does not automatically
provide a no-overflow integer interpretation of the sum of squares. The previous
initial-limb and accumulation-range conditions remain necessary for that
interpretation. Observations in that stage's probability theorem are the 256
stored unsigned magnitudes. The subsequent sign stage connects independence and
signed observations, while actual signed32 application retains explicit fit
conditions. Exact input conditions and connections appear in the
[complete iid buffer record](docs/gaussian-iid-buffer.md).

`GaussianStreamCorrectness.sample_gauss_N_full_at_correct` includes actual
`_sf_sample_gauss_N_full_at` seed/nonce initialization, 49 blocks, sign copying,
and repeated carry/refill/consumption. For requests 256/257, valid offsets, and
both initial limbs `<2^48`, the **return tuple of a terminating execution** matches
the specification. Uniqueness of the specification result was also checked.
Unconditional termination for a fixed seed was not assumed. The preceding
Hyperball stage also proved initial two-limb conditions across polynomial calls
using the stronger square-high bound `<2^36` and an accumulation budget of at
most 2,818 accepted candidates.

`HyperballCorrectness.hyperball_full_correct` and `hyperball_mode{2,3,5}_correct`
prove that **terminating executions of actual `_sf_hyperball_full` and the three
wrappers match the exact word specification**. They include every Gaussian call,
the initial estimate and six Newton updates, coordinatewise signs/scaling,
modular norm, previous rejections and final acceptance, and final SHAKE byte and
counter. Return-value uniqueness is also proved independently of unused scratch
regions or the choice of a sufficient stream prefix.

Norm acceptance is `N mod 2^64 <= bound` for the integer sum `N` of squared
signed32 coordinates. An integer radius guarantee is derived only under
`N < 2^64` or explicit coordinate ranges. C/Jasmin replay of fixed candidate
sequences confirms that the norm check passes after wrapping, but does not claim
the existence of an actual SHAKE seed generating those sequences or a concrete
seed counterexample. Numerical values and replay commands are recorded in the
[numerical boundary](docs/hyperball-numerical-boundary.md).

Execution records are in `logs/latest-generated.json`, `logs/latest-new.json`,
and their per-run subdirectories. Individual NTT logs from the same work are
preserved in `logs/ntt-support-replay/`. Logs are generated artifacts excluded
from Git. Source and tool identifiers are available in `manifests/`.

## Reproduction commands

```sh
# Fresh verification of the complete scope
make -C haetae-easycrypt verify

# The same verification by group
make -C haetae-easycrypt verify-generated
make -C haetae-easycrypt verify-new
make -C haetae-easycrypt verify-ntt
make -C haetae-easycrypt test-gate
make -C haetae-easycrypt test-hyperball-boundary
```

Full verification includes time-consuming NTT finite-table and loop proofs.
When combining results from separate runs of the three groups, ensure identical
sources, extracted artifacts, and tool versions.

## Checks of the verification procedure itself

- Hashes were pinned for 60 Jasmin sources, headers, and build inputs and 102
  generated files.
- The full re-extraction matched the stored artifacts, and 21 array-theory types
  with duplicate names had identical contents.
- Independently generated CDT/polynomial constants from C matched regeneration.
  Two negative checks altering a CDT entry or polynomial coefficient in a C copy
  each failed at the corresponding certification theorem.
- Mode-specific Hyperball constants were generated independently by compiling
  the actual expressions in the pinned C source. GCC 11.4 and Clang 14 outputs
  were byte-identical, and the final gate also confirmed regeneration equality.
  A negative check changing one digit of a generated theory's scale constant
  confirmed rejection by the provenance gate. Tests do not modify actual files.
- New Gaussian certificates were regenerated using integer interval arithmetic
  and compared with stored contents. EasyCrypt checked real containment of
  outward-rounded operations and all required numerical inequalities.
  Temporary certificates changing a squaring step or one CDT comparison value
  failed in the actual checking theorems; unchanged controls passed. Distinct
  temporary module names and data identifiers prevented the original specification
  from being loaded instead.
- Exponential certificates were regenerated with exact rational arithmetic.
  An independent implementation produced the same 66 integer control coefficients.
  EasyCrypt checked not only basis conversion/nonnegativity but also all six
  identities with the actual polynomial. Negative control coefficients, an
  internally consistent positive certificate for a different polynomial, and
  changed reference coefficients all failed. Valid controls passed and actual
  files remained unchanged.
- The proof gate was confirmed to reject `Proofs:weak`, `Proofs:report`,
  unfinished proofs, new axioms, and disallowed constrained declarations.
  NTT exceptions apply only to specific support files pinned by name and hash.
- Preflight failures such as source drift were confirmed to replace the latest
  record with FAIL rather than leave a previous PASS in place.
- EasyCrypt returning success at EOF with an open proof, missing `qed`, or
  unresolved clone obligation was reproduced. Appending a final checking lemma
  to a same-basename temporary copy rejects these cases. Valid proofs, inline
  proofs, and clone/realize passed; regression tests also checked source
  preservation, exit codes, and temporary-file cleanup.
- Hashes of four historical files used for SHAKE support matched the preserved
  Git snapshot. Imported portions were adapted to the current signing extraction,
  and both local files were freshly verified.
- The pinned official C distribution, production Jasmin sources, and `archive`
  materials were not modified.

Independent review found missing connections to the actual production-context
helper and to the integer meaning of rounded results; these were supplied by
`ProductionApiCorrectness` and `SigmaRoundingCorrectness`, respectively.
The final review approved the current component scope.
Independent review of the Hyperball stage approved word-level partial correctness
of the actual complete function and mode wrappers. It checked the premises of
multiple Gaussian calls, actual fixed-point/scaling/norm calls, first-acceptance
history, final byte/counter, and return-value uniqueness. It confirmed that public
theorem premises did not hide the desired conclusions, numerical fit, convergence,
or termination assumptions. Unconditional mathematical-norm guarantees, real
Newton convergence/error, probability distributions/termination, a separate
equivalence to the FIPS bit specification, and complete API composition remain
obligations.

Final independent review of the CDT stage checked the official nonnegative
Gaussian definition, infinite normalization/tail, interval certificates,
the +1 boundary of strict comparison, actual Jasmin calls, the 1/2
statistical-distance factor, and the theorem for arbitrary output sets.
It separately reviewed name separation and valid controls in the final mutation
tests. Approval is limited to the single-CDT explicit uniform-input experiment.
It does not extend to the official specification's separate Rényi bound,
sigma76 rejection sampling, actual SHAKE uniformity/independence, Hyperball,
or the complete signature distribution.

Independent review of the exponential stage checked the actual input range,
signed Horner interpretation, 24+3 error composition, termination of actual calls,
the conditional sigma call, and the clipped/even acceptance formula.
Its comparison target was `α(actual rounded)·exp(-actual xi/2^48)`.
Subsequent stages proved raw-exponent error and the difference between the two
zero rules, connecting them to acceptance probability averaged over explicit
uniform noise. One-sided ceiling, the official Rényi bound, and the full Gaussian
output distribution remain separate obligations.

## Meaning of the verdict

This record documents successful checks of component theorems registered in
[CLAIMS.md](CLAIMS.md). Checking 102 generated files is not counted as 102
functional-correctness theorems. Complete KeyGen/Sign/Verify, unconditional
termination/distributions of concrete SHAKE/Hyperball execution, Sign→Verify
composition, OS memory access, and complete correctness of generated assembly
remain unfinished. NTT arithmetic assumptions remain in the
[assumption inventory](manifests/ntt-assumptions.md).

Independent review of the pre-rounding acceptance-formula stage checked the
exact square/exponent formulas, Gaussian-weight ratio, exceptional interval of
the two zero rules, actual 72+48-bit probability experiment, and averaging
composition. Exceptions were explicit, without overstating the result as a
small error for every fixed candidate. The conditional distribution after
acceptance, rejection normalization, official Rényi bound, concrete SHAKE,
and the complete API were retained as obligations.

Independent review of the joint-output stage checked actual unsigned return
values, events for all output sets, the independent 83+72+48-bit experiment,
infinite Gaussian support and unbounded integer rounding, pointwise error after
applying the indicator, CDT kernel contraction with factor 1, and final numerical
bounds. It confirmed that the then-current theorems hid no fit/accuracy/output-set
restrictions and did not claim post-acceptance normalization or actual SHAKE
properties from the joint-probability result.

Independent review of the conditional-distribution stage checked the connection
between actual/ideal native distributions and program probabilities, distinct
denominators, numerical acceptance lower bounds and final discharge of positivity
premises, mass 1, and a strict statistical-distance bound via a common non-strict
error bound for all events. The reference distribution was the previous ideal
experiment conditioned on acceptance. The review confirmed that, at that time,
the conditional-distribution result did not claim a separate Gaussian
mass-function identification, signs, rejection retries, or actual SHAKE.

Independent review of the Gaussian-identification stage checked independent
normalization over all integers, restricted quotient/remainder reindexing based
on absolute convergence, the infinite range of ideal x, the Z/2 zero-correction
factor, rounding after taking absolute value, and the exact conditional-distribution
equality. It confirmed that the actual distribution's existing error transfers
through that equality alone, without additional claims about actual signs,
retries, SHAKE, or complete API correctness.
