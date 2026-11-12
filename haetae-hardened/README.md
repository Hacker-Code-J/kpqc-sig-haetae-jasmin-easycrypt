# HAETAE Hyperball arithmetic hardening

Directory renames are tracked by per-file before/after hashes in
`layout-migration.json`. Existing baseline/toolchain locks and historical
verification results retain their original bytes and paths; current path
translation is applied by `scripts/materialize.py`. A rename record does not
approve existing source mismatches or new proof changes.

This separate implementation preserves the existing HAETAE Jasmin implementation
and adds checks for Hyperball coefficient conversion and sum-of-squares overflow.
EasyCrypt verifies that **the actual integer sum of squares of a vector accepted
by the hardened variant is at most the mode's bound**.

The subsequent [Gaussian rejection-rate and expected-count proof](gaussian-acceptance.md)
connects an actual candidate rejection probability `<5%` with an expected number
of candidate attempts until success `<20/19`, under an independent uniform
randomness model. This is distinct from termination of outer Hyperball retries.

The [exponential-approximation Rényi proof](gaussian-renyi.md) compares the actual
output distribution after acceptance with a reference distribution using exact
exp and the same CDT, quantized exponent, handling of 0 and rounding. For integer
orders 2–1024, the nonlogarithmic Rényi quantity is at most `1+2^-68`, below the
specification's bound `1+2^-45.1`. Connections to the full ideal Gaussian or a
signing-query budget are separate from this single-output comparison.

The [single-attempt Hyperball Rényi proof](hyperball-renyi.md) composes the
single-sample bound across raw squares, dummies, signs and each mode's complete
batch. For the **output candidate and acceptance bit** in an explicit iid byte
model calling actual hardened helpers, it proves
`R_α ≤ (1+2^-68)^D < 1+2^-56` in both directions for integer orders 2–1024.
Rejected candidates are included; the Hyperball distribution conditioned on
acceptance and the distribution of outer retries are separate from this bound.

In `N = Σ signed32(y1[i])² + Σ signed32(y2[j])²`, sums and squares use unbounded
integer arithmetic. Neither `N < 2^64` nor a safe interval for Gaussian inputs
is assumed before the check.

| Mode | Number of coefficients checked | Integer sum-of-squares bound |
| --- | ---: | ---: |
| 2 | 1024 + 512 | 6,505,809,026,482,176 |
| 3 | 1536 + 768 | 22,510,896,139,993,088 |
| 5 | 1792 + 1024 | 33,503,371,683,954,688 |

The bounds are constants from the preserved reference implementation. This
directory name does not identify a new official release. It is a research
hardening variant that explicitly rejects inputs on which its behavior differs
from the existing implementation; the library names and SONAME also include
`hardened`.

## Checks and proved properties

| Target | Property | Termination scope |
| --- | --- | --- |
| Scalar conversion | Computes the final rounding without addition overflow and returns a failure mask if magnitude `M > 2147483647`. The stored 32-bit coefficient is the same as in the existing implementation. | Always terminates |
| Vector conversion | Processes both arrays and accumulates failures. On acceptance, every active sample's magnitude before conversion is at most `2147483647`. | Always terminates |
| Sum of squares | The returned word is `N mod 2^64`, and the overflow mask is 0 if and only if `N < 2^64`. | Correct within the array-length bounds and always terminates |
| Acceptance decision | Array-length conditions alone imply `accepted = 1 ⇒ N ≤ bound`. Sample, sign and scale arrays are arbitrary. | The finite decision function always terminates |
| Actual call paths | Connects the same acceptance property to freshly extracted signer, standalone Hyperball and public phase paths. | For complete Hyperball, the property concerns **executions that return** |

Proof files are listed in [easycrypt/proof-targets.txt](easycrypt/proof-targets.txt).
Execution results and hashes from the previous tool environment are in
[verification-results.json](verification-results.json). Replay logs with the
2026.09 tools are recorded separately in `logs/`; historical PASS records are
not replaced by results attributed to the new tools.
The historical `ApiTarget` is not replaced with the new implementation. Instead,
separate `HardenedSignerTarget`, `HardenedHyperballTarget` and
`HardenedPhaseTarget` models are extracted from the new production sources.

The coefficient-conversion check tests
`M = floor((uint64(r1) + 16384) / 32768)` for the high word `r1` returned by
multiplication. This final addition is interpreted as integer addition. Earlier
fixed-point multiplication and Newton steps retain the existing word operations.
This therefore does not assert that all intermediate calculations agree exactly
with real arithmetic. The check uses the same bound for both signs, so it also
rejects `M = 2^31`, although that magnitude is representable as a negative value.

The check loops run to completion and accumulate failure status. Neither the
sum of squares nor internal failure masks are disclosed; only the final
acceptance bit required by the existing retry flow is disclosed. CT/SCT checks
use this explicit declassification condition.

## Differences from existing behavior and execution checks

All previously constructed counterexamples for modes 2·3·5 change from acceptance
`1` in the existing implementation to rejection `0` in the new one. Output
coefficient words are unchanged. This is checked both in test functions and in
**the public functions of each mode's actual production library**. No claim is
made that corresponding SHAKE seeds exist or that the counterexamples are
reachable through the complete signing API.

Boundary checks independently trigger coefficient-conversion and norm failures.
For example, 16 coefficients of magnitude `2^30` each fit in 32 bits, but their
sum of squares is exactly `2^64`. The new decision rejects even when the
accumulation word wraps to 0.

Official KAT request and response files match for 100 cases per mode, 300 in
total. API boundaries, signing/verification and interoperability with the C
reference implementation are also tested. Passing KATs does not establish
equivalence with the existing implementation for all inputs; acceptance results
for the counterexamples above intentionally differ.

## Reproduction

Run from the repository root using Jasmin, EasyCrypt, a C compiler and OpenSSL
from the existing environment.

```sh
make -C haetae-jasmin -j1 libs
make -C haetae-hardened -j1 test
python3 haetae-hardened/tests/checked-hyperball.py
bash haetae-hardened/scripts/check-ct.sh
python3 haetae-hardened/tests/materialize.py
python3 haetae-hardened/tests/layout-migration.py
python3 haetae-hardened/tests/verification-gate.py
python3 haetae-hardened/scripts/verify.py
```

Environments already using a Why3 server may set `WHY3_SERVER_SOCKET`. The
verifier checks each new proof and every existing local proof it imports as
a main target. It uses `-no-eco`, `Proofs:check` and EOF completeness checks and
disallows project axioms, admits and verification-bypass pragmas. Other existing
proofs are preserved by hash and distinguished from those rechecked in this run.

The theorems concern Jasmin's `barray` extraction model. Array-size and pointer
contracts for actual calls, together with the toolchain, remain within the trust
boundary. These results must not be interpreted as proving memory safety for
arbitrary pointer use.

[baseline-lock.json](baseline-lock.json) pins hashes of 542 original Jasmin,
EasyCrypt, reference-implementation and archive files from the baseline commit.
Only the three change fragments in [overlay](overlay/) are managed separately;
`scripts/materialize.py` creates the build copies. It stops if original hashes
differ or output paths contain symlinks. Only the declared changes to 2026.09
extraction and verification settings are checked through the separate migration
lock below. Generated `jasmin/`, `include/`, `test/`, `kat/` and `build/`
directories are not stored redundantly in Git.

## Preserved Jasmin/EasyCrypt toolchain migration record

The existing `baseline-lock.json` and four `*-results.json` files are preserved
as historical records. [toolchain-migration-lock.json](toolchain-migration-lock.json)
pins those lock-file hashes and the baseline commit, and records old/current
hashes for each changed, deleted or added path in the original extraction and
verification setup. At that time, 409 of the original 542 files retained the
same bytes; 133 changed/deleted files and 20 new support-array and record files
were declared. These counts describe the migration snapshot, not the current
inventory including subsequent NTT proofs, public documentation and path changes.
Jasmin, C, archive files and existing specifications, theorems and premises are
preserved. Proof-body ports in 22 original files checked with the new tools are
restricted by their exact old/current file hashes in `PROOF_PORTS`.
The single `JModel` → `JModel_x86` import rename in `theories/ntt/Fq.ec` is pinned
separately in `MODEL_IMPORTS`. Merely changing ledger hashes in either list cannot
authorize other theorem, premise, definition, proof or model-import changes.
The original project's `manifests/2026.09-migration.json` records invariants and
individual runs for each port. The existing support-origin TSV is preserved;
the original verifier that checks approved port hashes and its mutation tests
are pinned by the exact two old/current file-hash pairs in `CONTROL_PORTS`.
Arbitrary ledger edits cannot substitute for these verification-control changes
either. Missing files, reappearing deleted files, undeclared generated files
and lock changes during a check also cause failure.

Proof-tactic ports were also applied to the hardened variant's
`CheckedAcceptanceCorrectness`, `CheckedNormCorrectness` and
`HyperballRenyiBatch`. Their theorems, premises and definitions remain unchanged;
the verifier includes these files in the source snapshot and full proof closure.

The hardened extraction changes from 54 files to 25. The new barray extractor
no longer emits unused `Array*` and `WArray*` files, and the import lists of the
three `Hardened*Target` models and the `Int` import in `BArray*` have changed.
The remaining program bodies of the three targets are unchanged. The five
arrays required by existing dependency proofs come from `generated/support`,
extracted separately in warray mode from the same Jasmin source in the original
project. The verified programs continue to use the barray model.
[extraction-manifest.json](extraction-manifest.json) binds the extractor version,
executable hash, options, production sources and hashes of all 25 outputs.

```sh
# Run from the repository root after completing the installation in env/README.md.
source env/activate.sh
python3 haetae-hardened/scripts/materialize.py --check
python3 haetae-hardened/scripts/extract.py --check
python3 haetae-hardened/tests/materialize.py
python3 haetae-hardened/tests/verification-gate.py
python3 haetae-hardened/tests/gaussian-rate-gate.py
python3 haetae-hardened/tests/gaussian-renyi-gate.py
python3 haetae-hardened/tests/hyperball-renyi-gate.py
python3 haetae-hardened/scripts/verify.py --group all
```

The preserved 2026.09 migration checks passed production reconstruction, fresh
extraction agreement, array namespaces and 71 verifier-regression checks.
The full proof matrix at that time had **all 290 mains PASS**. Each main's checked
hash is bound to that execution snapshot; this is not a recheck of all current
sources. The 207 original specifications/proofs and 30 hardened
specifications/proofs form 237 distinct authored mains; main checks of the 53
original generated files are also included. The 25 hardened generated files
were checked for fresh extraction agreement and imported by the hardened
proofs. These 25 are not added to the count of separately passed mains.
The [original migration record](../haetae-easycrypt/manifests/2026.09-migration.json)
links the full execution evidence from that time. Evidence within the public
repository is described in the
[preserved evidence guide](../evidence/toolchain-migration/README.md).
Recheck current sources with `bash scripts/reproduce.sh full` from the repository
root; historical PASS records and fresh execution results are not combined into
one success count.

The hardened verifier's `all` group checks 30 new specifications/proofs and 147
original dependency specifications/proofs, 177 in total, each as a main.
Dependency files overlapping with the original project were not counted twice
in the full matrix. New results include the migration lock and extraction
manifest in the source snapshot and record the hashes of the Jasmin, EasyCrypt
and Why3 executables used. Changing tools requires an explicit update of
extraction provenance and a full verification rerun.

Complete KeyGen/Sign/Verify correctness, termination of outer Hyperball retries,
the probability distribution of actual SHAKE, and security composition across
all signing queries remain separate tasks. Gaussian rejection rates and Rényi
bounds for exponential-approximation comparisons are handled by the subsequent
proofs linked above. The underlying code's MIT license and copyright are retained
in [LICENSE](LICENSE).
