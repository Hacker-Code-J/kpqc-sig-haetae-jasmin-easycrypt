# Gaussian rejection rate and expected candidate attempts

With independent uniform randomness, **a single actual Jasmin Gaussian candidate is rejected with probability less than 5%**.
In the model that generates fresh candidates in the same way until success, the
number of attempts `T`, including the successful candidate, has expectation
**`E[T] < 20/19 ≈ 1.052632`**.

| Quantity | Meaning and source |
| --- | --- |
| Rejection probability `< 1/20` | Corresponds to the Gaussian rejection rate `<5%` in [HAETAE specification 260904 §5.1.1](https://drive.google.com/file/d/1H2SFqZFG5BcWH--bJKssvXaSG0Sd3mUx/view). |
| Expected attempts `< 20/19` | A bound derived in this development from the actual acceptance probability `p > 19/20` and the retry-count law. It is not a number quoted from the specification. |
| Ideal acceptance probability `≥ 39/41` | A proof lower bound for the ideal candidate experiment used to compare against the actual implementation. It is not a measured acceptance rate. |

One attempt passes a single 26-byte candidate to `__sample_gauss_sigma76_regs`.
The 83 CDT bits, 72 additional noise bits and 48 rejection-decision bits are
mutually independent and uniform. Sampling all 26 bytes uniformly gives the
same law because the 5 unused bits do not affect the result.

The 5% bound averages over all these inputs. It does not assert an acceptance
probability of at least 95% for every candidate after fixing the CDT and noise
values. `T` includes both the first attempt and the final successful attempt.
It differs from the number of SHAKE blocks, buffer refills, the cost of batch
outputs excluding dummies, and the number of complete Hyperball retries.

## Proof connections

1. The existing rational certificate gives the normalization constant
   `H ≥ 41/2` for the sigma 16 nonnegative Gaussian. `H` counts the weight at 0 as 1.
2. Monotonicity of Gaussian mass and the existing lattice-sum theorem establish
   the ideal acceptance probability
   `p_ideal ≥ 1 − 1/H ≥ 39/41 > 951/1000`. The half weight of raw candidate 0 is
   retained; no Gaussian integral or new numerical assumption is introduced.
3. Apply the previously proved difference `< 2^-43` between actual and ideal
   acceptance probabilities. Thus `p > 951/1000 − 2^-43 > 19/20`, and the rejection
   probability is `< 1/20`.
4. Add an integer counter for analysis to the loop that calls the actual
   extracted function. Prove that erasing the counter preserves the output of
   the existing IID candidate-loop model, then prove the actual count's
   distribution, finiteness of its expectation and `E[T] = 1/p` to obtain `< 20/19`.

`GaussianAcceptanceProduction` directly calls the Gaussian functions in the
freshly extracted signer and standalone Hyperball code.
`GaussianProductionCounted` calls the same functions with fresh uniform 26-byte
inputs on each attempt and counts the actual attempts. Correspondence between
function bodies is checked by relational equivalence in EasyCrypt.

The probability model explicitly supplies independent uniform inputs in place
of concrete SHAKE execution. The Gaussian candidate loop terminates with
probability 1 in this model. Connecting concrete SHAKE through security
assumptions, termination of the outer Hyperball loop, the specification's Rényi
bound, and complete API correctness are separate tasks. The C/Jasmin executable
code was not changed at this stage.

## Files and reproduction

| File | Verification target |
| --- | --- |
| `GaussianAcceptanceConstants.ec` | Derive the required normalization constant and numerical margin from the existing certificate |
| `GaussianAcceptanceIdeal.ec` | Analytic lower bound on the ideal acceptance probability |
| `GaussianAcceptanceActual.ec` | Actual acceptance/rejection probabilities and a tail bound on consecutive rejections |
| `GaussianAcceptanceProduction.ec` | Connect actual production code to the uniform 26-byte experiment |
| `GaussianAttemptExpectation.ec` | Candidate-counting loop, count distribution and finite expectation |
| `GaussianAttemptProduction.ec` | Connect the same count and expectation results to the production candidate loop |

The files are in [easycrypt/proofs](easycrypt/proofs/). From the repository root:

```sh
make -C haetae-hardened prepare
python3 haetae-hardened/tests/gaussian-rate-gate.py
python3 haetae-hardened/scripts/verify.py --group gaussian-rate
```

Set `WHY3_SERVER_SOCKET` to use an already running Why3 server. Each new theorem
and imported local dependency theorem is rechecked as a main target, with
`-no-eco`, `Proofs:check` and EOF completeness checks. Fresh extraction agreement
and existing file hashes are also checked. The exact targets, hashes and
results are recorded in
[gaussian-acceptance-results.json](gaussian-acceptance-results.json).
The earlier hardened variant's [KAT and execution-check record](verification-results.json)
is preserved as historical evidence, including the hashes of its verifier and
target list at that time. The new record specifies the hash-comparison scope
for the verifier and list changed in this stage and for the executable code
and runtime artifacts that remain unchanged.
