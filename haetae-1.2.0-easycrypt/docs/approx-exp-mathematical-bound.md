# Mathematical error of the actual approximate exponential

Let `M=2^48`, let `X` be the unsigned integer input of `approx_exp`, and let
`A` be its unsigned output. For `0 <= X` and `3*X <= 2*M`, the checked actual
Jasmin contracts prove termination and

```text
| A/M - exp(-X/M) | <= 27/M < 2^-43.
```

The integer domain is proved for every 26-byte sigma76 input `p`:

```text
0 <= uint(sigma_exp_argument(p)) <= 183103063064576
3 * uint(sigma_exp_argument(p)) <= 2 * 281474976710656.
```

The final theorem `ApproxExpNumericalCorrectness.sigma76_approx_exp_numerical_total`
therefore requires only that the actual signer routine receives that argument.
It has no extra domain, intermediate-fit, polynomial-accuracy or termination
premise. The public sampler and internal sampler routines also have numerical
contracts on the stated domain.

## Source and proof connections

[Specification 260904](https://drive.google.com/file/d/1H2SFqZFG5BcWH--bJKssvXaSG0Sd3mUx/view),
section 5.1.1, Listing 1 (printed page 32), gives the degree-ten evaluator and
the ceiling multiply. Its 11 coefficients match the pinned reference and the
Jasmin computation. The source PDF is identified by SHA-256 in
[`specification-sources.json`](../manifests/specification-sources.json).

The mathematical target in this stage is the real function `exp(-X/M)`.
The polynomial with the actual integer coefficients divided by `M` is an
intermediate object, not an assumed correct specification of that function.

| Layer | Checked result |
| --- | --- |
| `SigmaExpInputBounds` | Domain of the exact sigma76 exponent expression, including CDT output 166, subtraction, bit merge and rounding |
| `ApproxExpWordCorrectness` | Actual word computation equals integer ceiling-Horner; every prefix and rounded multiply fits signed64; final unsigned value is exact |
| `ApproxExpWordCorrectness.ae_rounding_error3` | `0 <= A/M-P(X/M) <= 3/M` |
| `Bernstein10Correctness` | Exact change of polynomial basis and nonnegativity from checked integer controls |
| `ApproxExpCertificateChecks` | All six certificate identities, all 66 nonnegative controls, and their exact identities with the actual coefficient polynomial |
| `ExponentialGridComparison` / `ApproxExpPolynomialBound` | `|P(X/M)-exp(-X/M)| <= 24/M` on the entire valid integer grid |
| `ApproxExpNumericalCorrectness` | Composition into the actual-procedure bound `27/M < 2^-43`, with termination |

The signed64 result bounds justify integer interpretation at the Horner
boundaries. They do not say that every unsigned register operation avoids
wrapping: the existing word-to-ceiling refinement accounts for the intentional
word arithmetic inside `smulh48`.

## Analytic certificate method

With `h=1/M` and `E=24/M`, set `U(z)=P(z)+E` and `L(z)=P(z)-E`. The certificate
proves

```text
(M+1)*U(z+h) - M*U(z) >= 0
(M-1)*L(z) - M*L(z+h) >= 0
```

on `[0,2/9]`, `[2/9,4/9]`, and `[4/9,2/3]`. Each residual is a degree-ten
polynomial. Exact fractions are cleared with a positive common denominator,
and EasyCrypt checks its identity with the proposed Bernstein form.

The standard exponential laws give
`1-h <= exp(-h) <= 1/(1+h)`. Starting from the checked bounds at zero, induction
on the integer grid propagates `L(X/M) <= exp(-X/M) <= U(X/M)`. It does not
enumerate the approximately `2^48` possible arguments or use sampled numerical
tests in place of the universal statement. The result concerns the evaluator's
integer grid; it is not advertised as a separate bound for arbitrary real inputs.

The generator uses Python integer/Fraction arithmetic and does not evaluate
the exponential numerically. Its output is a proposed certificate, not a trusted
accuracy assertion. Defined `[opaque]` lists prevent eager symbolic expansion;
the relevant checks explicitly unfold them.

## Conditional acceptance probability

`SigmaRejection48Experiment.sample(p)` fixes the candidate bytes, draws a uniform
48-bit integer, replaces only bytes 11 through 16, and calls the actual extracted
`SamplerTarget.M.__sample_gauss_sigma76_regs`. It returns the actual acceptance bit.

Write `r` for the **rounded 64-bit candidate word**, `T` for the approximate
exponential threshold, and `alpha(r)=1/2` if `r=0`, otherwise `1`. The exact law is

```text
Pr[accept] = alpha(r) * min(2^47, max(0, ceil(T/2))) / 2^47.
```

This handles the evenized rejection word, strict comparison, saturation and
the rounded-zero correction. The threshold's required signed-comparison range
is derived from the actual evaluator bounds.

`SigmaExpAcceptanceCorrectness.sigma_exp_acceptance_error` proves, for every
fixed candidate input `p`,

```text
| Pr[accept] - alpha(r) * exp(-uint(sigma_exp_argument(p))/M) |
  <= alpha(r) * 28/M < 2^-43.
```

## Exact scope

- The numerical function bound needs no randomness assumption. Uniformity is
  explicit only in the separate 48-bit conditional acceptance experiment.
- The acceptance reference retains the **actual quantized exponent** and the
  **actual rounded-zero rule**. Accuracy against the ideal raw exponent
  `y*(y+2^73*x_CDT)/2^153`, and the relation of rounded zero to raw-candidate zero,
  remain separate obligations.
- Neither the C comment's one-sided ceiling claim nor the specification's
  Renyi-divergence bound is assumed or established by this absolute-error result.
- This is not the output-distribution theorem for the complete sigma76 rejection
  sampler, an independence/uniformity theorem for concrete SHAKE, a Hyperball
  distribution theorem, or full signature correctness.
- The existing EasyCrypt real/word libraries, SMT tools and Jasmin extraction
  semantics remain in the trusted foundation. No project axiom asserting an
  approximation bound or certificate validity is added.

## Reproduction

```sh
make -C haetae-1.2.0-easycrypt verify-new
make -C haetae-1.2.0-easycrypt test-gate
```

The gate regenerates the certificate and checks every local theory as a main
target with proof checking and an EOF completion guard. Regression fixtures use
distinct module names and fully qualified data. They reject a negative control
even when its power coefficients are updated consistently, a positive internally
consistent certificate for the wrong polynomial, and a changed reference
coefficient. Matching unmodified controls must pass.
