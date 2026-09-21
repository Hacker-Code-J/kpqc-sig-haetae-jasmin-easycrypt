# An explicit Gaussian law for accepted sample magnitudes

Define an independent integer Gaussian G by

```
rho(k) = exp(-k*k/2^153),  k in Z
Z      = sum_{k in Z} rho(k)
Pr[G=k]= rho(k)/Z.
```

The target output is

```
R = floor((abs(G)+32768)/65536).
```

`Gaussian76Spec` defines this distribution without a CDT table, acceptance
program, machine word or sampler-derived normalizer. The parameter `2^76`
occurs in the Gaussian weight before the sixteen-bit rounding.

## Independent infinite normalization

`Gaussian76Properties` proves positivity and symmetry of rho, absolute
summability over **all integers**, `Z>=1`, and total probability one. The proof
uses the geometric ratio `q=exp(-1/2^153)`, with `0<q<1`. On nonnegative
integers, `rho(k)<=q^k`; a reflected copy bounds the negative half. The existing
generic geometric-series proof is reused. No numerical exponential oracle,
finite cutoff or acceptance-probability definition of Z is used.

## Exact identification of the prior ideal experiment

Let `N=2^72` and `H16=sum_{x>=0} exp(-x*x/512)`. The prior ideal experiment
samples nonnegative Gaussian x and uniform y in `[0,N)`, then uses its raw
Gaussian acceptance formula. For every legal x,y, including arbitrarily large
ideal x, the checked identity is

```
exp(-x*x/512) * raw_accept(x,y)
  = alpha(z) * rho(z),  z=N*x+y,
alpha(0)=1/2, alpha(z>0)=1.
```

The candidate map is one-to-one on `x>=0, 0<=y<N`, with inverse integer quotient
and remainder. `GaussianBlockReindex` proves the block-sum identity by quotient
fibres and translations, with all summability requirements discharged. It does
not enumerate `2^72` values or claim a bijection from unrestricted Z×Z to Z.

For every output set S, the ideal joint accepted mass is therefore

```
J(S) = sum_{z>=0}[alpha(z)*rho(z)*1_S(round(z))] / (N*H16).
```

Folding the signed Gaussian counts zero once and every positive magnitude twice.
Thus `sum_{z>=0} alpha(z)*rho(z)=Z/2`, and ideal acceptance has the exact value
`Z/(2*N*H16)`. Conditioning cancels the common positive factor exactly.

The resulting checked identity is

```
sc_ideal_conditioned = g76_rounded = law(floor((abs(G)+32768)/65536)).
```

The previous reference experiment has now been identified with this independent
Gaussian formula. The actual implementation comparison is still approximate.

## Explicit probability of every rounded value

Let `w(0)=rho(0)=1`, `w(z)=2*rho(z)` for positive z, and `w(z)=0` for negative z.
Then

```
Pr[R=0] = (1 + 2*sum_{z=1}^{32767} rho(z)) / Z
Pr[R=r] = 2*sum_{z=65536*r-32768}^{65536*r+32767} rho(z) / Z,  r>=1
Pr[R=r] = 0,  r<0.
```

The interval is lower-inclusive and upper-exclusive in the EasyCrypt finite
sum. The zero bin contains 65,535 signed lattice points. Both `G=32768` and
`G=-32768` map to R=1, while `±32767` map to R=0. Absolute value precedes
rounding. The returned probability is the sum across its rounding bin; this
is not an identification with pointwise Gaussian weights on the coarser grid.

## Actual Jasmin consequence

Let A be the actual single-attempt acceptance event under independent uniform
83-bit CDT, 72-bit noise and 48-bit rejection inputs. The previously checked
conditional distribution `sc_actual_conditioned(p)` comes from the actual
extracted sampler and uses the unsigned rounded magnitude. Rewriting the exact
reference identity transfers the existing error without adding a new term:

```
SDist(sc_actual_conditioned(p), law(R)) < 2^-39.
```

Both distributions have total mass one, and the same bound applies to the
probability difference for every integer output set. The base template p is
unrestricted. A separate theorem exposes the per-value error against the finite
bin formula above.

The subsequent [retry and batch proofs](gaussian-retries-and-batches.md)
connect this law to an operational loop calling the extracted attempt with
fresh independent inputs. They establish almost-sure termination, exact
first-accepted and ordered-batch laws, finite candidate-prefix bounds, and
conditional concrete buffered termination under an adequate-prefix premise.

## Scope and reproduction

The mathematical Gaussian G is signed so that its absolute value can define
the magnitude target. This does not prove the implementation's later sign
handling. The later retry proofs cover explicit independent inputs. Concrete SHAKE
randomness, a buffered iid-controller probability law, the published Renyi
guarantee, Hyperball mathematics and complete signature APIs remain separate
obligations.

The seven new files cover the independent Gaussian definition and normalization,
block reindexing, folding, kernel cancellation, rounding bins and final
identification/actual transfer. At the Gaussian-identification milestone, all 113 non-NTT files passed fresh
integrated checking as independent main targets with `-no-eco`, `Proofs:check`
and the EOF completion guard. All 18 gate regression tests passed. Previous NTT
records remain pinned with unchanged hashes; every prior proof, implementation
and extraction source is unchanged. See `../VALIDATION.md` and the verification
manifest for exact source hashes and timing.

| File | Main checked result |
| --- | --- |
| `Gaussian76Properties` | `g76_rho_summable`, `g76_normalizer_ge1`, `g76_distr_mu1`, `g76_distr_ll` |
| `GaussianBlockReindex` | `gb_block_sum` with explicit summability and support |
| `Gaussian76Kernel` | `g76_full_contribution` on the full integer domain |
| `Gaussian76Folding` | `g76_accept_weight_sum`, `g76_rounded_event_law` |
| `Gaussian76Rounding` | `g76_rounded_mass`, `g76_rounded_zero_mass`, `g76_rounded_zero_ties` |
| `Gaussian76Identification` | `g76_ideal_conditioned_eq`, `g76_gaussian_mass`, `g76_actual_gaussian_correct`, `g76_actual_rounded_mass_error` |

The exact Gaussian definition is in `Gaussian76Spec`. No new project axiom,
unsupported series interchange, finite ideal truncation or numerical oracle
is part of the proof.

```
make -C haetae-1.2.0-easycrypt verify-new
make -C haetae-1.2.0-easycrypt test-gate
```
