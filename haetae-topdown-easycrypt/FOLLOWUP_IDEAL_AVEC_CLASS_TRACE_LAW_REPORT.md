# Follow-up: ideal `avec` class-trace law

## Result

`PROVED-IDEAL-LAW`

For `q = 64513`, one ideal `avec` coefficient is sampled uniformly from
`0..q-1`.  Adding an arbitrary integer `pre_bp` modulo `q` is proved to be a
permutation of that distribution.  Applying the finalized-`s2` six-class map

```text
0                    -> class 0
q - 1                -> class 1
all other rho         -> class 2 + (rho mod 4)
```

therefore gives the exact class counts

```text
(1, 1, 16127, 16128, 16128, 16128)
```

and the corresponding point masses obtained by division by `64513`.

## Formal surface

`Mode2FaithfulSecurityIdealAvecClassTraceLawPostFreeze.ec` proves:

- `ideal_avec_parameter_certificate`, tying the ideal modulus to
  `KeygenM23FinalizeSemantics.q` and fixing the trace shape to `2 x 256 = 512`;
- `ideal_avec_shift_uniform`, uniformity after an arbitrary modular shift;
- explicit, unique preimage lists for all six classes, including their support
  and exact sizes;
- `ideal_avec_class_distribution_point`, the exact point mass of every valid
  class, together with zero mass outside classes 0 through 5;
- `ideal_avec_shifted_class_distribution_point`, the same exact law after any
  `pre_bp` shift;
- a canonical iid 512-coordinate class distribution reshaped into two ordered
  rows of 256, with exact coordinate marginals and point masses; and
- both marginals of the independent product with an arbitrary lossless
  `pre_bp`/secret carrier.  This product leaves all correlations internal to
  that retained carrier untouched.

No axiom, admit, or externally trusted count is used by the EasyCrypt proof.

## Independent executable certificate

`check-mode2-ideal-avec-class-counts.py` exhaustively enumerates all 64513
residues, confirms the six exact counts and probability sum, and checks that
modular addition is a permutation for negative, boundary, and large offsets.
It also requires the formal-law symbols and pins both checker and theory hashes
in `mode2-ideal-avec-class-counts.json`.

## Boundary

This result does not establish:

- equality between deterministic SHAKE/ExpandVecA output and iid ideal
  coefficients;
- independence between `pre_bp` and the retained secret carrier;
- a law conditioned on KeyGen acceptance;
- a joint distribution of acceptance, score, and ordered class trace;
- a numeric value for the ideal mass of
  `accepted /\ P8_bad(ordered trace)`; or
- an actual-program probability without the existing `delta_xof` transport
  boundary.

## Next research obligation

The next useful theorem must combine this exact iid class-trace law with the
ideal acceptance/score semantics in a single joint summary distribution.  Its
target is

```text
mu ideal_summary
  (accepted and ordered_class_trace_p8_bad(trace)) <= epsilon_p8.
```

That is now the narrowest unresolved quantitative bridge.  It must preserve
the dependence created by the acceptance predicate; multiplying an
unconditional trace probability by an acceptance probability would be
unsound without a new independence or conditional-law proof.
