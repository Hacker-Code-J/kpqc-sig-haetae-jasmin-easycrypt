# Signed Gaussian observations and implemented sign application

All 7 new proof files passed individual and integrated fresh checks. The
complete non-NTT replay passed 151/151 main targets with `-no-eco`,
`Proofs:check` and the EOF completion guard; all 18 gate regressions passed.
The 144 unchanged targets were checked first, then every new frozen target.
Final inventory and source hashes matched before PASS. The 163-file local
inventory also retains 12 unchanged NTT targets, whose prior results were
preserved without rerunning them in this milestone. All 102 fresh extractions
matched. The production implementation was unchanged, so KAT was not rerun.

The [iid byte-buffer model](gaussian-iid-buffer.md) calls the extracted Jasmin
sign-copy, carry and finite Gaussian consumer with independent uniform byte
blocks. This milestone follows the sign bytes through that same model. Its
randomness assumption remains explicit; it is not a theorem that the concrete
SHAKE stream has independent uniform bytes.

## Signs and the complete unsigned state

The first 32 bytes supply 256 bits in little-endian order. Bit `i` is bit
`i mod 8` of byte `sign_offset + i div 8`. The candidate data start after
those 32 bytes. Splitting the initial uniform 6664-byte draw into independent
32-byte and 6632-byte draws permits the sign draw to move after the entire
unsigned rejection loop.

The proved independence statement includes the complete output array and
both square-accumulator words. Thus any deterministic scale computed from
that unsigned state is also independent of the sign bits. It does not assert
that the accumulator itself has an ideal Gaussian square-sum distribution.
For the decoded bits `B`, the complete unsigned state `U`, and arbitrary
events `S` and `A`, the factorization is:

```
Pr[B in S and U in A] = Pr[Uniform256Bits in S] * Pr[U in A].
```

The arrays start at arbitrary word values under the existing `gib_bounds`:
request 256 or 257, valid sample region, and a valid 32-byte sign region.
Only this 32-byte sign window is freshly uniform; the rest of the sign array
retains its caller-provided values.

The request-257 dummy still contributes to the square words and consumes an
accepted candidate. Only the first 256 magnitudes have stored output slots
and corresponding sign bits.

## Independent mathematical target

Let `G` be the all-integer Gaussian already defined independently of the
implementation:

```
Pr[G = k] = exp(-k*k / 2^153) / sum_{j in Z} exp(-j*j / 2^153).
R(k) = floor((abs(k) + 32768) / 65536).
T(k) = if k < 0 then -R(k) else R(k).
```

The signed target is the distribution of `T(G)`. In particular,
`T(32767) = T(-32767) = 0`, `T(32768) = 1`, and `T(-32768) = -1`.
Negative ties round away from zero. This is different from adding 32768 to
a signed value and then taking the quotient.

Gaussian symmetry identifies `T(G)` with an independent fair sign applied
to `R(G)`, including its complete mass at zero. Signing both magnitude
distributions in this way cannot increase statistical distance. The proved
256-coordinate result therefore preserves the existing bound `<2^-31`.

The raw signed observation is an unbounded mathematical integer:
`if bit_i then -uint64(sample_i) else uint64(sample_i)`.
It is not a cast of the sample word to signed64, and it is not yet the final
scaled Hyperball coefficient.

## Actual sign application after scaling

`__fixpoint_mul_rnd13_regs` first performs the implemented word multiplication
and rounding, then applies XOR/add negation and truncates to 32 bits. If `M`
is the nonnegative integer decoded from that implemented rounded word, the
word result is `W32.of_int(if bit then -M else M)`.

Reading that result as a signed32 integer gives exactly `+M` or `-M` when
`M <= 2147483647`. This explicit fit premise is retained. The statement uses
the implemented scaling and rounding operations, including their word
semantics; it does not replace them with exact real multiplication.

The actual vector procedure also retains its storage bounds:
`0 <= left_count <= 2048`, `0 <= count-left_count <= 2048`, and
`count <= 4096`. Its fit premise applies to every active coefficient.

The scale routine uses the same global coefficient index for the sample and
the sign bit. Connecting a local sample/sign window to this routine therefore
requires `sample_offset = 8 * sign_offset`; the checked local coefficient
corollaries state that condition explicitly. The raw signed observation law
itself allows the two valid offsets to be chosen independently.

The scale's numerical accuracy, its fit condition on all reachable Hyperball
states, integer accumulator bounds, concrete SHAKE randomness, the published
Rényi guarantee and complete KeyGen/Sign/Verify proofs remain separate tasks.

## Checked public contracts

| Contract | Meaning |
| --- | --- |
| `gsb_uniform256` | Actual little-endian byte decoding has the fair256-bit law. |
| `gsi_actual_redraw` | Independently replacing the sign window after the unsigned loop preserves the entire returned-tuple law. |
| `gsi_sign_state_independent` | Sign events factor from arbitrary events on the full output and square-word arrays. |
| `gst_target_eq` | The independent symmetric rounded Gaussian equals a fair sign applied to its rounded magnitude. |
| `gsc_actual_joint_law` | The operational sign/magnitude observation has the exact product law. |
| `gsc_actual_signed_law`, `gsc_actual_correct` | The operational signed256 observation has the exact implementation distribution, terminates almost surely and has Gaussian distance `<2^-31`. |
| `hss_regs_word_total`, `hss_scale_samples_signed_total` | Actual scalar word sign application and the vector signed32 observation under the explicit fit condition. |

## Reproduction

From the repository root, the complete non-NTT proof gate and its regression
tests are:

```sh
make -C haetae-1.2.0-easycrypt verify-new
make -C haetae-1.2.0-easycrypt test-gate
```

The gate checks each local proof as a main target with fresh proof checking
and an EOF completion guard. Final inventory, hashes and evidence are stored
in [verification-results.json](../manifests/verification-results.json).
