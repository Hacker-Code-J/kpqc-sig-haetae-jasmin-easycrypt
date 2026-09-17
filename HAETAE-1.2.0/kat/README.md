# HAETAE Known Answer Tests (KAT)

This directory holds the **golden** KAT vectors for HAETAE:

| file | meaning |
|------|---------|
| `PQCsignKAT_haetae_mode{2,3,5}.req` | NIST DRBG seeds + message lengths (algorithm-independent) |
| `PQCsignKAT_haetae_mode{2,3,5}.rsp` | keys / signatures produced by HAETAE for those seeds |
| `SHA256SUMS` | SHA-256 of every `.req`/`.rsp` above — a compact, reviewable fingerprint |

## The invariant CI enforces

> A fresh build of `reference_implementation/` **and** the AVX2 / AVX-512
> `optimized_implementation/` must regenerate these files **byte-for-byte**.

The [`kat` workflow](../.github/workflows/kat.yml) runs on every push and PR to
`main`. For each variant it builds only the KAT targets, runs them, and `diff`s
the output against the files here. Any mismatch fails the build.

## Run it locally

From the repo root (`kat.sh` drives the whole thing — build, generate, compare):

```bash
./kat.sh list          # show variants + whether this CPU supports avx2/avx512
./kat.sh check         # ref + avx2 + avx512 (avx512 auto-skipped if unsupported)
./kat.sh check ref     # just the reference implementation
```

`check` exits non-zero on any mismatch and prints the differing SHA-256s and a
diff excerpt.

## When you *intentionally* change the KAT

Any source change that alters HAETAE's output (a spec fix, a sampler change, new
parameters, …) **will** change these vectors, and that is expected. Because the
reference implementation *defines* the algorithm, regenerate from it:

```bash
# 1. make your source change under reference_implementation/src (and mirror it
#    in optimized_implementation/ so the variants still agree)
# 2. regenerate the committed vectors + SHA256SUMS from the reference build:
./kat.sh update
# 3. review the change — the diff you actually read is SHA256SUMS:
git diff kat/SHA256SUMS
# 4. commit the source change and kat/ TOGETHER, in the same commit/PR:
git add reference_implementation optimized_implementation kat/
git commit -m "…: update HAETAE <what changed> (regenerates KAT)"
```

Then CI passes again, because the committed vectors once more match a fresh
build.

### Why this is safe

- You **cannot** hand-edit a `.rsp` to make CI green — the check rebuilds from
  source, so a vector that doesn't correspond to the code is caught.
- You **cannot** silently change behavior — a source change that moves the
  output forces a `kat/` change in the *same* PR, so it always shows up in
  review. If you forget to run `./kat.sh update`, CI fails and prints the exact
  command (and uploads the freshly generated KAT as a build artifact).
- Reviewers approve the tiny `SHA256SUMS` diff plus your explanation of *why*
  the vectors moved, instead of scrolling through megabytes of hex.

> A KAT change is a change to the algorithm's observable behavior. Treat an
> unexpected `SHA256SUMS` diff in review as a red flag until the author explains
> it.

## Notes

- The KAT build needs **OpenSSL** headers (`libssl-dev`) — the NIST DRBG in
  `kat/rng.c` uses AES-CTR from libcrypto.
- The AVX-512 leg only runs where the runner CPU exposes
  `avx512f/bw/dq/vl`; otherwise the workflow emits a warning and skips that leg
  (set `KAT_REQUIRE_ALL=1` locally to make an unsupported variant fatal instead).
