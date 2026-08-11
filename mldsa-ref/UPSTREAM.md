# Vendored ML-DSA reference implementation

This directory is a source snapshot of the official CRYSTALS-Dilithium
repository, whose portable implementation is the reference implementation for
the scheme standardized as ML-DSA in FIPS 204.

- Upstream: <https://github.com/pq-crystals/dilithium>
- Revision: `d35ba3fe5449bee3e6d43e1f296c3ca818bd36be`
- Upstream branch at import: `master`
- Imported: 2026-08-04
- License: see `LICENSE`
- Standard: <https://csrc.nist.gov/pubs/fips/204/final>

The upstream working tree is retained verbatim except for its `.git`
directory; this provenance file is the only project-local addition. The
portable reference implementation is in `ref/`. The upstream `avx2/`
implementation and repository metadata are retained so that the snapshot can
be compared and tested exactly as published.

Upstream keeps the pre-standardization parameter-set names in its C API:

| Upstream name | FIPS 204 name |
| --- | --- |
| Dilithium2 | ML-DSA-44 |
| Dilithium3 | ML-DSA-65 |
| Dilithium5 | ML-DSA-87 |

From the project root, build and run the portable reference tests with:

```sh
make -C mldsa-ref/ref
./mldsa-ref/ref/test/test_dilithium2
./mldsa-ref/ref/test/test_dilithium3
./mldsa-ref/ref/test/test_dilithium5
make -C mldsa-ref/ref clean
```

Keep changes to vendored implementation files separate from upstream imports,
and update the revision above whenever refreshing the snapshot.
