# License status

The primary upstream repository,
[`formosa-crypto/formosa-mldsa-correctness`](https://github.com/formosa-crypto/formosa-mldsa-correctness),
does not contain a `LICENSE`, `COPYING`, or equivalent grant at commit
`2dc59703c38bb29bb3f6e3a765f0a9934e143263`. No such file was found in the
repository history available at import time.

Consequently, no license for the primary `proofs/`, `config/`, workflow, or
build files should be inferred from this snapshot. Keep it for local research
and evaluation only unless the copyright holders provide an explicit license
or permission. In particular, do not assume that the licenses of dependencies
also cover the top-level correctness artifact.

Materialized dependency subsets retain their upstream license files:

- `submodules/formosa-mldsa/LICENSE`: Apache-2.0;
- `submodules/formosa-mldsa/formosa-keccak/LICENSE`:
  CC0-1.0 OR Apache-2.0;
- `submodules/formosa-mldsa/formosa-keccak/submodules/crypto-specs/LICENSE`:
  CC0-1.0; and
- `submodules/jasmin-compiler/LICENSE`: MIT.

`LICENSES/EasyCrypt-LICENSE` records the MIT license of the pinned EasyCrypt
toolchain source, which is not itself vendored here.
