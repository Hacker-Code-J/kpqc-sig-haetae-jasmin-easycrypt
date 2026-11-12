# Reviewed README link repair

The original review changed exactly two lines in `haetae-easycrypt/README.md`.
Both lines linked to evidence in a private thesis directory outside the repository.
The repair used these public repository locations instead:

- Full toolchain-migration result: `../evidence/toolchain-migration/haetae-full-proof-result.json`.
- Historical evidence location index: `../evidence/toolchain-migration/index.json`.

The surrounding claim remained 260/260 PASS for the historical run, with
`-no-eco`, `Proofs:check`, EOF completion checking, and the default prover selection.
The repair did not change implementations, proofs, or recorded verification results.

This English explanation replaces the displayed Korean patch; it is not a newly
executed check or an executable patch. The exact original is preserved in
[Git history](https://github.com/Hacker-Code-J/kpqc-sig-haetae-jasmin-easycrypt/blob/3336e4290e56b7588f0b8abe1ae30366730f461b/evidence/readme-publication-fix-20261111/reviewed-readme.patch),
with SHA-256 `34486dd531b383a0c004eefc84d5ceeb7d039c0d610aa87750aa5252a4a016b0`.
To recover and authenticate it from a full clone:

```sh
git show 3336e4290e56b7588f0b8abe1ae30366730f461b:evidence/readme-publication-fix-20261111/reviewed-readme.patch > /tmp/haetae-original-readme.patch
sha256sum /tmp/haetae-original-readme.patch
```
