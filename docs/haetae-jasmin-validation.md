# HAETAE Jasmin validation record

Validation date: 2026-09-17. The target is
[haetae-jasmin](../haetae-jasmin/README.md). Starting from the preserved earlier
implementation at commit `6177f8db0a2887314dbff213e5ca04234eece58e`, it was
updated to match the pinned [HAETAE reference sources](HAETAE.md).

## Reproduction commands and results

```sh
make -C haetae-jasmin -j2 all
make -C haetae-jasmin -j2 test
make -C haetae-jasmin sampler-ct
```

All passed with Jasmin Compiler 2026.03.0 on Linux x86-64. Assembly was compiled
from the sources in the new directory rather than copied from an earlier build.

| Check | Result |
| --- | --- |
| Basic signing and verification | 100 executions passed for each of modes 2·3·5 |
| Official KAT | 100 responses for each of modes 2·3·5; all 6 `.req`·`.rsp` files matched |
| API | Passed 8 APIs, deterministic inputs, context lengths 255/256, raw prefix 301, empty input, tampering and length errors, same-buffer signing/recovery, and failure outputs |
| C/Jasmin interoperability | Passed deterministic key/signature byte equality, bidirectional verification of randomized signatures, combined signing/open, and messages at SHAKE block boundaries |
| Sampler differential checks | Passed values below/at/above all 166 CDT thresholds and borrow cases, signed ceiling, exponential approximation, 26-byte inputs, maximum sample 166, dummy output and buffer boundaries |
| SHAKE stream | Matched C in 60 deterministic cases, with 4,355 refills and 31 cases involving repeated refills |
| Regression detection | Detected all 3 mutations introduced into temporary copies: the old 17-byte stride, old tail rounding, and a missing polynomial correction term |
| C diagnostics | API and interoperability tests passed `-Wall -Wextra -Werror` in all three modes; sampler tests also passed strict diagnostics |
| Link checks | The only required external symbol of the three production libraries was `__jasmin_syscall_randombytes__`; they were not linked to the reference C algorithm |

Sampler tests use the distribution's actual `src/sampler.c` as the oracle.
They do not use upstream `test/test_sampler.c`, which replicates a different
polynomial. Interoperability tests isolate reference C symbols with the
`reference_haetae_` prefix and call both implementations. Reference C code is
linked only into test executables.

## Memory and compiler checks

The following API boundary check for the largest parameter set reported 0
Valgrind errors and 0 bytes of unreleased heap at exit.

```sh
cd haetae-jasmin
valgrind --error-exitcode=99 --leak-check=full --track-origins=yes \
  build/bin/haetae-mode5-api-test
```

`sampler-ct` performed CT/SCT checks for CDT, ceiling multiplication,
exponential approximation, a single Gaussian attempt, the fixed-buffer
consumer, and the Gaussian stream module. Separate `jasminc -checksafety`
checks reported `No Safety Violation` for the following three slices:

- `sample_gauss83_jazz`
- `smulh48_jazz`
- `sample_gauss_sigma76_jazz`

Compiler checks are relative to the source's explicit declassification and
the checker configuration. They do not certify side-channel safety of the
complete KeyGen/Sign/Verify API or constitute new EasyCrypt proofs. This record
covers functional agreement, specific memory boundaries, and limited compiler checks.
