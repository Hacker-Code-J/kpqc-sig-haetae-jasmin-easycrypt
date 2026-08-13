#!/usr/bin/env python3
"""Deterministic cross-check for the minimum avec/security-model mismatch.

This is not a probabilistic sampler test and is not used as an EasyCrypt
axiom.  It reproduces one terminating execution with Python's FIPS-202 SHAKE
implementation so the false synthetic-coefficient identification has an
independent concrete witness.
"""

import hashlib


Q = 64513
RAW_SEED = bytes(32)
EXPECTED_RHO = bytes.fromhex(
    "f5977c8283546a63723bc31d2619124f"
    "11db4658643336741df81757d5ad3062"
)
EXPECTED_FIRST = {515: 44985, 516: 20488}


def accepted_prefix(rho: bytes, nonce: int, count: int) -> list[int]:
    blocks = 4
    accepted: list[int] = []
    while len(accepted) < count:
        stream = hashlib.shake_128(
            rho + nonce.to_bytes(2, "little")
        ).digest(blocks * 168)
        accepted = [
            stream[i] + 256 * stream[i + 1]
            for i in range(0, len(stream), 2)
            if stream[i] + 256 * stream[i + 1] < Q
        ]
        blocks += 1
    return accepted[:count]


def main() -> None:
    seedbuf = hashlib.shake_256(RAW_SEED).digest(128)
    rho = seedbuf[:32]
    assert rho == EXPECTED_RHO

    for nonce, expected in EXPECTED_FIRST.items():
        values = accepted_prefix(rho, nonce, 256)
        assert len(values) == 256
        assert all(0 <= value < Q for value in values)
        assert values[0] == expected

    assert EXPECTED_FIRST[515] != 401
    print("PASS deterministic actual avec trace: row0[0]=44985, row1[0]=20488")


if __name__ == "__main__":
    main()
