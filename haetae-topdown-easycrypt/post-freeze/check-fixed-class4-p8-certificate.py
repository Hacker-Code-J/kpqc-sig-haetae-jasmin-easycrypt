#!/usr/bin/env python3
"""Exact-rational checker for the homogeneous class-4 P8 stress profile.

This checker is a reproducible computational artifact, not an EasyCrypt
assumption.  It parses the already-proved integer root certificate table,
mirrors the center-radius operations used by the post-freeze EasyCrypt
evaluator, and checks all 256 odd roots and both real/imaginary components.
"""

from decimal import Decimal, getcontext
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
ROOT_TABLE = (
    ROOT
    / "haetae-ref-easycrypt/easycrypt/spec/KeygenM23RootTableRounding.ec"
)
EXPECTED_TABLE_SHA256 = (
    "084c82a16ac59e957af0a43810a7bccca3731e426d4dad08a665f86bb961c38c"
)
SCALE = 10**18
ROOT_COUNT = 256

EXPECTED_MAX = Fraction(
    12308347695001004974787451393165056107966550137033046255135982299515776667076115687052376917085741289907479067367466010672899342400767489358108900612552819,
    8789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
)
CERTIFIED_CEILING = Fraction(1400416448854)
UNIFORM_ENVELOPE = Fraction(49301448283783168, 2187)
MIN_HEADROOM = Fraction(8057501, 196608)


def parse_root_certificates() -> list[tuple[int, int, int, int]]:
    text = ROOT_TABLE.read_text(encoding="utf-8")
    body = text.split("op root_certificates : icert list = [", 1)[1].split(
        "].", 1
    )[0]
    assert sha256(body.encode()).hexdigest() == EXPECTED_TABLE_SHA256
    entries = [
        tuple(map(int, match))
        for match in re.findall(
            r"\(\((-?\d+),\s*(-?\d+)\),\s*\((-?\d+),\s*(-?\d+)\)\)",
            body,
        )
    ]
    assert len(entries) == ROOT_COUNT
    return entries


Interval = tuple[Fraction, Fraction]


def point(x: Fraction | int) -> Interval:
    return (Fraction(x), Fraction(0))


def add(left: Interval, right: Interval) -> Interval:
    return (left[0] + right[0], left[1] + right[1])


def mul(left: Interval, right: Interval) -> Interval:
    lc, lr = left
    rc, rr = right
    return (lc * rc, abs(lc) * rr + abs(rc) * lr + lr * rr)


def power2(value: Interval) -> Interval:
    return mul(value, value)


def power4(value: Interval) -> Interval:
    square = power2(value)
    return mul(square, square)


def power6(value: Interval) -> Interval:
    cube = mul(power2(value), value)
    return mul(cube, cube)


def power8(value: Interval) -> Interval:
    fourth = power4(value)
    return mul(fourth, fourth)


def scale_mul(scale: int, left: Interval, right: Interval) -> Interval:
    return mul(point(scale), mul(left, right))


def root_ball(
    entries: list[tuple[int, int, int, int]], residue: int, imag: bool
) -> Interval:
    residue %= 512
    sign = 1
    if residue >= 256:
        residue -= 256
        sign = -1
    re_center, re_radius, im_center, im_radius = entries[residue]
    center, radius = (
        (im_center, im_radius) if imag else (re_center, re_radius)
    )
    return (Fraction(sign * center, SCALE), Fraction(radius, SCALE))


def build_terms(
    entries: list[tuple[int, int, int, int]], imag: bool
) -> list[tuple[Interval, Interval, Interval, Interval]]:
    moments = {
        2: Fraction(8, 3),
        4: Fraction(32, 3),
        6: Fraction(128, 3),
        8: Fraction(512, 3),
    }
    terms = []
    for residue in range(512):
        ball = root_ball(entries, residue, imag)
        terms.append(
            (
                mul(power2(ball), point(moments[2])),
                mul(power4(ball), point(moments[4])),
                mul(power6(ball), point(moments[6])),
                mul(power8(ball), point(moments[8])),
            )
        )
    return terms


def evaluate_root(
    k: int, terms: list[tuple[Interval, Interval, Interval, Interval]]
) -> Interval:
    p2 = p4 = p6 = p8 = point(0)
    multiplier = 2 * k + 1
    for j in range(256):
        t2, t4, t6, t8 = terms[(multiplier * j) % 512]
        next2 = add(p2, t2)
        next4 = add(p4, add(scale_mul(6, p2, t2), t4))
        next6 = add(
            p6,
            add(
                add(scale_mul(15, p4, t2), scale_mul(15, p2, t4)),
                t6,
            ),
        )
        next8 = add(
            p8,
            add(
                add(
                    add(
                        scale_mul(28, p6, t2),
                        scale_mul(70, p4, t4),
                    ),
                    scale_mul(28, p2, t6),
                ),
                t8,
            ),
        )
        p2, p4, p6, p8 = next2, next4, next6, next8
    return p8


def upper(interval: Interval) -> Fraction:
    return abs(interval[0]) + interval[1]


def decimal(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def main() -> None:
    entries = parse_root_certificates()
    real_terms = build_terms(entries, imag=False)
    imag_terms = build_terms(entries, imag=True)
    uppers = [
        upper(evaluate_root(k, terms))
        for k in range(ROOT_COUNT)
        for terms in (real_terms, imag_terms)
    ]

    maximum = max(uppers)
    assert maximum == EXPECTED_MAX
    assert all(value <= CERTIFIED_CEILING for value in uppers)
    assert 16 * CERTIFIED_CEILING < UNIFORM_ENVELOPE
    assert 5 * CERTIFIED_CEILING < MIN_HEADROOM**8

    getcontext().prec = 24
    print(
        "PASS homogeneous class-4 P8 certificate: "
        f"roots={ROOT_COUNT}, components=2, "
        f"max={decimal(maximum)}, ceiling={CERTIFIED_CEILING}, "
        f"uniform-improvement>{decimal(UNIFORM_ENVELOPE / CERTIFIED_CEILING)}, "
        f"Markov-at-min-headroom<{decimal(CERTIFIED_CEILING / MIN_HEADROOM**8)}, "
        f"root-table-sha256={EXPECTED_TABLE_SHA256}"
    )


if __name__ == "__main__":
    main()
