#!/usr/bin/env python3
"""Exact-rational P8 checker for the zero-seed accepted mode-2 trace."""

from concurrent.futures import ProcessPoolExecutor
from decimal import Decimal, getcontext
from fractions import Fraction
from hashlib import sha256
import json
import os
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
POST_FREEZE = ROOT / "haetae-topdown-easycrypt/post-freeze"
ROOT_TABLE = (
    ROOT
    / "haetae-ref-easycrypt/easycrypt/spec/KeygenM23RootTableRounding.ec"
)
TRACE_ARTIFACT = POST_FREEZE / "mode2-zero-seed-accepted-class-trace.json"
P8_ARTIFACT = POST_FREEZE / "mode2-zero-seed-accepted-p8-certificate.json"
EASYCRYPT_CERTIFICATE = (
    POST_FREEZE
    / "Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze.ec"
)
EXPECTED_ROOT_TABLE_SHA256 = (
    "084c82a16ac59e957af0a43810a7bccca3731e426d4dad08a665f86bb961c38c"
)
EXPECTED_TRACE_SHA256 = (
    "f7f6836125cbc9eec3a1c165f4ff1523a533960677a0908c31278d581707e948"
)
SCALE = 10**18
ROOT_COUNT = 256

UNIFORM_ENVELOPE = Fraction(49301448283783168, 2187)
MIN_HEADROOM = Fraction(8057501, 196608)

MOMENTS = {
    2: [Fraction(2, 9), Fraction(2, 9), 0, Fraction(8, 9), Fraction(8, 3), Fraction(8, 9)],
    3: [Fraction(-2, 27), Fraction(2, 27), 0, Fraction(16, 27), 0, Fraction(-16, 27)],
    4: [Fraction(2, 27), Fraction(2, 27), 0, Fraction(32, 27), Fraction(32, 3), Fraction(32, 27)],
    5: [Fraction(-10, 243), Fraction(10, 243), 0, Fraction(320, 243), 0, Fraction(-320, 243)],
    6: [Fraction(22, 729), Fraction(22, 729), 0, Fraction(1408, 729), Fraction(128, 3), Fraction(1408, 729)],
    8: [Fraction(86, 6561), Fraction(86, 6561), 0, Fraction(22016, 6561), Fraction(512, 3), Fraction(22016, 6561)],
}


Interval = tuple[Fraction, Fraction]


def canonical_hash(value: object) -> str:
    encoded = json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode()
    return sha256(encoded).hexdigest()


def parse_inputs() -> tuple[list[tuple[int, int, int, int]], list[list[int]]]:
    text = ROOT_TABLE.read_text(encoding="utf-8")
    body = text.split("op root_certificates : icert list = [", 1)[1].split(
        "].", 1
    )[0]
    assert sha256(body.encode()).hexdigest() == EXPECTED_ROOT_TABLE_SHA256
    entries = [
        tuple(map(int, match))
        for match in re.findall(
            r"\(\((-?\d+),\s*(-?\d+)\),\s*\((-?\d+),\s*(-?\d+)\)\)",
            body,
        )
    ]
    assert len(entries) == ROOT_COUNT

    artifact = json.loads(TRACE_ARTIFACT.read_text(encoding="utf-8"))
    traces = artifact["class_trace"]
    assert artifact["class_trace_sha256"] == EXPECTED_TRACE_SHA256
    assert canonical_hash(traces) == EXPECTED_TRACE_SHA256
    assert len(traces) == 2 and all(len(row) == 256 for row in traces)
    return entries, traces


def point(value: Fraction | int) -> Interval:
    return (Fraction(value), Fraction(0))


def add(left: Interval, right: Interval) -> Interval:
    return (left[0] + right[0], left[1] + right[1])


def mul(left: Interval, right: Interval) -> Interval:
    lc, lr = left
    rc, rr = right
    return (lc * rc, abs(lc) * rr + abs(rc) * lr + lr * rr)


def power2(value: Interval) -> Interval:
    return mul(value, value)


def power3(value: Interval) -> Interval:
    return mul(power2(value), value)


def power4(value: Interval) -> Interval:
    square = power2(value)
    return mul(square, square)


def power5(value: Interval) -> Interval:
    return mul(power4(value), value)


def power6(value: Interval) -> Interval:
    cube = power3(value)
    return mul(cube, cube)


def power8(value: Interval) -> Interval:
    fourth = power4(value)
    return mul(fourth, fourth)


def scale_mul(scale: int, left: Interval, right: Interval) -> Interval:
    return mul(point(scale), mul(left, right))


def add3(a: Interval, b: Interval, c: Interval) -> Interval:
    return add(add(a, b), c)


def add4(a: Interval, b: Interval, c: Interval, d: Interval) -> Interval:
    return add(add3(a, b, c), d)


def add6(
    a: Interval,
    b: Interval,
    c: Interval,
    d: Interval,
    e: Interval,
    f: Interval,
) -> Interval:
    return add(add4(a, b, c, d), add(e, f))


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
) -> list[list[tuple[Interval, Interval, Interval, Interval, Interval, Interval]]]:
    output = []
    powers = (power2, power3, power4, power5, power6, power8)
    orders = (2, 3, 4, 5, 6, 8)
    for class_value in range(6):
        class_terms = []
        for residue in range(512):
            ball = root_ball(entries, residue, imag)
            class_terms.append(
                tuple(
                    mul(power(ball), point(MOMENTS[order][class_value]))
                    for order, power in zip(orders, powers)
                )
            )
        output.append(class_terms)
    return output


ENTRIES, TRACES = parse_inputs()
P8_CERTIFICATE = json.loads(P8_ARTIFACT.read_text(encoding="utf-8"))
assert P8_CERTIFICATE["schema"] == "haetae-mode2-accepted-p8-certificate-v1"
assert P8_CERTIFICATE["root_table_sha256"] == EXPECTED_ROOT_TABLE_SHA256
assert P8_CERTIFICATE["class_trace_sha256"] == EXPECTED_TRACE_SHA256
ROW_CERTIFICATES = P8_CERTIFICATE["rows"]
assert [row["row"] for row in ROW_CERTIFICATES] == [0, 1]
REAL_TERMS = build_terms(ENTRIES, imag=False)
IMAG_TERMS = build_terms(ENTRIES, imag=True)


def validate_easycrypt_constants() -> None:
    source = EASYCRYPT_CERTIFICATE.read_text(encoding="utf-8")
    ceiling_body = source.split(
        "op zero_seed_accepted_ceiling (row : int) : real =", 1
    )[1].split(".", 1)[0]
    improvement_body = source.split(
        "op zero_seed_accepted_uniform_improvement_floor (row : int) : real =",
        1,
    )[1].split(".", 1)[0]
    assert [int(value) for value in re.findall(r"\d+", ceiling_body)] == [
        0,
        ROW_CERTIFICATES[0]["ceiling"],
        1,
        ROW_CERTIFICATES[1]["ceiling"],
        0,
    ]
    assert [int(value) for value in re.findall(r"\d+", improvement_body)] == [
        0,
        ROW_CERTIFICATES[0]["uniform_improvement_integer_floor"],
        1,
        ROW_CERTIFICATES[1]["uniform_improvement_integer_floor"],
        0,
    ]
    assert "op zero_seed_accepted_numeric_certificate : bool" in source


def evaluate(task: tuple[int, int, bool]) -> tuple[Fraction, int, int, str]:
    row, k, imag = task
    terms = IMAG_TERMS if imag else REAL_TERMS
    p2 = p3 = p4 = p5 = p6 = p8 = point(0)
    multiplier = 2 * k + 1
    for j, class_value in enumerate(TRACES[row]):
        t2, t3, t4, t5, t6, t8 = terms[class_value][
            (multiplier * j) % 512
        ]
        next2 = add(p2, t2)
        next3 = add(p3, t3)
        next4 = add(p4, add(scale_mul(6, p2, t2), t4))
        next5 = add(
            p5, add3(scale_mul(10, p3, t2), scale_mul(10, p2, t3), t5)
        )
        next6 = add(
            p6,
            add4(
                scale_mul(15, p4, t2),
                scale_mul(20, p3, t3),
                scale_mul(15, p2, t4),
                t6,
            ),
        )
        next8 = add(
            p8,
            add6(
                scale_mul(28, p6, t2),
                scale_mul(56, p5, t3),
                scale_mul(70, p4, t4),
                scale_mul(56, p3, t5),
                scale_mul(28, p2, t6),
                t8,
            ),
        )
        p2, p3, p4, p5, p6, p8 = (
            next2,
            next3,
            next4,
            next5,
            next6,
            next8,
        )
    return (abs(p8[0]) + p8[1], row, k, "im" if imag else "re")


def decimal(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def main() -> None:
    validate_easycrypt_constants()
    tasks = [
        (row, k, imag)
        for row in range(2)
        for k in range(ROOT_COUNT)
        for imag in (False, True)
    ]
    requested = int(os.environ.get("HAETAE_P8_WORKERS", "8"))
    workers = max(1, min(requested, os.cpu_count() or 1))
    with ProcessPoolExecutor(max_workers=workers) as executor:
        results = list(executor.map(evaluate, tasks, chunksize=4))

    getcontext().prec = 24
    summaries = []
    for row in range(2):
        certificate = ROW_CERTIFICATES[row]
        expected_maximum = Fraction(
            certificate["max_numerator"], certificate["max_denominator"]
        )
        ceiling = Fraction(certificate["ceiling"])
        row_results = [result for result in results if result[1] == row]
        maximum = max(row_results)
        assert maximum[0] == expected_maximum
        assert (maximum[2], maximum[3]) == (
            certificate["max_root"],
            certificate["max_component"],
        )
        assert all(result[0] <= ceiling for result in row_results)
        assert certificate["uniform_improvement_integer_floor"] * ceiling < (
            UNIFORM_ENVELOPE
        )
        assert certificate["markov_denominator"] * ceiling < MIN_HEADROOM**8
        summaries.append(
            f"row{row}:k={maximum[2]}:{maximum[3]},"
            f"max={decimal(maximum[0])},ceiling={ceiling},"
            f"improvement>{decimal(UNIFORM_ENVELOPE / ceiling)},"
            f"Markov<{decimal(ceiling / MIN_HEADROOM**8)}"
        )

    print(
        "PASS zero-seed accepted P8 certificate: "
        + "; ".join(summaries)
        + f"; trace_sha256={EXPECTED_TRACE_SHA256}"
    )


if __name__ == "__main__":
    main()
