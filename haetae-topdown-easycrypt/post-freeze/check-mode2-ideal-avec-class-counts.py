#!/usr/bin/env python3
"""Certify the exact ideal mode-2 avec class carrier."""

from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[2]
POST_FREEZE = ROOT / "haetae-topdown-easycrypt" / "post-freeze"
THEORY = POST_FREEZE / "Mode2FaithfulSecurityIdealAvecClassTraceLawPostFreeze.ec"
ARTIFACT = POST_FREEZE / "mode2-ideal-avec-class-counts.json"

Q = 64513
TRACE_ROWS = 2
TRACE_WORDS = 256
TRACE_SIZE = TRACE_ROWS * TRACE_WORDS
OFFSETS = [
    -2 * Q - 1,
    -Q,
    -(Q - 1),
    -1,
    0,
    1,
    Q - 1,
    Q,
    2 * Q + 7,
]

EXPECTED_COUNTS = [1, 1, 16127, 16128, 16128, 16128]
EXPECTED_MASSES = [Fraction(count, Q) for count in EXPECTED_COUNTS]
REQUIRED_THEORY_SYMBOLS = {
    "parameter_certificate": "ideal_avec_parameter_certificate",
    "coefficient_distribution": "ideal_avec_coefficient_distribution",
    "shift_uniform": "ideal_avec_shift_uniform",
    "shifted_point_mass": "ideal_avec_shifted_class_distribution_point",
    "class_count_certificate": "ideal_avec_class_count_certificate",
    "point_mass_theorem": "ideal_avec_class_distribution_point",
    "point_mass_outside": "ideal_avec_class_distribution_point_outside",
    "ordered_product_distribution": "ideal_avec_ordered_class_trace_distribution",
    "coordinate_marginal": "ideal_avec_ordered_class_trace_coordinate_marginal",
    "coordinate_point_mass": (
        "ideal_avec_ordered_class_trace_coordinate_point_mass"
    ),
    "independent_carrier_distribution": (
        "ideal_mode2_independent_avec_carrier_distribution"
    ),
    "independent_carrier_boundary": "ideal_mode2_independent_avec_carrier_boundary",
    "independent_carrier_prebp_secret_marginal": (
        "ideal_mode2_independent_avec_carrier_prebp_secret_marginal"
    ),
    "independent_carrier_trace_marginal": (
        "ideal_mode2_independent_avec_carrier_trace_marginal"
    ),
}


def canonical_hash(value: object) -> str:
    encoded = json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode()
    return sha256(encoded).hexdigest()


def file_sha256(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def class_index(rho: int) -> int:
    if rho == 0:
        return 0
    if rho == Q - 1:
        return 1
    return 2 + rho % 4


def build_counts() -> list[int]:
    counts = [0] * 6
    for rho in range(Q):
        counts[class_index(rho)] += 1
    return counts


def shift(pre_bp: int, avec: int) -> int:
    return (pre_bp + avec) % Q


def check_shift_permutations() -> dict[str, object]:
    records: list[dict[str, object]] = []
    base = list(range(Q))
    for pre_bp in OFFSETS:
        shifted = [shift(pre_bp, avec) for avec in base]
        assert min(shifted) == 0
        assert max(shifted) == Q - 1
        assert len(set(shifted)) == Q
        records.append(
            {
                "offset": pre_bp,
                "image_sha256": canonical_hash(shifted),
                "first_values": shifted[:8],
                "last_values": shifted[-8:],
            }
        )
    return {"offsets": OFFSETS, "records": records}


def inspect_theory() -> dict[str, object]:
    if not THEORY.exists():
        return {
            "path": str(THEORY.relative_to(ROOT)),
            "status": "missing",
            "symbols": {},
        }

    source = THEORY.read_text(encoding="utf-8")
    symbols = {
        label: bool(
            re.search(
                rf"\b(?:op|type|lemma)\s+{re.escape(name)}\b",
                source,
            )
        )
        for label, name in REQUIRED_THEORY_SYMBOLS.items()
    }
    assert all(symbols.values()), symbols
    return {
        "path": str(THEORY.relative_to(ROOT)),
        "status": "present",
        "sha256": file_sha256(THEORY),
        "symbols": symbols,
    }


def build_artifact() -> dict[str, object]:
    counts = build_counts()
    assert counts == EXPECTED_COUNTS
    masses = [Fraction(count, Q) for count in counts]
    assert masses == EXPECTED_MASSES
    assert sum(masses, Fraction(0, 1)) == Fraction(1, 1)

    shift_report = check_shift_permutations()
    theory = inspect_theory()
    probabilities = [
        {
            "class": cls,
            "count": count,
            "numerator": mass.numerator,
            "denominator": mass.denominator,
            "fraction": f"{mass.numerator}/{mass.denominator}",
        }
        for cls, (count, mass) in enumerate(zip(counts, masses))
    ]

    return {
        "schema": "haetae-mode2-ideal-avec-class-counts-v1",
        "q": Q,
        "trace_shape": {
            "rows": TRACE_ROWS,
            "words_per_row": TRACE_WORDS,
            "total_coefficients": TRACE_SIZE,
        },
        "class_definition": {
            "description": (
                "0 if rho=0; 1 if rho=q-1; else 2+rho%4"
            ),
            "counts": counts,
            "total": sum(counts),
            "counts_sha256": canonical_hash(counts),
            "probabilities": probabilities,
            "probabilities_sha256": canonical_hash(probabilities),
            "sum_fraction": "1/1",
        },
        "shift_permutation_certificate": shift_report,
        "source_hashes": {
            "checker_script": {
                "path": str(Path(__file__).relative_to(ROOT)),
                "sha256": file_sha256(Path(__file__)),
            },
            "theory": theory,
        },
    }


def emit_artifact(path: Path) -> None:
    path.write_text(
        json.dumps(build_artifact(), indent=2, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )


def verify_committed_artifact() -> None:
    expected = build_artifact()
    observed = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert observed == expected
    print(
        "PASS ideal mode2 avec class counts: "
        f"counts={expected['class_definition']['counts']}, "
        f"sum={expected['class_definition']['sum_fraction']}, "
        f"theory={expected['source_hashes']['theory']['status']}"
    )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit-artifact", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    if args.emit_artifact:
        emit_artifact(ARTIFACT)
        return 0

    verify_committed_artifact()
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
