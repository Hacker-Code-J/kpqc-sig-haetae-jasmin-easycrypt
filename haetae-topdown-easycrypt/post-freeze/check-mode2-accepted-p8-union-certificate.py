#!/usr/bin/env python3
"""Check the exact 1024-term accepted-context P8 union limitation.

The summed terms are the certified interval upper bounds divided by the
uniform minimum headroom to the eighth power.  A total above one certifies a
limitation of this componentwise Markov/union analysis; it is not a lower
bound on the underlying bad-event probability.
"""

from concurrent.futures import ProcessPoolExecutor
from decimal import Decimal, getcontext
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import re
import sys


sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[2]
POST_FREEZE = ROOT / "haetae-topdown-easycrypt/post-freeze"
BASE_CHECKER = POST_FREEZE / "check-mode2-accepted-p8-certificate.py"
BASE_CERTIFICATE = POST_FREEZE / "mode2-zero-seed-accepted-p8-certificate.json"
UNION_CERTIFICATE = (
    POST_FREEZE / "mode2-zero-seed-accepted-p8-union-certificate.json"
)
EASYCRYPT_CERTIFICATE = (
    POST_FREEZE
    / "Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8UnionLimitationPostFreeze.ec"
)

EXPECTED_ROOT_TABLE_SHA256 = (
    "084c82a16ac59e957af0a43810a7bccca3731e426d4dad08a665f86bb961c38c"
)
EXPECTED_TRACE_SHA256 = (
    "f7f6836125cbc9eec3a1c165f4ff1523a533960677a0908c31278d581707e948"
)
EXPECTED_P8_CERTIFICATE_SHA256 = (
    "0dfb6999c8718b7bddaa0f4729686d55dd7de295e0788417124205a4a539f652"
)
EXPECTED_P8_CHECKER_SHA256 = (
    "44fb171142496480f018f81f11645b4704329638fedc85ffc32d339dcd1955cd"
)
ROW_COUNT = 2
ROOT_COUNT = 256
COMPONENT_COUNT = 2
SITE_COUNT = ROW_COUNT * ROOT_COUNT * COMPONENT_COUNT


def file_hash(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def load_base_checker():
    spec = importlib.util.spec_from_file_location(
        "mode2_accepted_p8_base", BASE_CHECKER
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


BASE = load_base_checker()


def artifact_fraction(record: dict[str, object]) -> Fraction:
    return Fraction(int(record["sum_numerator"]), int(record["sum_denominator"]))


def decimal_text(value: Fraction) -> str:
    return str(Decimal(value.numerator) / Decimal(value.denominator))


def parse_easycrypt_fraction(source: str, name: str) -> Fraction:
    match = re.search(
        rf"op {re.escape(name)} : real =\s*(\d+)%r\s*/\s*(\d+)%r\.",
        source,
    )
    assert match is not None, f"missing EasyCrypt rational constant: {name}"
    return Fraction(int(match.group(1)), int(match.group(2)))


def main() -> None:
    assert file_hash(BASE_CERTIFICATE) == EXPECTED_P8_CERTIFICATE_SHA256
    assert file_hash(BASE_CHECKER) == EXPECTED_P8_CHECKER_SHA256
    BASE.validate_easycrypt_constants()

    artifact = json.loads(UNION_CERTIFICATE.read_text(encoding="utf-8"))
    assert artifact["schema"] == "haetae-mode2-accepted-p8-union-certificate-v1"
    assert artifact["root_table_sha256"] == EXPECTED_ROOT_TABLE_SHA256
    assert artifact["class_trace_sha256"] == EXPECTED_TRACE_SHA256
    assert artifact["p8_certificate_sha256"] == EXPECTED_P8_CERTIFICATE_SHA256
    assert artifact["p8_checker_sha256"] == EXPECTED_P8_CHECKER_SHA256
    assert artifact["site_count"] == SITE_COUNT
    assert artifact["min_headroom"] == {
        "numerator": BASE.MIN_HEADROOM.numerator,
        "denominator": BASE.MIN_HEADROOM.denominator,
    }

    tasks = [
        (row, k, imag)
        for row in range(ROW_COUNT)
        for k in range(ROOT_COUNT)
        for imag in (False, True)
    ]
    requested = int(os.environ.get("HAETAE_P8_UNION_WORKERS", "8"))
    workers = max(1, min(requested, os.cpu_count() or 1))
    with ProcessPoolExecutor(max_workers=workers) as executor:
        results = list(executor.map(BASE.evaluate, tasks, chunksize=4))

    assert len(results) == SITE_COUNT
    assert len({(row, k, component) for _, row, k, component in results}) == SITE_COUNT

    headroom8 = BASE.MIN_HEADROOM**8
    getcontext().prec = 30
    row_sums: list[Fraction] = []
    rows = artifact["rows"]
    assert [row["row"] for row in rows] == [0, 1]

    for row in range(ROW_COUNT):
        row_results = [result for result in results if result[1] == row]
        assert len(row_results) == ROOT_COUNT * COMPONENT_COUNT

        base_row = BASE.ROW_CERTIFICATES[row]
        maximum = max(row_results)
        assert maximum[0] == Fraction(
            base_row["max_numerator"], base_row["max_denominator"]
        )
        assert (maximum[2], maximum[3]) == (
            base_row["max_root"],
            base_row["max_component"],
        )
        assert all(result[0] <= base_row["ceiling"] for result in row_results)

        row_sum = sum((result[0] / headroom8 for result in row_results), Fraction(0))
        row_sums.append(row_sum)
        row_artifact = rows[row]
        assert row_artifact["component_count"] == len(row_results)
        assert row_sum == artifact_fraction(row_artifact)
        assert row_artifact["decimal"] == decimal_text(row_sum)

    total = sum(row_sums, Fraction(0))
    total_artifact = artifact["total"]
    assert total == artifact_fraction(total_artifact)
    assert total_artifact["decimal"] == decimal_text(total)
    assert total > 1
    assert total_artifact["greater_than_one"] is True
    assert total_artifact["subunit_probability_bound"] is False

    easycrypt_source = EASYCRYPT_CERTIFICATE.read_text(encoding="utf-8")
    easycrypt_values = [
        parse_easycrypt_fraction(
            easycrypt_source,
            "zero_seed_accepted_s2_slot_headroom_markov8_row0_exact",
        ),
        parse_easycrypt_fraction(
            easycrypt_source,
            "zero_seed_accepted_s2_slot_headroom_markov8_row1_exact",
        ),
        parse_easycrypt_fraction(
            easycrypt_source,
            "zero_seed_accepted_s2_slot_headroom_markov8_exact",
        ),
    ]
    assert easycrypt_values == [row_sums[0], row_sums[1], total]
    assert (
        "op zero_seed_accepted_s2_slot_headroom_markov8_union_numeric_certificate"
        in easycrypt_source
    )
    assert "markov8_exact_gt_one" in easycrypt_source
    assert "markov8_bound_not_subunit" in easycrypt_source

    print(
        "PASS zero-seed accepted P8 componentwise-union limitation: "
        f"sites={SITE_COUNT}, row0={decimal_text(row_sums[0])}, "
        f"row1={decimal_text(row_sums[1])}, total={decimal_text(total)} > 1; "
        f"trace_sha256={EXPECTED_TRACE_SHA256}"
    )


if __name__ == "__main__":
    main()
