#!/usr/bin/env python3
"""Check the accepted-context P8 union with certified local headrooms.

The checker mirrors the EasyCrypt center-radius bias evaluator with exact
Fractions, recomputes all 1024 P8 terms, and checks the resulting sum against
1/1024.  The enormous exact sums are pinned by canonical numerator/denominator
hashes instead of being copied into the proof source.
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
sys.set_int_max_str_digits(1_000_000)
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

ROOT = Path(__file__).resolve().parents[2]
POST_FREEZE = ROOT / "haetae-topdown-easycrypt/post-freeze"
BASE_CHECKER = POST_FREEZE / "check-mode2-accepted-p8-certificate.py"
BASE_CERTIFICATE = POST_FREEZE / "mode2-zero-seed-accepted-p8-certificate.json"
P8_UNION_THEORY = (
    POST_FREEZE
    / "Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8UnionLimitationPostFreeze.ec"
)
TRACE_HEADROOM_CERTIFICATE = (
    POST_FREEZE / "mode2-zero-seed-accepted-p8-trace-headroom-certificate.json"
)
EASYCRYPT_CERTIFICATE = (
    POST_FREEZE
    / "Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8TraceHeadroomCertificatePostFreeze.ec"
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
EXPECTED_P8_UNION_THEORY_SHA256 = (
    "a158677d50592fef869e59f319e5bfab5f4a81e25b14d4abce43564d6bc9b38a"
)

ROW_COUNT = 2
ROOT_COUNT = 256
COMPONENT_COUNT = 2
SITE_COUNT = ROW_COUNT * ROOT_COUNT * COMPONENT_COUNT
ACCUMULATOR_COORDINATE_CAP = Fraction(127)
FFT_ENDPOINT_EPSILON = Fraction(44833, 65536)
CLASS_BIAS = (
    Fraction(-1, 3),
    Fraction(1, 3),
    Fraction(0),
    Fraction(-1, 3),
    Fraction(0),
    Fraction(1, 3),
)
TARGET = Fraction(1, 1024)


def file_hash(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def exact_hash(value: Fraction) -> str:
    return sha256(f"{value.numerator}/{value.denominator}".encode()).hexdigest()


def decimal_text(value: Fraction) -> str:
    return str(Decimal(value.numerator) / Decimal(value.denominator))


def load_base_checker():
    spec = importlib.util.spec_from_file_location(
        "mode2_accepted_p8_trace_headroom_base", BASE_CHECKER
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


BASE = load_base_checker()


def bias_interval(row: int, k: int, imag: bool):
    value = BASE.point(0)
    multiplier = 2 * k + 1
    for j, class_value in enumerate(BASE.TRACES[row]):
        root = BASE.root_ball(
            BASE.ENTRIES, (multiplier * j) % 512, imag
        )
        value = BASE.add(
            value, BASE.mul(root, BASE.point(CLASS_BIAS[class_value]))
        )
    return value


def validate_fraction_record(value: Fraction, record: dict[str, object]) -> None:
    assert record["exact_sum_sha256"] == exact_hash(value)
    assert record["numerator_digits"] == len(str(value.numerator))
    assert record["denominator_digits"] == len(str(value.denominator))
    assert record["decimal"] == decimal_text(value)


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
    assert file_hash(P8_UNION_THEORY) == EXPECTED_P8_UNION_THEORY_SHA256
    BASE.validate_easycrypt_constants()

    artifact = json.loads(
        TRACE_HEADROOM_CERTIFICATE.read_text(encoding="utf-8")
    )
    assert artifact["schema"] == (
        "haetae-mode2-accepted-p8-trace-headroom-certificate-v1"
    )
    assert artifact["root_table_sha256"] == EXPECTED_ROOT_TABLE_SHA256
    assert artifact["class_trace_sha256"] == EXPECTED_TRACE_SHA256
    assert artifact["p8_certificate_sha256"] == EXPECTED_P8_CERTIFICATE_SHA256
    assert artifact["p8_checker_sha256"] == EXPECTED_P8_CHECKER_SHA256
    assert artifact["p8_union_theory_sha256"] == EXPECTED_P8_UNION_THEORY_SHA256
    assert artifact["site_count"] == SITE_COUNT
    assert artifact["accumulator_coordinate_cap"] == int(
        ACCUMULATOR_COORDINATE_CAP
    )
    assert artifact["fft_endpoint_epsilon"] == {
        "numerator": FFT_ENDPOINT_EPSILON.numerator,
        "denominator": FFT_ENDPOINT_EPSILON.denominator,
    }
    assert artifact["class_bias_oracle"] == [
        "-1/3", "1/3", "0", "-1/3", "0", "1/3"
    ]

    tasks = [
        (row, k, imag)
        for row in range(ROW_COUNT)
        for k in range(ROOT_COUNT)
        for imag in (False, True)
    ]
    requested = int(os.environ.get("HAETAE_P8_HEADROOM_WORKERS", "8"))
    workers = max(1, min(requested, os.cpu_count() or 1))
    with ProcessPoolExecutor(max_workers=workers) as executor:
        p8_results = list(executor.map(BASE.evaluate, tasks, chunksize=4))

    records = []
    for p8_upper, row, k, component in p8_results:
        imag = component == "im"
        center, radius = bias_interval(row, k, imag)
        assert radius >= 0
        bias_upper = abs(center) + radius
        headroom = (
            ACCUMULATOR_COORDINATE_CAP
            - FFT_ENDPOINT_EPSILON
            - bias_upper
        )
        assert headroom > 0
        bound = p8_upper / headroom**8
        records.append(
            {
                "row": row,
                "k": k,
                "component": component,
                "bias_upper": bias_upper,
                "headroom": headroom,
                "p8_upper": p8_upper,
                "bound": bound,
            }
        )

    assert len(records) == SITE_COUNT
    assert len({(r["row"], r["k"], r["component"]) for r in records}) == SITE_COUNT
    getcontext().prec = 50

    minimum = min(records, key=lambda record: record["headroom"])
    minimum_artifact = artifact["minimum_headroom"]
    minimum_value = Fraction(
        int(minimum_artifact["numerator"]),
        int(minimum_artifact["denominator"]),
    )
    assert minimum["headroom"] == minimum_value
    assert minimum_artifact["decimal"] == decimal_text(minimum_value)
    assert (minimum["row"], minimum["k"], minimum["component"]) == (
        minimum_artifact["row"],
        minimum_artifact["root"],
        minimum_artifact["component"],
    )

    maximum_bias = max(records, key=lambda record: record["bias_upper"])
    maximum_bias_artifact = artifact["maximum_bias_upper"]
    maximum_bias_value = Fraction(
        int(maximum_bias_artifact["numerator"]),
        int(maximum_bias_artifact["denominator"]),
    )
    assert maximum_bias["bias_upper"] == maximum_bias_value
    assert maximum_bias_artifact["decimal"] == decimal_text(maximum_bias_value)
    assert (
        maximum_bias["row"], maximum_bias["k"], maximum_bias["component"]
    ) == (
        maximum_bias_artifact["row"],
        maximum_bias_artifact["root"],
        maximum_bias_artifact["component"],
    )

    rows = artifact["rows"]
    assert [row["row"] for row in rows] == [0, 1]
    row_sums: list[Fraction] = []
    for row in range(ROW_COUNT):
        row_records = [record for record in records if record["row"] == row]
        assert len(row_records) == ROOT_COUNT * COMPONENT_COUNT
        row_sum = sum((record["bound"] for record in row_records), Fraction(0))
        row_sums.append(row_sum)
        assert rows[row]["component_count"] == len(row_records)
        validate_fraction_record(row_sum, rows[row])

    maximum_bound = max(records, key=lambda record: record["bound"])
    maximum_bound_artifact = artifact["maximum_component_bound"]
    assert maximum_bound_artifact["exact_sha256"] == exact_hash(
        maximum_bound["bound"]
    )
    assert maximum_bound_artifact["numerator_digits"] == len(
        str(maximum_bound["bound"].numerator)
    )
    assert maximum_bound_artifact["denominator_digits"] == len(
        str(maximum_bound["bound"].denominator)
    )
    assert maximum_bound_artifact["decimal"] == decimal_text(
        maximum_bound["bound"]
    )
    assert (
        maximum_bound["row"], maximum_bound["k"], maximum_bound["component"]
    ) == (
        maximum_bound_artifact["row"],
        maximum_bound_artifact["root"],
        maximum_bound_artifact["component"],
    )

    total = sum(row_sums, Fraction(0))
    total_artifact = artifact["total"]
    validate_fraction_record(total, total_artifact)
    assert TARGET == Fraction(
        total_artifact["target_numerator"],
        total_artifact["target_denominator"],
    )
    assert total < TARGET
    assert total_artifact["strictly_below_target"] is True
    scaled_margin = Fraction(1) - 1024 * total
    assert total_artifact["scaled_margin_decimal"] == decimal_text(scaled_margin)

    easycrypt_source = EASYCRYPT_CERTIFICATE.read_text(encoding="utf-8")
    assert parse_easycrypt_fraction(
        easycrypt_source,
        "zero_seed_accepted_trace_min_headroom",
    ) == minimum_value
    assert parse_easycrypt_fraction(
        easycrypt_source,
        "zero_seed_accepted_trace_headroom_p8_target",
    ) == TARGET
    assert "op zero_seed_accepted_trace_headroom_p8_numeric_certificate" in easycrypt_source
    assert "headroom_markov8_sum_lt_target" in easycrypt_source
    assert "headroom_bad_mu_lt_one_over_1024" in easycrypt_source

    print(
        "PASS zero-seed accepted trace-headroom P8 union: "
        f"sites={SITE_COUNT}, min_headroom={decimal_text(minimum_value)}, "
        f"row0={decimal_text(row_sums[0])}, row1={decimal_text(row_sums[1])}, "
        f"total={decimal_text(total)} < 1/1024; "
        f"trace_sha256={EXPECTED_TRACE_SHA256}"
    )


if __name__ == "__main__":
    main()
