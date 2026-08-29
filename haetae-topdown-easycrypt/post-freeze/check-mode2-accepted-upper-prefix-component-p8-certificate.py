#!/usr/bin/env python3
"""Check the accepted-trace upper-prefix component-cap P8 certificate."""

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
ALL_SLOT_THEORY = (
    POST_FREEZE
    / "Mode2FaithfulSecurityIdealAccumulatorAllSlotCoordinateP8CertificatePostFreeze.ec"
)
ALL_SLOT_CHECKER = (
    POST_FREEZE / "check-mode2-accepted-all-slot-coordinate-p8-certificate.py"
)
ALL_SLOT_ARTIFACT = (
    POST_FREEZE / "mode2-zero-seed-accepted-all-slot-coordinate-p8-certificate.json"
)
UPPER_HEADROOM_THEORY = (
    POST_FREEZE / "Mode2FaithfulSecurityAccumulatorUpperHeadroomPostFreeze.ec"
)
ARTIFACT = (
    POST_FREEZE
    / "mode2-zero-seed-accepted-upper-prefix-component-p8-certificate.json"
)
EASYCRYPT_CERTIFICATE = (
    POST_FREEZE
    / "Mode2FaithfulSecurityIdealAccumulatorUpperPrefixComponentP8CertificatePostFreeze.ec"
)

EXPECTED_ALL_SLOT_THEORY_SHA256 = (
    "c9dd171a52e980a5c524c0c2150fb6d4bb5dc942fdaf5e14dc4e92ea6a7deab7"
)
EXPECTED_ALL_SLOT_CHECKER_SHA256 = (
    "ae1f2afa3d4e2c6c76d8b954f85863112859095fb965b3f20e3971073975b292"
)
EXPECTED_ALL_SLOT_ARTIFACT_SHA256 = (
    "86590eabc31c93f6f7fb42b63ac1f67c771d9d1c5e56ac78788d092323b0a8e0"
)
EXPECTED_UPPER_HEADROOM_THEORY_SHA256 = (
    "52e0d48dcf9db292a35d6cc5fcdcb1db5105ed330dbf218e0a28951abefe015c"
)

S1_SLOT_COUNT = 3
S2_SLOT_COUNT = 2
ROOT_COUNT = 256
S1_COMPONENT_CAP = Fraction(50)
S2_COMPONENT_CAP = Fraction(65)
FFT_ENDPOINT_EPSILON = Fraction(44833, 65536)
SQABS_ROUNDING_EPSILON = Fraction(1, 65536)
ACCUMULATOR_SIGNED_LIMIT = Fraction(2147483648, 65536)
FULL_TARGET = Fraction(1, 2)


def file_hash(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def exact_hash(value: Fraction) -> str:
    return sha256(f"{value.numerator}/{value.denominator}".encode()).hexdigest()


def decimal_text(value: Fraction) -> str:
    return str(Decimal(value.numerator) / Decimal(value.denominator))


def load_all_slot_checker():
    spec = importlib.util.spec_from_file_location(
        "mode2_upper_prefix_all_slot_base", ALL_SLOT_CHECKER
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


ALL_SLOT = load_all_slot_checker()
S2 = ALL_SLOT.S2
BASE = ALL_SLOT.BASE


def step_budget(cap: Fraction) -> Fraction:
    return (
        2 * cap**2
        + 4 * FFT_ENDPOINT_EPSILON * cap
        + SQABS_ROUNDING_EPSILON
        + 2 * FFT_ENDPOINT_EPSILON**2
    )


def fraction_record(value: Fraction) -> dict[str, object]:
    return {
        "exact_sum_sha256": exact_hash(value),
        "numerator_digits": len(str(value.numerator)),
        "denominator_digits": len(str(value.denominator)),
        "decimal": decimal_text(value),
    }


def validate_fraction_record(value: Fraction, record: dict[str, object]) -> None:
    assert record == fraction_record(value)


def parse_easycrypt_integer(source: str, name: str) -> int:
    match = re.search(rf"op {re.escape(name)} : real =\s*(\d+)%r\.", source)
    assert match is not None, f"missing EasyCrypt integer constant: {name}"
    return int(match.group(1))


def parse_easycrypt_fraction(source: str, name: str) -> Fraction:
    match = re.search(
        rf"op {re.escape(name)} : real =\s*(\d+)%r\s*/\s*(\d+)%r\.",
        source,
    )
    assert match is not None, f"missing EasyCrypt rational constant: {name}"
    return Fraction(int(match.group(1)), int(match.group(2)))


def compute() -> dict[str, Fraction]:
    requested = int(os.environ.get("HAETAE_UPPER_PREFIX_P8_WORKERS", "8"))
    workers = max(1, min(requested, os.cpu_count() or 1))
    s1_tasks = [(k, imag) for k in range(ROOT_COUNT) for imag in (False, True)]
    s2_tasks = [
        (row, k, imag)
        for row in range(S2_SLOT_COUNT)
        for k in range(ROOT_COUNT)
        for imag in (False, True)
    ]
    with ProcessPoolExecutor(max_workers=workers) as executor:
        s1_profiles = list(executor.map(ALL_SLOT.evaluate_s1, s1_tasks, chunksize=4))
        s2_profiles = list(executor.map(BASE.evaluate, s2_tasks, chunksize=4))

    s1_upper = S1_SLOT_COUNT * sum(
        (profile / S1_COMPONENT_CAP**8 for profile, _, _ in s1_profiles),
        Fraction(0),
    )
    s2_upper = Fraction(0)
    minimum_s2_headroom = None
    for profile, row, k, component in s2_profiles:
        center, radius = S2.bias_interval(row, k, component == "im")
        bias_upper = abs(center) + radius
        upper_headroom = S2_COMPONENT_CAP - bias_upper
        assert upper_headroom > 0
        if minimum_s2_headroom is None or upper_headroom < minimum_s2_headroom:
            minimum_s2_headroom = upper_headroom
        s2_upper += profile / upper_headroom**8

    assert minimum_s2_headroom is not None
    component_union = s1_upper + s2_upper
    full_union = component_union
    s1_budget = step_budget(S1_COMPONENT_CAP)
    s2_budget = step_budget(S2_COMPONENT_CAP)
    full_budget = S1_SLOT_COUNT * s1_budget + S2_SLOT_COUNT * s2_budget
    return {
        "s1_budget": s1_budget,
        "s2_budget": s2_budget,
        "full_budget": full_budget,
        "s1_upper": s1_upper,
        "s2_upper": s2_upper,
        "component_union": component_union,
        "full_union": full_union,
        "minimum_s2_headroom": minimum_s2_headroom,
    }


def emit_values(values: dict[str, Fraction]) -> None:
    output = {
        "s1_step_budget": {
            "numerator": values["s1_budget"].numerator,
            "denominator": values["s1_budget"].denominator,
            "decimal": decimal_text(values["s1_budget"]),
        },
        "s2_step_budget": {
            "numerator": values["s2_budget"].numerator,
            "denominator": values["s2_budget"].denominator,
            "decimal": decimal_text(values["s2_budget"]),
        },
        "full_budget": {
            "numerator": values["full_budget"].numerator,
            "denominator": values["full_budget"].denominator,
            "decimal": decimal_text(values["full_budget"]),
        },
        "minimum_s2_residual_headroom": {
            "numerator": values["minimum_s2_headroom"].numerator,
            "denominator": values["minimum_s2_headroom"].denominator,
            "decimal": decimal_text(values["minimum_s2_headroom"]),
        },
        "s1_component_union": fraction_record(values["s1_upper"]),
        "s2_component_union": fraction_record(values["s2_upper"]),
        "upper_prefix_component_union": fraction_record(values["component_union"]),
        "full_reduced_headroom_union": fraction_record(values["full_union"]),
    }
    print(json.dumps(output, indent=2))


def main() -> None:
    assert file_hash(ALL_SLOT_THEORY) == EXPECTED_ALL_SLOT_THEORY_SHA256
    assert file_hash(ALL_SLOT_CHECKER) == EXPECTED_ALL_SLOT_CHECKER_SHA256
    assert file_hash(ALL_SLOT_ARTIFACT) == EXPECTED_ALL_SLOT_ARTIFACT_SHA256
    assert file_hash(UPPER_HEADROOM_THEORY) == EXPECTED_UPPER_HEADROOM_THEORY_SHA256
    ALL_SLOT.S2.BASE.validate_easycrypt_constants()
    getcontext().prec = 50
    values = compute()

    assert values["full_budget"] < ACCUMULATOR_SIGNED_LIMIT
    assert values["component_union"] < FULL_TARGET
    assert values["full_union"] < FULL_TARGET

    if "--emit-values" in sys.argv:
        emit_values(values)
        return

    artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert artifact["schema"] == (
        "haetae-mode2-accepted-upper-prefix-component-p8-certificate-v1"
    )
    assert artifact["all_slot_theory_sha256"] == EXPECTED_ALL_SLOT_THEORY_SHA256
    assert artifact["all_slot_checker_sha256"] == EXPECTED_ALL_SLOT_CHECKER_SHA256
    assert artifact["all_slot_artifact_sha256"] == EXPECTED_ALL_SLOT_ARTIFACT_SHA256
    assert artifact["upper_headroom_theory_sha256"] == (
        EXPECTED_UPPER_HEADROOM_THEORY_SHA256
    )
    assert artifact["slot_count"] == S1_SLOT_COUNT + S2_SLOT_COUNT
    assert artifact["root_count"] == ROOT_COUNT
    assert artifact["component_count"] == 2
    assert artifact["s1_component_cap"] == S1_COMPONENT_CAP.numerator
    assert artifact["s2_component_cap"] == S2_COMPONENT_CAP.numerator
    assert artifact["full_target"] == {"numerator": 1, "denominator": 2}

    for key, value_key in (
        ("s1_component_union", "s1_upper"),
        ("s2_component_union", "s2_upper"),
        ("upper_prefix_component_union", "component_union"),
        ("full_reduced_headroom_union", "full_union"),
    ):
        validate_fraction_record(values[value_key], artifact[key])

    for key, value_key in (
        ("s1_step_budget", "s1_budget"),
        ("s2_step_budget", "s2_budget"),
        ("full_budget", "full_budget"),
        ("minimum_s2_residual_headroom", "minimum_s2_headroom"),
    ):
        value = values[value_key]
        assert artifact[key] == {
            "numerator": value.numerator,
            "denominator": value.denominator,
            "decimal": decimal_text(value),
        }

    source = EASYCRYPT_CERTIFICATE.read_text(encoding="utf-8")
    assert parse_easycrypt_integer(
        source, "ideal_mode2_upper_prefix_s1_component_cap"
    ) == S1_COMPONENT_CAP
    assert parse_easycrypt_integer(
        source, "ideal_mode2_upper_prefix_s2_component_cap"
    ) == S2_COMPONENT_CAP
    assert parse_easycrypt_fraction(
        source, "ideal_mode2_reduced_headroom_p8_target"
    ) == FULL_TARGET
    assert "ideal_mode2_upper_prefix_p8_numeric_certificate" in source
    assert "upper_prefix_bad_mu_le_component_cap_sum" in source
    assert "reduced_headroom_bad_mu_lt_one_half" in source
    assert "accumulator_unsafe_mu_lt_one_half" in source
    assert "accumulator_unsafe_mu_lt_one_half_closed" in source

    print(
        "PASS accepted upper-prefix component P8 certificate: "
        f"caps=({S1_COMPONENT_CAP},{S2_COMPONENT_CAP}), "
        f"budget={decimal_text(values['full_budget'])}<32768, "
        f"prefix={decimal_text(values['component_union'])}, "
        f"full={decimal_text(values['full_union'])}<1/2"
    )


if __name__ == "__main__":
    main()
