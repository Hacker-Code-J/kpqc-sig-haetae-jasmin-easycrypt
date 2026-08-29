#!/usr/bin/env python3
"""Check the accepted-context all-five-slot coordinate P8 certificate."""

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
S2_THEORY = (
    POST_FREEZE
    / "Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotP8TraceHeadroomCertificatePostFreeze.ec"
)
S2_CHECKER = POST_FREEZE / "check-mode2-accepted-p8-trace-headroom-certificate.py"
S2_ARTIFACT = POST_FREEZE / "mode2-zero-seed-accepted-p8-trace-headroom-certificate.json"
CLASS4_THEORY = (
    POST_FREEZE
    / "Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentFixedClassTraceP8CertificateCheckerPostFreeze.ec"
)
CLASS4_CHECKER = POST_FREEZE / "check-fixed-class4-p8-certificate.py"
ARTIFACT = POST_FREEZE / "mode2-zero-seed-accepted-all-slot-coordinate-p8-certificate.json"
EASYCRYPT_CERTIFICATE = (
    POST_FREEZE
    / "Mode2FaithfulSecurityIdealAccumulatorAllSlotCoordinateP8CertificatePostFreeze.ec"
)

EXPECTED_ROOT_TABLE_SHA256 = (
    "084c82a16ac59e957af0a43810a7bccca3731e426d4dad08a665f86bb961c38c"
)
EXPECTED_TRACE_SHA256 = (
    "f7f6836125cbc9eec3a1c165f4ff1523a533960677a0908c31278d581707e948"
)
EXPECTED_S2_THEORY_SHA256 = (
    "7221718b41442d1df1030dc739d0b89cb4ee96a10752b44997291ddd88b86129"
)
EXPECTED_S2_CHECKER_SHA256 = (
    "6084cf87084602f65d876ccd88e6c9e5197f35d196bc2c006d2ccccf4ae4b1ed"
)
EXPECTED_S2_ARTIFACT_SHA256 = (
    "dcb727356fe396c9f646f54e81ee0190a13c92aa5db6804037e4bea314b174db"
)
EXPECTED_CLASS4_THEORY_SHA256 = (
    "2141bec11eb85697b0f96acc3b3b8b7279abeb2c8863a769074aec9fc6a85223"
)
EXPECTED_CLASS4_CHECKER_SHA256 = (
    "78f6ba615893d8ec4b9cd2e690e24822ab643b8c26793e27b755b1991de99468"
)

S1_SLOT_COUNT = 3
S2_SLOT_COUNT = 2
ROOT_COUNT = 256
COMPONENT_COUNT = 2
S1_COMPONENT_TERMS = S1_SLOT_COUNT * ROOT_COUNT * COMPONENT_COUNT
S2_COMPONENT_TERMS = S2_SLOT_COUNT * ROOT_COUNT * COMPONENT_COUNT
TOTAL_COMPONENT_TERMS = S1_COMPONENT_TERMS + S2_COMPONENT_TERMS
S1_HEADROOM = Fraction(127) - Fraction(44833, 65536)
S1_TARGET = Fraction(1, 4096)
ALL_SLOT_TARGET = Fraction(1, 1024)


def file_hash(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def exact_hash(value: Fraction) -> str:
    return sha256(f"{value.numerator}/{value.denominator}".encode()).hexdigest()


def decimal_text(value: Fraction) -> str:
    return str(Decimal(value.numerator) / Decimal(value.denominator))


def load_s2_checker():
    spec = importlib.util.spec_from_file_location(
        "mode2_all_slot_s2_base", S2_CHECKER
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


S2 = load_s2_checker()
BASE = S2.BASE


def load_class4_checker():
    spec = importlib.util.spec_from_file_location(
        "mode2_all_slot_class4_base", CLASS4_CHECKER
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


CLASS4 = load_class4_checker()
CLASS4_ENTRIES = CLASS4.parse_root_certificates()
CLASS4_REAL_TERMS = CLASS4.build_terms(CLASS4_ENTRIES, imag=False)
CLASS4_IMAG_TERMS = CLASS4.build_terms(CLASS4_ENTRIES, imag=True)


def evaluate_s1(task: tuple[int, bool]) -> tuple[Fraction, int, str]:
    k, imag = task
    terms = CLASS4_IMAG_TERMS if imag else CLASS4_REAL_TERMS
    class4_upper = CLASS4.upper(CLASS4.evaluate_root(k, terms))
    return (class4_upper / 256, k, "im" if imag else "re")


def validate_hashed_fraction(value: Fraction, record: dict[str, object]) -> None:
    key = "exact_sha256" if "exact_sha256" in record else "exact_sum_sha256"
    assert record[key] == exact_hash(value)
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
    assert file_hash(S2_THEORY) == EXPECTED_S2_THEORY_SHA256
    assert file_hash(S2_CHECKER) == EXPECTED_S2_CHECKER_SHA256
    assert file_hash(S2_ARTIFACT) == EXPECTED_S2_ARTIFACT_SHA256
    assert file_hash(CLASS4_THEORY) == EXPECTED_CLASS4_THEORY_SHA256
    assert file_hash(CLASS4_CHECKER) == EXPECTED_CLASS4_CHECKER_SHA256
    BASE.validate_easycrypt_constants()

    artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert artifact["schema"] == (
        "haetae-mode2-accepted-all-slot-coordinate-p8-certificate-v1"
    )
    assert artifact["root_table_sha256"] == EXPECTED_ROOT_TABLE_SHA256
    assert artifact["class_trace_sha256"] == EXPECTED_TRACE_SHA256
    assert artifact["homogeneous_class4_theory_sha256"] == EXPECTED_CLASS4_THEORY_SHA256
    assert artifact["homogeneous_class4_checker_sha256"] == EXPECTED_CLASS4_CHECKER_SHA256
    assert artifact["s2_trace_headroom_theory_sha256"] == EXPECTED_S2_THEORY_SHA256
    assert artifact["s2_trace_headroom_checker_sha256"] == EXPECTED_S2_CHECKER_SHA256
    assert artifact["s2_trace_headroom_artifact_sha256"] == EXPECTED_S2_ARTIFACT_SHA256
    assert artifact["slot_count"] == S1_SLOT_COUNT + S2_SLOT_COUNT
    assert artifact["root_count"] == ROOT_COUNT
    assert artifact["component_count"] == COMPONENT_COUNT
    assert artifact["total_component_terms"] == TOTAL_COMPONENT_TERMS

    requested = int(os.environ.get("HAETAE_ALL_SLOT_P8_WORKERS", "8"))
    workers = max(1, min(requested, os.cpu_count() or 1))
    s2_tasks = [
        (row, k, imag)
        for row in range(S2_SLOT_COUNT)
        for k in range(ROOT_COUNT)
        for imag in (False, True)
    ]
    s1_tasks = [(k, imag) for k in range(ROOT_COUNT) for imag in (False, True)]
    with ProcessPoolExecutor(max_workers=workers) as executor:
        s2_profiles = list(executor.map(BASE.evaluate, s2_tasks, chunksize=4))
        s1_profiles = list(executor.map(evaluate_s1, s1_tasks, chunksize=4))

    getcontext().prec = 50
    s1_one_row = sum(
        (profile / S1_HEADROOM**8 for profile, _, _ in s1_profiles),
        Fraction(0),
    )
    s1_three_slots = S1_SLOT_COUNT * s1_one_row
    s1_artifact = artifact["s1"]
    assert s1_artifact["slot_count"] == S1_SLOT_COUNT
    assert s1_artifact["component_terms"] == S1_COMPONENT_TERMS
    assert s1_artifact["centered_trit_moments"] == {
        "m2": "2/3", "m3": "0", "m4": "2/3",
        "m5": "0", "m6": "2/3", "m8": "2/3",
    }
    assert s1_artifact["coordinate_headroom"] == {
        "numerator": S1_HEADROOM.numerator,
        "denominator": S1_HEADROOM.denominator,
        "decimal": decimal_text(S1_HEADROOM),
    }
    validate_hashed_fraction(s1_one_row, s1_artifact["one_row_sum"])
    validate_hashed_fraction(s1_three_slots, s1_artifact["three_slot_sum"])
    assert s1_three_slots < S1_TARGET

    maximum_profile = max(s1_profiles)
    maximum_artifact = s1_artifact["maximum_profile8_upper"]
    maximum_value = Fraction(
        int(maximum_artifact["numerator"]),
        int(maximum_artifact["denominator"]),
    )
    assert maximum_profile[0] == maximum_value
    assert maximum_artifact["decimal"] == decimal_text(maximum_value)
    assert (maximum_profile[1], maximum_profile[2]) == (
        maximum_artifact["root"], maximum_artifact["component"]
    )

    s2_records = []
    for p8_upper, row, k, component in s2_profiles:
        center, radius = S2.bias_interval(row, k, component == "im")
        headroom = (
            S2.ACCUMULATOR_COORDINATE_CAP
            - S2.FFT_ENDPOINT_EPSILON
            - (abs(center) + radius)
        )
        assert headroom > 0
        s2_records.append(p8_upper / headroom**8)
    s2_sum = sum(s2_records, Fraction(0))
    s2_artifact = artifact["s2"]
    assert s2_artifact["component_terms"] == S2_COMPONENT_TERMS
    validate_hashed_fraction(s2_sum, s2_artifact)

    combined = s1_three_slots + s2_sum
    all_artifact = artifact["all_slots"]
    validate_hashed_fraction(combined, all_artifact)
    assert ALL_SLOT_TARGET == Fraction(
        all_artifact["target_numerator"], all_artifact["target_denominator"]
    )
    assert combined < ALL_SLOT_TARGET
    assert all_artifact["strictly_below_target"] is True
    margin = Fraction(1) - 1024 * combined
    assert all_artifact["scaled_margin_decimal"] == decimal_text(margin)

    source = EASYCRYPT_CERTIFICATE.read_text(encoding="utf-8")
    assert parse_easycrypt_fraction(
        source, "ideal_mode2_s1_coordinate_headroom"
    ) == S1_HEADROOM
    assert parse_easycrypt_fraction(
        source, "ideal_mode2_all_slot_coordinate_p8_target"
    ) == ALL_SLOT_TARGET
    assert "op ideal_mode2_all_slot_coordinate_p8_numeric_certificate" in source
    assert "s1_coordinate_markov8_sum_lt_one_over_4096" in source
    assert "coordinate_headroom_bad_mu_lt_one_over_1024" in source

    print(
        "PASS accepted all-slot coordinate P8 certificate: "
        f"components={TOTAL_COMPONENT_TERMS}, s1={decimal_text(s1_three_slots)}, "
        f"s2={decimal_text(s2_sum)}, total={decimal_text(combined)} < 1/1024; "
        f"trace_sha256={EXPECTED_TRACE_SHA256}"
    )


if __name__ == "__main__":
    main()
