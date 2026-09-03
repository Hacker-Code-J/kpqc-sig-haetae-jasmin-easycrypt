#!/usr/bin/env python3
"""Regression checker for the ordered class-trace upper-prefix P8 evaluator."""

from collections import Counter
from decimal import Decimal, getcontext
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import sys


sys.dont_write_bytecode = True
sys.set_int_max_str_digits(1_000_000)
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

ROOT = Path(__file__).resolve().parents[2]
POST_FREEZE = ROOT / "haetae-topdown-easycrypt/post-freeze"

ZERO_TRACE_ARTIFACT = POST_FREEZE / "mode2-zero-seed-accepted-class-trace.json"
UPPER_PREFIX_ARTIFACT = (
    POST_FREEZE
    / "mode2-zero-seed-accepted-upper-prefix-component-p8-certificate.json"
)
FIRST_ATTEMPT_FEASIBILITY = (
    POST_FREEZE / "mode2-first-attempt-accepted-context-feasibility.json"
)
SEED27_ARTIFACT = (
    POST_FREEZE / "mode2-first-attempt-seed27-ordered-class-trace-p8.json"
)
UPPER_PREFIX_CHECKER = (
    POST_FREEZE / "check-mode2-accepted-upper-prefix-component-p8-certificate.py"
)
EXTRACTOR_SOURCE = (
    POST_FREEZE / "extract-mode2-first-attempt-class-trace.c"
)
ORDERED_EVALUATOR_THEORY = (
    POST_FREEZE / "Mode2FaithfulSecurityOrderedClassTraceP8EvaluatorPostFreeze.ec"
)

ROW_COUNT = 2
ROOT_COUNT = 256
CLASS_COUNT = 6
TARGET = Fraction(1, 2)
EXPECTED_ZERO_BOUND_HASH = (
    "ba044b47b38b55e241fe27becae33d17abfaee70575e9a640d0a70ca37362bec"
)
EXPECTED_SEED27_BOUND_HASH = (
    "03865df2e151434f8d83dbea5f4e26a696065cf1ea8f22660f81ced3f508763f"
)
EXPECTED_SEED27_BOUND_DECIMAL = (
    "0.36118553610112440682779752758327045173735490715089"
)
EXPECTED_SEED27_TRACE_HASH = (
    "ee68332469edc195b37a4b26015f5b7bcd2edf4d0254e89e5e5a9b2b4b6a2d5b"
)


def file_hash(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def canonical_hash(value: object) -> str:
    encoded = json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode()
    return sha256(encoded).hexdigest()


def exact_hash(value: Fraction) -> str:
    return sha256(f"{value.numerator}/{value.denominator}".encode()).hexdigest()


def decimal_text(value: Fraction) -> str:
    return str(Decimal(value.numerator) / Decimal(value.denominator))


def fraction_record(value: Fraction) -> dict[str, object]:
    return {
        "exact_sum_sha256": exact_hash(value),
        "numerator_digits": len(str(value.numerator)),
        "denominator_digits": len(str(value.denominator)),
        "decimal": decimal_text(value),
    }


def load_upper_checker():
    spec = importlib.util.spec_from_file_location(
        "mode2_ordered_class_trace_p8_upper", UPPER_PREFIX_CHECKER
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


UPPER = load_upper_checker()


def compute_for_trace(trace: list[list[int]]) -> dict[str, Fraction]:
    assert UPPER.BASE is UPPER.S2.BASE
    assert UPPER.BASE is UPPER.ALL_SLOT.BASE
    original = UPPER.BASE.TRACES
    UPPER.BASE.TRACES = trace
    try:
        return UPPER.compute()
    finally:
        UPPER.BASE.TRACES = original


def validate_trace_shape(trace: list[list[int]]) -> None:
    assert len(trace) == ROW_COUNT
    assert all(len(row) == ROOT_COUNT for row in trace)
    assert all(0 <= value < CLASS_COUNT for row in trace for value in row)


def histograms(trace: list[list[int]]) -> list[list[int]]:
    return [
        [Counter(row)[class_value] for class_value in range(CLASS_COUNT)]
        for row in trace
    ]


def rotate_rows(trace: list[list[int]]) -> list[list[int]]:
    return [row[1:] + row[:1] for row in trace]


def p8_bad(value: Fraction) -> bool:
    return TARGET <= value


def validate_seed27_artifact(
    artifact: dict[str, object], feasibility: dict[str, object]
) -> list[list[int]]:
    assert artifact["schema"] == "haetae-mode2-ordered-class-trace-p8-seed27-v1"
    trace = artifact["class_trace"]
    validate_trace_shape(trace)
    expected = feasibility["accepted_fixture"]
    family = feasibility["fixture_family"]
    assert artifact["seed_index"] == family["first_accepted_seed_index"] == 27
    assert artifact["seed_hex"] == expected["seed_hex"]
    assert artifact["rhoprime_hex"] == expected["rhoprime_hex"]
    assert artifact["sigma_hex"] == expected["sigma_hex"]
    assert artifact["accepted"] is True
    assert artifact["counter_start"] == expected["counter_start"] == 0
    assert artifact["counter_end"] == expected["counter_end"] == 5
    assert artifact["squared_singular_value"] == expected["squared_singular_value"] == 533485
    assert artifact["acceptance_bound_floor"] == family["acceptance_bound_floor"] == 611098
    assert artifact["pre_bp_sha256"] == expected["pre_bp_sha256"]
    assert artifact["avec_sha256"] == expected["avec_sha256"]
    trace_hash = canonical_hash(trace)
    assert trace_hash == artifact["class_trace_sha256"]
    assert trace_hash == expected["class_trace_sha256"] == EXPECTED_SEED27_TRACE_HASH
    trace_histograms = histograms(trace)
    assert trace_histograms == artifact["class_histograms"]
    assert trace_histograms == expected["class_histograms"]
    return trace


def inspect_ordered_evaluator_theory(expected_sha256: str) -> dict[str, object]:
    assert ORDERED_EVALUATOR_THEORY.exists()
    source = ORDERED_EVALUATOR_THEORY.read_text(encoding="utf-8")
    symbols = {
        "trace_p8_union_bound": "trace_p8_union_bound" in source,
        "bad_predicate": "ordered_class_trace_p8_bad" in source,
        "zero_structure_certificate": (
            "zero_seed_accepted_ordered_class_trace_structure_certificate"
            in source
        ),
        "zero_specialization": (
            "zero_seed_accepted_ordered_class_trace_component_markov8_sumE"
            in source
        ),
        "zero_not_bad": (
            "zero_seed_accepted_ordered_class_trace_not_p8_bad" in source
        ),
        "concrete_bridge": (
            "sampled_dseed_first_attempt_accepted_ordered_class_trace_p8_pr_le_certificate"
            in source
        ),
    }
    assert all(symbols.values())
    theory_sha256 = file_hash(ORDERED_EVALUATOR_THEORY)
    assert theory_sha256 == expected_sha256
    return {
        "status": "present",
        "path": ORDERED_EVALUATOR_THEORY.name,
        "sha256": theory_sha256,
        "symbols": symbols,
    }


def build_expected_seed27_artifact(
    trace: list[list[int]],
    feasibility: dict[str, object],
    union_record: dict[str, object],
) -> dict[str, object]:
    validate_trace_shape(trace)
    family = feasibility["fixture_family"]
    accepted = feasibility["accepted_fixture"]
    feasibility_record = feasibility["current_fixed_cap_diagnostic"]["component_union"]
    assert union_record == feasibility_record
    assert union_record["exact_sum_sha256"] == EXPECTED_SEED27_BOUND_HASH
    assert union_record["decimal"] == EXPECTED_SEED27_BOUND_DECIMAL
    return {
        "schema": "haetae-mode2-ordered-class-trace-p8-seed27-v1",
        "seed_index": family["first_accepted_seed_index"],
        "seed_hex": accepted["seed_hex"],
        "rhoprime_hex": accepted["rhoprime_hex"],
        "sigma_hex": accepted["sigma_hex"],
        "accepted": True,
        "counter_start": accepted["counter_start"],
        "counter_end": accepted["counter_end"],
        "squared_singular_value": accepted["squared_singular_value"],
        "acceptance_bound_floor": family["acceptance_bound_floor"],
        "pre_bp_sha256": accepted["pre_bp_sha256"],
        "avec_sha256": accepted["avec_sha256"],
        "class_trace_sha256": canonical_hash(trace),
        "class_histograms": histograms(trace),
        "class_trace": trace,
        "generic_union_record": union_record,
        "p8_bad": False,
        "source_sha256": {
            "extractor_source": file_hash(EXTRACTOR_SOURCE),
            "upper_prefix_checker": file_hash(UPPER_PREFIX_CHECKER),
            "upper_prefix_artifact": file_hash(UPPER_PREFIX_ARTIFACT),
            "zero_seed_trace_artifact": file_hash(ZERO_TRACE_ARTIFACT),
            "first_attempt_feasibility_artifact": file_hash(FIRST_ATTEMPT_FEASIBILITY),
            "ordered_evaluator_theory": file_hash(ORDERED_EVALUATOR_THEORY),
        },
    }


def main() -> None:
    getcontext().prec = 50
    zero_artifact = json.loads(ZERO_TRACE_ARTIFACT.read_text(encoding="utf-8"))
    upper_artifact = json.loads(UPPER_PREFIX_ARTIFACT.read_text(encoding="utf-8"))
    feasibility = json.loads(FIRST_ATTEMPT_FEASIBILITY.read_text(encoding="utf-8"))
    committed_seed27 = json.loads(SEED27_ARTIFACT.read_text(encoding="utf-8"))

    assert zero_artifact["schema"] == "haetae-mode2-accepted-class-trace-v1"
    zero_trace = zero_artifact["class_trace"]
    validate_trace_shape(zero_trace)
    assert canonical_hash(zero_trace) == zero_artifact["class_trace_sha256"]
    zero_histograms = histograms(zero_trace)
    assert zero_histograms == zero_artifact["class_histograms"]

    assert upper_artifact["schema"] == (
        "haetae-mode2-accepted-upper-prefix-component-p8-certificate-v1"
    )
    assert upper_artifact["full_target"] == {"numerator": 1, "denominator": 2}
    zero_expected = upper_artifact["upper_prefix_component_union"]
    assert zero_expected["exact_sum_sha256"] == EXPECTED_ZERO_BOUND_HASH
    assert upper_artifact["full_reduced_headroom_union"] == zero_expected

    seed27_trace = validate_seed27_artifact(committed_seed27, feasibility)
    seed27_values = compute_for_trace(seed27_trace)
    seed27_record = fraction_record(seed27_values["component_union"])
    assert p8_bad(seed27_values["component_union"]) is False
    expected_seed27 = build_expected_seed27_artifact(
        seed27_trace, feasibility, seed27_record
    )

    if "--emit-artifact" in sys.argv:
        print(json.dumps(expected_seed27, indent=2))
        return

    assert committed_seed27 == expected_seed27

    zero_values = compute_for_trace(zero_trace)
    zero_record = fraction_record(zero_values["component_union"])
    assert zero_record == zero_expected
    assert zero_values["full_union"] == zero_values["component_union"]
    assert p8_bad(zero_values["component_union"]) is False

    assert seed27_record == committed_seed27["generic_union_record"]
    assert seed27_record == feasibility["current_fixed_cap_diagnostic"]["component_union"]
    assert p8_bad(seed27_values["component_union"]) is False

    rotated = rotate_rows(zero_trace)
    validate_trace_shape(rotated)
    assert histograms(rotated) == zero_histograms
    rotated_record = fraction_record(compute_for_trace(rotated)["component_union"])
    assert rotated_record["exact_sum_sha256"] != zero_record["exact_sum_sha256"]

    theory_status = inspect_ordered_evaluator_theory(
        committed_seed27["source_sha256"]["ordered_evaluator_theory"]
    )

    print(
        "PASS ordered class-trace P8 evaluator: "
        f"zero={zero_record['decimal']}, "
        f"seed27={seed27_record['decimal']}, "
        f"rotated_zero_changed={rotated_record['exact_sum_sha256'] != zero_record['exact_sum_sha256']}, "
        f"theory={theory_status['status']}"
    )


if __name__ == "__main__":
    main()
