#!/usr/bin/env python3
"""Audit whether the current P8 interface supports an accepted-context theorem.

This is a feasibility and counterexample-to-certificate checker, not a claim
about the real accumulator failure probability.  It first confirms that the
current proof surface connects acceptance only to the singular score/context
validity, while the useful S2 P8 lemmas separately require equality with the
fixed zero-seed class trace.  It then finds the first accepted first-attempt
fixture in a deterministic seed-index family and applies the existing exact
fixed-cap P8 computation to that fixture's full ordered class trace.
"""

from collections import Counter
from decimal import Decimal, getcontext
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


sys.dont_write_bytecode = True
sys.set_int_max_str_digits(1_000_000)
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

ROOT = Path(__file__).resolve().parents[2]
POST_FREEZE = ROOT / "haetae-topdown-easycrypt/post-freeze"
REFERENCE = ROOT / "haetae-ref"

HARNESS = POST_FREEZE / "extract-mode2-first-attempt-class-trace.c"
UPPER_CHECKER = (
    POST_FREEZE
    / "check-mode2-accepted-upper-prefix-component-p8-certificate.py"
)
DECISION_THEORY = (
    POST_FREEZE / "Mode2FaithfulSecurityFirstAttemptDecisionPostFreeze.ec"
)
ACTUAL_CONTEXT_THEORY = (
    POST_FREEZE
    / "Mode2FaithfulSecurityActualAccumulatorContextBridgePostFreeze.ec"
)
UPPER_THEORY = (
    POST_FREEZE
    / "Mode2FaithfulSecurityIdealAccumulatorUpperPrefixComponentP8CertificatePostFreeze.ec"
)
FEASIBILITY_THEORY = (
    POST_FREEZE
    / "Mode2FaithfulSecurityAcceptedContextClassTraceFeasibilityPostFreeze.ec"
)
ARTIFACT = (
    POST_FREEZE
    / "mode2-first-attempt-accepted-context-feasibility.json"
)

SOURCES = [
    "fips202.c",
    "symmetric-shake.c",
    "reduce.c",
    "ntt.c",
    "poly.c",
    "sampler.c",
    "polyvec.c",
    "polymat.c",
    "fixpoint.c",
    "fft.c",
    "decompose.c",
]

MAX_SEED_INDEX = 255
ACCEPTANCE_BOUND = 611098
TARGET = Fraction(1, 2)


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
        "mode2_first_attempt_feasibility_upper", UPPER_CHECKER
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


UPPER = load_upper_checker()


def build_harness(output: Path) -> None:
    compiler = os.environ.get("CC", "cc")
    command = [
        compiler,
        "-O2",
        "-std=c11",
        "-Wall",
        "-Wextra",
        "-Werror",
        "-DHAETAE_CONFIG_MODE=HAETAE_MODE2",
        f"-I{REFERENCE / 'include'}",
        str(HARNESS),
        *(str(REFERENCE / "src" / source) for source in SOURCES),
        "-lm",
        "-o",
        str(output),
    ]
    subprocess.run(command, cwd=ROOT, check=True)


def run_harness(binary: Path, seed_index: int) -> dict[str, object]:
    completed = subprocess.run(
        [str(binary), str(seed_index)],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return json.loads(completed.stdout)


def seed_hex(seed_index: int) -> str:
    return seed_index.to_bytes(8, "little").hex() + "00" * 24


def class_index(pre_bp: int, avec: int) -> int:
    rho = (pre_bp + avec) % 64513
    if rho == 0:
        return 0
    if rho == 64512:
        return 1
    return 2 + rho % 4


def validate_fixture(fixture: dict[str, object], seed_index: int) -> None:
    assert fixture["schema"] == "haetae-mode2-first-attempt-class-trace-v1"
    assert fixture["seed_index"] == seed_index
    assert fixture["seed_hex"] == seed_hex(seed_index)
    assert fixture["counter_start"] == 0
    assert fixture["counter_end"] == 5
    assert fixture["acceptance_bound_floor"] == ACCEPTANCE_BOUND
    assert fixture["accepted"] == (
        fixture["squared_singular_value"] <= ACCEPTANCE_BOUND
    )

    pre_bp = fixture["pre_bp"]
    avec = fixture["avec"]
    trace = fixture["class_trace"]
    assert len(pre_bp) == len(avec) == len(trace) == 2
    assert all(len(row) == 256 for row in pre_bp)
    assert all(len(row) == 256 for row in avec)
    assert all(len(row) == 256 for row in trace)
    assert all(-32768 <= value <= 32767 for row in pre_bp for value in row)
    assert all(0 <= value < 64513 for row in avec for value in row)
    recomputed = [
        [class_index(pre_bp[row][j], avec[row][j]) for j in range(256)]
        for row in range(2)
    ]
    assert trace == recomputed
    assert all(0 <= value <= 5 for row in trace for value in row)


def first_accepted_fixture(binary: Path) -> tuple[dict[str, object], list[int]]:
    scores = []
    for seed_index in range(MAX_SEED_INDEX + 1):
        fixture = run_harness(binary, seed_index)
        validate_fixture(fixture, seed_index)
        scores.append(fixture["squared_singular_value"])
        if fixture["accepted"]:
            return fixture, scores
    raise AssertionError(
        f"no accepted first attempt in seed indices 0..{MAX_SEED_INDEX}"
    )


def validate_class_reachability() -> list[dict[str, int]]:
    # These signed-16/canonical-a scalar witnesses show that context validity
    # alone admits every class.  They do not claim reachability from KeyGen.
    witnesses = [(0, 0), (-1, 0), (4, 0), (1, 0), (2, 0), (3, 0)]
    records = []
    for expected, (pre_bp, avec) in enumerate(witnesses):
        assert -32768 <= pre_bp <= 32767
        assert 0 <= avec < 64513
        assert class_index(pre_bp, avec) == expected
        records.append({"class": expected, "pre_bp": pre_bp, "avec": avec})
    return records


def validate_proof_surface() -> dict[str, object]:
    decision = DECISION_THEORY.read_text(encoding="utf-8")
    actual = ACTUAL_CONTEXT_THEORY.read_text(encoding="utf-8")
    upper = UPPER_THEORY.read_text(encoding="utf-8")
    feasibility = FEASIBILITY_THEORY.read_text(encoding="utf-8")

    assert "checked_mode2_first_attempt_decision_accepted_iff_score_le" in decision
    assert "ideal_final_s2_row_class_trace" not in decision
    assert "checked_first_attempt_snapshot_trace_local_context_valid" in actual
    assert "does not identify the actual" in actual
    assert "accumulator law with one fixed" in actual
    assert "zero_seed_accepted_trace" not in actual
    assert "ideal_final_s2_row_class_trace pre_bp avec row =" in upper
    assert "zero_seed_accepted_trace row" in upper
    assert "every_scalar_class_has_a_valid_context" in feasibility
    assert "A useful accepted-context optimization still" in feasibility

    return {
        "status": "UNDER_SPECIFIED_ACCEPTED_CONTEXT_DOMAIN",
        "acceptance_surface": "score<=611098 plus trace-local context validity",
        "missing_bridge": (
            "accepted first-attempt snapshot -> admissible ordered class-trace set"
        ),
        "histogram_exact": False,
        "reason": (
            "the bias and P8 recurrences are ordered root-weighted functions "
            "of the full trace"
        ),
    }


def compute_for_trace(trace: list[list[int]]) -> dict[str, Fraction]:
    assert UPPER.BASE is UPPER.S2.BASE
    assert UPPER.BASE is UPPER.ALL_SLOT.BASE
    original = UPPER.BASE.TRACES
    UPPER.BASE.TRACES = trace
    try:
        return UPPER.compute()
    finally:
        UPPER.BASE.TRACES = original


def compute_result() -> dict[str, object]:
    getcontext().prec = 50
    with tempfile.TemporaryDirectory(
        prefix="haetae-first-attempt-feasibility-"
    ) as directory:
        binary = Path(directory) / "extract-mode2-first-attempt-class-trace"
        build_harness(binary)
        fixture, scores = first_accepted_fixture(binary)

    trace = fixture["class_trace"]
    values = compute_for_trace(trace)
    histograms = [
        [Counter(row)[class_value] for class_value in range(6)]
        for row in trace
    ]
    component_union = values["component_union"]
    subhalf = component_union < TARGET
    diagnostic_status = (
        "NO_COUNTEREXAMPLE_AT_FIRST_ACCEPTED_FIXTURE"
        if subhalf
        else "CURRENT_FIXED_CAP_CERTIFICATE_NOT_UNIFORM"
    )

    return {
        "schema": "haetae-mode2-first-attempt-accepted-context-feasibility-v1",
        "proof_surface": validate_proof_surface(),
        "context_validity_class_witnesses": validate_class_reachability(),
        "fixture_family": {
            "seed_encoding": "uint64 little-endian followed by 24 zero bytes",
            "searched_seed_interval": {
                "first": 0,
                "last": fixture["seed_index"],
                "inclusive": True,
            },
            "first_accepted_seed_index": fixture["seed_index"],
            "first_attempt_scores": scores,
            "acceptance_bound_floor": ACCEPTANCE_BOUND,
        },
        "accepted_fixture": {
            "seed_hex": fixture["seed_hex"],
            "rhoprime_hex": fixture["rhoprime_hex"],
            "sigma_hex": fixture["sigma_hex"],
            "counter_start": fixture["counter_start"],
            "counter_end": fixture["counter_end"],
            "squared_singular_value": fixture["squared_singular_value"],
            "pre_bp_sha256": canonical_hash(fixture["pre_bp"]),
            "avec_sha256": canonical_hash(fixture["avec"]),
            "class_trace_sha256": canonical_hash(trace),
            "class_histograms": histograms,
        },
        "current_fixed_cap_diagnostic": {
            "status": diagnostic_status,
            "s1_component_cap": UPPER.S1_COMPONENT_CAP.numerator,
            "s2_component_cap": UPPER.S2_COMPONENT_CAP.numerator,
            "full_budget": fraction_record(values["full_budget"]),
            "minimum_s2_residual_headroom": fraction_record(
                values["minimum_s2_headroom"]
            ),
            "s1_component_union": fraction_record(values["s1_upper"]),
            "s2_component_union": fraction_record(values["s2_upper"]),
            "component_union": fraction_record(component_union),
            "target": "1/2",
            "subhalf": subhalf,
        },
        "source_sha256": {
            "first_attempt_harness": file_hash(HARNESS),
            "upper_prefix_checker": file_hash(UPPER_CHECKER),
            "first_attempt_decision_theory": file_hash(DECISION_THEORY),
            "actual_context_theory": file_hash(ACTUAL_CONTEXT_THEORY),
            "upper_prefix_theory": file_hash(UPPER_THEORY),
            "class_trace_feasibility_theory": file_hash(FEASIBILITY_THEORY),
        },
        "claim_boundary": {
            "establishes": (
                "the current proof surface does not define an accepted "
                "class-trace domain; the numeric result is a diagnostic on "
                "one reproducible actual accepted first-attempt context"
            ),
            "does_not_establish": [
                "an actual accumulator failure lower bound",
                "infeasibility of every possible accepted-context analysis",
                "a distribution for accepted class traces",
                "an XOF-to-ideal coupling",
            ],
        },
    }


def main() -> None:
    result = compute_result()
    if "--emit-artifact" in sys.argv:
        print(json.dumps(result, indent=2))
        return

    artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert artifact == result
    diagnostic = result["current_fixed_cap_diagnostic"]
    print(
        "PASS first-attempt accepted-context feasibility audit: "
        f"domain={result['proof_surface']['status']}, "
        f"seed_index={result['fixture_family']['first_accepted_seed_index']}, "
        f"score={result['accepted_fixture']['squared_singular_value']}, "
        f"certificate={diagnostic['status']}, "
        f"union={diagnostic['component_union']['decimal']}"
    )


if __name__ == "__main__":
    main()
