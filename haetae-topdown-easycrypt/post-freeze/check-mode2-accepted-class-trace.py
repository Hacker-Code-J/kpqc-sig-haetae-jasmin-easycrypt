#!/usr/bin/env python3
"""Rebuild and verify the deterministic accepted-attempt class trace."""

from collections import Counter
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
POST_FREEZE = ROOT / "haetae-topdown-easycrypt/post-freeze"
REFERENCE = ROOT / "haetae-ref"
HARNESS = POST_FREEZE / "extract-mode2-accepted-class-trace.c"
ARTIFACT = POST_FREEZE / "mode2-zero-seed-accepted-class-trace.json"
EASYCRYPT_TRACE = (
    POST_FREEZE
    / "Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentZeroSeedAcceptedTraceCertificatePostFreeze.ec"
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


def canonical_hash(value: object) -> str:
    encoded = json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode()
    return sha256(encoded).hexdigest()


def class_index(pre_bp: int, avec: int) -> int:
    rho = (pre_bp + avec) % 64513
    if rho == 0:
        return 0
    if rho == 64512:
        return 1
    return 2 + rho % 4


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


def run_harness(binary: Path) -> tuple[str, dict[str, object]]:
    completed = subprocess.run(
        [str(binary)], cwd=ROOT, check=True, capture_output=True, text=True
    )
    return completed.stdout, json.loads(completed.stdout)


def validate_observed(observed: dict[str, object]) -> None:
    assert observed["schema"] == "haetae-mode2-accepted-class-trace-v1"
    assert observed["seed_hex"] == "00" * 32
    assert observed["accepted_attempt"] == 2
    assert observed["attempt_scores"] == [660097, 788110, 610851]
    assert observed["counter_start"] == 10
    assert observed["counter_end"] == 15
    assert observed["squared_singular_value"] == 610851
    assert observed["acceptance_bound_floor"] == 611098

    pre_bp = observed["pre_bp"]
    avec = observed["avec"]
    trace = observed["class_trace"]
    assert len(pre_bp) == len(avec) == len(trace) == 2
    assert all(len(row) == 256 for row in pre_bp)
    assert all(len(row) == 256 for row in avec)
    assert all(len(row) == 256 for row in trace)
    assert all(-32768 <= value <= 32767 for row in pre_bp for value in row)
    assert all(0 <= value < 64513 for row in avec for value in row)

    recomputed = [
        [class_index(pre_bp[row][column], avec[row][column]) for column in range(256)]
        for row in range(2)
    ]
    assert trace == recomputed
    assert all(0 <= value <= 5 for row in trace for value in row)


def validate_artifact(
    observed: dict[str, object], artifact: dict[str, object]
) -> None:
    copied_fields = [
        "schema",
        "seed_hex",
        "rhoprime_hex",
        "sigma_hex",
        "accepted_attempt",
        "attempt_scores",
        "counter_start",
        "counter_end",
        "squared_singular_value",
        "acceptance_bound_floor",
        "class_trace",
    ]
    for field in copied_fields:
        assert artifact[field] == observed[field]

    assert artifact["pre_bp_sha256"] == canonical_hash(observed["pre_bp"])
    assert artifact["avec_sha256"] == canonical_hash(observed["avec"])
    assert artifact["class_trace_sha256"] == canonical_hash(
        observed["class_trace"]
    )
    histograms = [
        [Counter(row)[class_value] for class_value in range(6)]
        for row in observed["class_trace"]
    ]
    assert artifact["class_histograms"] == histograms


def validate_easycrypt_trace(artifact: dict[str, object]) -> None:
    source = EASYCRYPT_TRACE.read_text(encoding="utf-8")
    rows = []
    for name in (
        "zero_seed_accepted_row0_classes",
        "zero_seed_accepted_row1_classes",
    ):
        body = source.split(f"op {name} : int list = [", 1)[1].split(
            "].", 1
        )[0]
        rows.append([int(value) for value in re.findall(r"-?\d+", body)])
    assert rows == artifact["class_trace"]


def main() -> None:
    artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory(prefix="haetae-class-trace-") as directory:
        binary = Path(directory) / "extract-mode2-accepted-class-trace"
        build_harness(binary)
        first_raw, first = run_harness(binary)
        second_raw, second = run_harness(binary)

    assert first_raw == second_raw
    assert first == second
    validate_observed(first)
    validate_artifact(first, artifact)
    validate_easycrypt_trace(artifact)
    print(
        "PASS deterministic mode2 accepted class trace: "
        f"attempt={first['accepted_attempt']}, counter={first['counter_start']}, "
        f"score={first['squared_singular_value']}, "
        f"histograms={artifact['class_histograms']}, "
        f"trace_sha256={artifact['class_trace_sha256']}"
    )


if __name__ == "__main__":
    main()
