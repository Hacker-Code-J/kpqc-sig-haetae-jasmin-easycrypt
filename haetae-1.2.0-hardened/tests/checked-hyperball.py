#!/usr/bin/env python3
"""Exercise checked helpers and production exports; candidates are not SHAKE seeds.

Prerequisites: make -C haetae-1.2.0-jasmin -j1 libs, then
make -C haetae-1.2.0-hardened -j1 libs. This script rebuilds its own wrapper.
"""

import argparse
import ctypes as C
from collections import Counter
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import random
import shlex
import subprocess
import sys


PROJECT = Path(__file__).resolve().parents[1]
ROOT = PROJECT.parent
BASELINE = ROOT / "haetae-1.2.0-jasmin"
FIXTURE_PATH = ROOT / "haetae-1.2.0-easycrypt/tests/hyperball-norm-boundary.py"
BUILD = PROJECT / "build/test"
WRAPPER = PROJECT / "tests/checked-hyperball.jazz"
SEED = 0x484145544145120
MOD64 = 1 << 64
MASK64 = MOD64 - 1
MASK48 = (1 << 48) - 1
MASK32 = (1 << 32) - 1
INT32_MAX = (1 << 31) - 1
INT32_MIN = -(1 << 31)
SENTINEL = 0xA5B6C7D8
U64, U32, U8 = C.c_uint64, C.c_uint32, C.c_uint8
P64, P32, P8 = C.POINTER(U64), C.POINTER(U32), C.POINTER(U8)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def signed32(word):
    word &= MASK32
    return word if word <= INT32_MAX else word - (1 << 32)


def integer_norm(a, b):
    # Python integers deliberately retain every carry and multiple wrap.
    return sum(signed32(value) ** 2 for value in (*a, *b))


def signs_bytes(bits):
    out = (U8 * 512)()
    for index, bit in enumerate(bits):
        out[index // 8] |= (int(bit) & 1) << (index % 8)
    return out


def padded32(values):
    out = (U32 * 2048)(*([SENTINEL] * 2048))
    for index, value in enumerate(values):
        out[index] = value & MASK32
    return out


def load_fixtures():
    # The baseline module contains only definitions at import time; its build
    # and execution are protected by __name__ == "__main__".
    spec = importlib.util.spec_from_file_location("haetae_boundary_fixture", FIXTURE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot import baseline fixture definitions: {FIXTURE_PATH}")
    module = importlib.util.module_from_spec(spec)
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = previous
    return module


def production_library(mode):
    return PROJECT / f"build/mode{mode}/lib/libhaetae-mode{mode}-hardened-jazz.so"


def check_production_build(modes):
    process = subprocess.run([sys.executable, str(PROJECT / "scripts/materialize.py"), "--check"],
                             cwd=PROJECT, capture_output=True, text=True)
    if process.returncode:
        raise RuntimeError("Hardened materialization is not current; run make -C "
                           f"{PROJECT} -j1 libs.\n{process.stdout}{process.stderr}")
    # baseline.mk is the effective compilation recipe. The outer Makefile
    # forwards commands and may gain unrelated test/documentation targets.
    dependencies = [PROJECT / "build/baseline.mk"]
    dependencies.extend(path for path in (PROJECT / "jasmin").rglob("*") if path.is_file())
    newest = max(path.stat().st_mtime_ns for path in dependencies)
    for mode in modes:
        library = production_library(mode)
        if not library.is_file() or library.stat().st_mtime_ns < newest:
            raise RuntimeError(f"Missing or stale hardened mode {mode} library; "
                               f"run make -C {PROJECT} -j1 libs before this suite.")


def build_wrapper():
    phase = PROJECT / "jasmin/hyperball_phase.jinc"
    if not phase.is_file():
        raise RuntimeError("Materialize haetae-1.2.0-hardened before running these tests.")
    BUILD.mkdir(parents=True, exist_ok=True)
    assembly = BUILD / "checked-hyperball.s"
    library = BUILD / "checked-hyperball.so"
    commands = [
        [*shlex.split(os.environ.get("JASMINC", "jasminc")), "-auto-spill-all",
         "-o", str(assembly), str(WRAPPER)],
        [*shlex.split(os.environ.get("CC", "cc")), "-shared", "-fPIC",
         "-Wl,-z,noexecstack", "-o", str(library), str(assembly)],
    ]
    log_path = BUILD / "checked-hyperball-build.log"
    with log_path.open("w", encoding="utf-8") as log:
        for command in commands:
            log.write(shlex.join(command) + "\n")
            log.flush()
            process = subprocess.run(command, cwd=PROJECT, stdout=log, stderr=subprocess.STDOUT)
            if process.returncode:
                log.flush()
                details = "\n".join(log_path.read_text(errors="replace").splitlines()[-35:])
                raise RuntimeError(f"Test wrapper build failed ({process.returncode}):\n{details}")
    return library


def load_checked(path):
    lib = C.CDLL(str(path))
    signatures = {
        "test_checked_scalar": [P64, U64, U64, U64, U64],
        "test_checked_norm": [P64, P32, U64, P32, U64],
        "test_checked_scale": [P32, P32, P64, P64, P8, P64],
        "test_checked_combined": [P32, P32, P64, P64, P8, P64],
    }
    for name, arguments in signatures.items():
        function = getattr(lib, name)
        function.argtypes = arguments
        function.restype = None
    return lib


class Suite:
    def __init__(self):
        self.categories = Counter()
        self.assertions = 0
        self.current = "initialization"
        self.fixtures = []
        self.artifacts = {}

    def begin(self, group, name):
        self.current = f"{group}/{name}"

    def passed(self, group):
        self.categories[group] += 1

    def equal(self, label, actual, expected):
        self.assertions += 1
        if actual != expected:
            raise AssertionError(f"{self.current}: {label}: expected {expected!r}, got {actual!r}")

    def scalar(self, x, scale, sign):
        out = (U64 * 2)()
        self.checked.test_checked_scalar(out, x, *scale, sign)
        return tuple(out)

    def scalar_oracle(self, x, scale, sign):
        # Observe the unchanged multiplication through its original public ABI.
        # The guard oracle then uses unbounded rounding and the signed32 limit.
        product = (U64 * 2)()
        self.legacy.fixpoint_mul_jazz(
            product, (U64 * 2)((x & MASK32) << 16, x >> 32), (U64 * 2)(*scale))
        magnitude = (int(product[1]) + 16384) // 32768
        coefficient = self.legacy.fixpoint_mul_rnd13_jazz(x, (U64 * 2)(*scale), sign)
        return coefficient, MASK64 if magnitude > INT32_MAX else 0, magnitude, int(product[1])

    def norm(self, a, b):
        out = (U64 * 2)()
        self.checked.test_checked_norm(out, padded32(a), len(a), padded32(b), len(b))
        return tuple(out)

    def combined(self, library, values, bits, scale, left, bound, checked, initial_acceptance=0xBAD):
        a, b = padded32([]), padded32([])
        samples = (U64 * 4096)(*values)
        signs = signs_bytes(bits)
        factor = (U64 * 2)(*scale)
        state = (U64 * 4)(left, len(values), bound, initial_acceptance)
        if checked:
            library.test_checked_combined(a, b, state, samples, signs, factor)
        else:
            library.polyfixveclk_scale_and_check_jazz(a, b, state, samples, signs, factor)
        self.equal("state input fields", tuple(state[:3]), (left, len(values), bound))
        self.equal("left frame", list(a[left:]), [SENTINEL] * (2048-left))
        self.equal("right frame", list(b[len(values)-left:]), [SENTINEL] * (2048-len(values)+left))
        self.equal("samples input", list(samples), values + [0] * (4096-len(values)))
        self.equal("sign input", bytes(signs), bytes(signs_bytes(bits)))
        self.equal("scale input", tuple(factor), scale)
        return list(a[:left]), list(b[:len(values)-left]), int(state[3])

    def scaled(self, values, bits, scale, left):
        a, b = padded32([]), padded32([])
        state = (U64 * 3)(left, len(values), 0xBAD)
        self.checked.test_checked_scale(a, b, state, (U64 * 4096)(*values),
                                        signs_bytes(bits), (U64 * 2)(*scale))
        self.equal("scale counts", tuple(state[:2]), (left, len(values)))
        self.equal("scale left frame", list(a[left:]), [SENTINEL] * (2048-left))
        self.equal("scale right frame", list(b[len(values)-left:]), [SENTINEL] * (2048-len(values)+left))
        return list(a[:left]), list(b[:len(values)-left]), int(state[2])

    def scalar_boundaries(self):
        for magnitude in (0, 1, INT32_MAX-1, INT32_MAX, 1 << 31, (1 << 31)+1):
            for sign in (0, 1):
                self.begin("cast_boundary", f"magnitude={magnitude},sign={sign}")
                expected = ((-magnitude if sign else magnitude) & MASK32,
                            MASK64 if magnitude > INT32_MAX else 0)
                result = self.scalar(1 << 63, (0, magnitude << 12), sign)
                self.equal("exact constructed scalar", result, expected)
                self.equal("legacy coefficient", result[0], self.legacy.fixpoint_mul_rnd13_jazz(
                    1 << 63, (U64 * 2)(0, magnitude << 12), sign))
                self.passed("cast_boundary")

        for high in ((1 << 61)-2049, (1 << 61)-2048, (1 << 61)-1):
            for sign in (0, 1):
                self.begin("round_add_carry", f"high={high},sign={sign}")
                coefficient, bad, magnitude, pre_round = self.scalar_oracle(1 << 63, (0, high), sign)
                self.equal("constructed pre-round high", pre_round, high * 8)
                self.equal("checked output and flag", self.scalar(1 << 63, (0, high), sign),
                           (coefficient, bad))
                self.equal("magnitude exceeds signed32", magnitude > INT32_MAX, True)
                if high >= (1 << 61)-2048:
                    self.equal("addition really carries", pre_round + 16384 >= MOD64, True)
                    self.equal("legacy wrapped coefficient is zero", coefficient, 0)
                    self.equal("carry cannot be lost", bad, MASK64)
                else:
                    self.equal("immediate pre-carry neighbor", pre_round + 16384 < MOD64, True)
                self.passed("round_add_carry")

    def norm_boundaries(self):
        cases = [
            ("empty", [], []), ("zero", [0], [0]),
            ("negative_one", [-1], []), ("positive_max", [INT32_MAX], []),
            ("one_min_no_false_product_overflow", [INT32_MIN], []),
            ("one_min_second_array", [], [INT32_MIN]),
            ("three_min_fit", [INT32_MIN]*3, []),
            ("four_min_exact_wrap", [INT32_MIN]*4, []),
            ("multiple_wraps_then_zero", [INT32_MIN]*16+[0], []),
            ("cross_array_carry", [INT32_MIN]*3, [INT32_MIN]),
            ("cross_array_sticky", [INT32_MIN]*4, [0, 0]),
            ("wrap_in_second_array_then_zero", [0], [INT32_MIN]*8+[0]),
            ("full_arrays_multiple_wraps", [INT32_MIN]*2048, [INT32_MIN]*2048),
        ]
        for name, a, b in cases:
            self.begin("norm_boundary", name)
            total = integer_norm(a, b)
            self.equal("unbounded integer norm oracle", self.norm(a, b),
                       (total & MASK64, MASK64 if total >= MOD64 else 0))
            if name == "one_min_no_false_product_overflow":
                self.equal("INT32_MIN square fits", total, 1 << 62)
            if name == "four_min_exact_wrap":
                self.equal("four INT32_MIN squares", total, MOD64)
            self.passed("norm_boundary")

    def scale_sticky(self):
        for name, values, left in (
            ("bad_left_then_zero_right", [1 << 63, 0, 0, 0], 2),
            ("bad_right_then_zero", [0, 0, 1 << 63, 0], 2),
            ("only_right", [1 << 63, 0], 0),
            ("only_left", [1 << 63, 0], 2),
        ):
            for sign in (0, 1):
                self.begin("scale_sticky", f"{name},sign={sign}")
                bits = [sign] * len(values)
                scale = (0, 1 << 43)
                a, b, bad = self.scaled(values, bits, scale, left)
                expected = [self.legacy.fixpoint_mul_rnd13_jazz(x, (U64 * 2)(*scale), sign)
                            for x in values]
                self.equal("all coefficient words preserved", a+b, expected)
                self.equal("sticky cast flag", bad, MASK64)
                self.passed("scale_sticky")

    def combined_boundaries(self):
        cases = [
            ("empty", [], [], (0, 0), 0, 0),
            ("safe_zero", [0]*4, [0, 1, 0, 1], (0, 1 << 63), 2, 0),
            ("bound_equality", [1 << 63]*2, [0, 1], (0, 1 << 12), 1, 2),
            ("bound_below", [1 << 63]*2, [0, 1], (0, 1 << 12), 1, 1),
            ("large_safe_bound_equality", [1 << 63]*3, [0, 1, 0],
             (0, INT32_MAX << 12), 1, 3*INT32_MAX**2),
            ("large_safe_bound_below", [1 << 63]*3, [0, 1, 0],
             (0, INT32_MAX << 12), 1, 3*INT32_MAX**2-1),
            ("positive_cast_only", [1 << 63], [0], (0, 1 << 43), 1, MASK64),
            ("negative_cast_only", [1 << 63], [1], (0, 1 << 43), 0, MASK64),
            ("round_carry_only", [1 << 63, 0], [0, 1], (0, (1 << 61)-1), 1, 0),
            ("norm_only_16", [1 << 63]*16, [i % 2 for i in range(16)], (0, 1 << 42), 8, 0),
        ]
        for name, values, bits, scale, left, bound in cases:
            self.begin("combined_boundary", name)
            old = self.combined(self.legacy, values, bits, scale, left, bound, False)
            new = self.combined(self.checked, values, bits, scale, left, bound, True)
            a, b, bad = self.scaled(values, bits, scale, left)
            total = integer_norm(a, b)
            self.equal("legacy/new output coefficients", new[:2], old[:2])
            self.equal("scale/combined output coefficients", new[:2], (a, b))
            self.equal("norm flag independent of cast", self.norm(a, b),
                       (total & MASK64, MASK64 if total >= MOD64 else 0))
            self.equal("legacy modular acceptance", old[2], int((total & MASK64) <= bound))
            self.equal("checked acceptance", new[2], int(bad == 0 and total < MOD64 and total <= bound))
            if name == "norm_only_16":
                self.equal("all magnitudes are 2^30", [abs(signed32(x)) for x in a+b], [1 << 30]*16)
                self.equal("cast guard independently passes", bad, 0)
                self.equal("norm exactly 2^64", total, MOD64)
                self.equal("norm-only decision changes", (old[2], new[2]), (1, 0))
            if name in ("positive_cast_only", "negative_cast_only", "round_carry_only"):
                self.equal("norm guard independently passes", total < MOD64, True)
                self.equal("cast-only decision changes", (old[2], new[2]), (1, 0))
            self.passed("combined_boundary")

    def designated_fixtures(self, definitions):
        for mode, fixture in sorted(definitions.FIXTURES.items()):
            self.begin("designated_fixture", f"mode={mode}")
            library_path = BASELINE / f"build/mode{mode}/lib/libhaetae-mode{mode}-jazz.so"
            old_library = definitions.load_jasmin(library_path)
            self.artifacts[f"baseline_mode{mode}_library"] = sha256(library_path)
            hardened_path = production_library(mode)
            hardened_library = definitions.load_jasmin(hardened_path)
            self.artifacts[f"hardened_mode{mode}_library"] = sha256(hardened_path)
            count, left, multiplier, bound, cube0, cube1, three0, three1 = fixture["constants"]
            candidate = (U8 * 26).from_buffer_copy(bytes.fromhex(fixture["candidate"]))
            sample, square, accepted = (U64 * 1)(), (U64 * 2)(), (U32 * 1)()
            old_library.sample_gauss_sigma76_jazz(sample, square, accepted, candidate)
            self.equal("candidate accepted", accepted[0], 1)
            self.equal("candidate sample", sample[0], fixture["sample"])
            self.equal("candidate raw square", tuple(square), fixture["square"])
            events = count + 2
            low_sum = events * square[0]
            high_sum = events * square[1] + (low_sum >> 48)
            self.equal("raw accumulator fits", max(low_sum, high_sum) < MOD64, True)
            half = (U64 * 2)(low_sum & MASK48, high_sum)
            old_library.fixpoint_half_round_jazz(half)
            self.equal("rounded half", tuple(half), fixture["half"])
            inverse, scale = (U64 * 2)(), (U64 * 2)()
            old_library.fixpoint_newton_invsqrt_jazz(
                inverse, half, (U64 * 2)(cube0, cube1), (U64 * 2)(three0, three1))
            old_library.fixpoint_mul_high_jazz(scale, inverse, multiplier)
            self.equal("actual inverse", tuple(inverse), fixture["inverse"])
            self.equal("actual scale", tuple(scale), fixture["scale"])
            values, bits = [int(sample[0])]*count, [0]*count
            old = self.combined(old_library, values, bits, tuple(scale), left, bound, False)
            new = self.combined(self.checked, values, bits, tuple(scale), left, bound, True)
            production = self.combined(hardened_library, values, bits, tuple(scale), left, bound,
                                       False, initial_acceptance=0)
            self.equal("legacy accepts and checked rejects", (old[2], new[2]), (1, 0))
            self.equal("all output coefficients identical", new[:2], old[:2])
            self.equal("production export accepts/rejects", (old[2], production[2]), (1, 0))
            self.equal("production output coefficients identical", production[:2], old[:2])
            self.equal("production and isolated helper results", production, new)
            self.equal("fixture coefficient", new[0]+new[1], [fixture["coefficient"] & MASK32]*count)
            total = integer_norm(new[0], new[1])
            self.equal("full integer norm", total, fixture["total"])
            self.equal("fixture quotient/residue", divmod(total, MOD64),
                       (fixture["quotient"], fixture["residue"]))
            norm, overflow = self.norm(new[0], new[1])
            self.equal("checked norm residue and sticky flag", (norm, overflow), (fixture["residue"], MASK64))
            cast_bad = self.scalar(sample[0], tuple(scale), 0)[1]
            self.equal("fixture conversion flag", cast_bad, MASK64)
            self.fixtures.append({"mode": mode, "legacy_accepted": old[2], "checked_accepted": new[2],
                                  "production_accepted": production[2],
                                  "integer_norm": total, "residue": norm, "bound": bound,
                                  "cast_bad": cast_bad, "norm_overflow": overflow})
            self.passed("designated_fixture")

    def random_compatibility(self):
        rng = random.Random(SEED)
        for index in range(128):
            self.begin("random_scalar", str(index))
            x = rng.getrandbits(64)
            scale = (rng.getrandbits(64 if index % 2 else 48), rng.getrandbits(64))
            sign = rng.randrange(2)
            coefficient, bad, _, _ = self.scalar_oracle(x, scale, sign)
            self.equal("word output and mathematical range flag", self.scalar(x, scale, sign), (coefficient, bad))
            self.passed("random_scalar")
        for index in range(64):
            self.begin("random_norm", str(index))
            if index % 2:
                values = [rng.randint(-100000, 100000) for _ in range(rng.randrange(161))]
            else:
                values = [rng.getrandbits(32) for _ in range(rng.randrange(161))]
            left = rng.randrange(len(values)+1)
            a, b = values[:left], values[left:]
            total = integer_norm(a, b)
            self.equal("integer sum and carry mask", self.norm(a, b),
                       (total & MASK64, MASK64 if total >= MOD64 else 0))
            self.passed("random_norm")
        for index in range(64):
            self.begin("random_safe_compatibility", str(index))
            values = [rng.getrandbits(64) for _ in range(rng.randrange(1, 41))]
            bits = [rng.randrange(2) for _ in values]
            left = (0 if index % 3 == 0 else len(values) if index % 3 == 1 else rng.randrange(len(values)+1))
            scale = (rng.getrandbits(48), 1 << 40)
            a, b, bad = self.scaled(values, bits, scale, left)
            total = integer_norm(a, b)
            self.equal("generated cast domain", bad, 0)
            self.equal("generated norm domain", total < MOD64, True)
            bound = max(0, total + (index % 3)-1)
            old = self.combined(self.legacy, values, bits, scale, left, bound, False)
            new = self.combined(self.checked, values, bits, scale, left, bound, True)
            self.equal("safe legacy compatibility", new, old)
            self.equal("ordinary integer decision", new[2], int(total <= bound))
            self.passed("random_safe_compatibility")

    def run(self):
        definitions = load_fixtures()
        for mode in definitions.FIXTURES:
            path = BASELINE / f"build/mode{mode}/lib/libhaetae-mode{mode}-jazz.so"
            if not path.is_file():
                raise RuntimeError(f"Build the pinned baseline libraries first: make -C {BASELINE} -j1 libs")
        check_production_build(definitions.FIXTURES)
        path = build_wrapper()
        self.checked = load_checked(path)
        self.legacy = definitions.load_jasmin(BASELINE / "build/mode2/lib/libhaetae-mode2-jazz.so")
        self.artifacts.update({"wrapper_source": sha256(WRAPPER), "test_script": sha256(Path(__file__)),
                               "checked_phase_source": sha256(PROJECT / "jasmin/hyperball_phase.jinc"),
                               "checked_test_library": sha256(path), "baseline_fixture_source": sha256(FIXTURE_PATH)})
        self.scalar_boundaries()
        self.norm_boundaries()
        self.scale_sticky()
        self.combined_boundaries()
        self.designated_fixtures(definitions)
        self.random_compatibility()

    def report(self, result, error=None):
        record = {"suite": "checked-hyperball", "result": result, "seed": SEED,
                  "passed_cases": sum(self.categories.values()), "assertions": self.assertions,
                  "categories": dict(self.categories), "fixtures": self.fixtures,
                  "sha256": self.artifacts,
                  "scope": "Deterministic helper and production-export regressions using prescribed candidates; no SHAKE seed reachability or exploit claim."}
        if error is not None:
            record.update(failed_case=self.current, error_type=type(error).__name__, error=str(error))
        return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write the aggregate PASS/FAIL record to this path")
    args = parser.parse_args()
    suite = Suite()
    try:
        suite.run()
    except Exception as error:
        record = suite.report("FAIL", error)
        status = 1
    else:
        record = suite.report("PASS")
        status = 0
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    return status


if __name__ == "__main__":
    sys.exit(main())
