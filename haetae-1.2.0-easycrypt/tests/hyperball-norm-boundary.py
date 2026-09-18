#!/usr/bin/env python3
"""Replay fixed abstract candidate streams; no SHAKE seed or exploit is claimed."""
import ctypes as C
import hashlib
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

PROJECT = Path(__file__).resolve().parents[1]
ROOT = PROJECT.parent
REFERENCE = ROOT / "HAETAE-1.2.0/reference_implementation"
JASMIN = ROOT / "haetae-1.2.0-jasmin"
MODULUS = 1 << 64
MASK48 = (1 << 48) - 1
U64, U32, U8 = C.c_uint64, C.c_uint32, C.c_uint8
P64, P32, P8 = C.POINTER(U64), C.POINTER(U32), C.POINTER(U8)


class Result(C.Structure):
    _fields_ = [
        ("accepted", U64), ("sample", U64),
        *[(name, U64 * 2) for name in ("square", "half", "first", "inverse", "scale")],
        ("coefficient", U64), ("norm", U64),
    ]


# Constants: stored count, left count, scale multiplier, norm bound,
#            starting cube (low, high), starting three-halves (low, high).
# These fixtures prescribe one accepted candidate for every event, with all
# sign bits zero. Two accepted values contribute squares but are not stored.
FIXTURES = {
    2: {
        "constants": (1536, 1024, 2643021496320, 6505809026482176,
                      130843895063578, 4450, 115690877850491, 10267222),
        "candidate": "f02b9beab2fa80e32cff07010000000000fa0c64c17e9d051d68",
        "sample": 4136588167694172516,
        "square": (140509563513772, 3455611969),
        "half": (246938261909420, 2657365604544),
        "first": (331270931819935, 18446744073675761646),
        "inverse": (101666530011624, 17352118948918032670),
        "scale": (265747297086624, 14053931103413738628),
        "coefficient": -1704795102,
        "total": 4464117257937700460544,
        "quotient": 242,
        "residue": 5192099988969472,
    },
    3: {
        "constants": (2304, 1536, 4916390789120, 22510896139993088,
                      28764298784360, 2424, 135042716239155, 8384969),
        "candidate": "85666c58d6ffffffffff07010000000000e682480d5e84d3bc6c",
        "sample": 8893690980794764617,
        "square": (262880264445775, 15973661233),
        "half": (233869965312719, 18417631402725),
        "first": (241583609198600, 18446744073551616452),
        "inverse": (101443927918593, 6515027660407619326),
        "scale": (42658744122560, 9079590807424815727),
        "coefficient": -334802028,
        "total": 258260884883511054336,
        "quotient": 14,
        "residue": 6467851577331712,
    },
    5: {
        "constants": (2816, 1792, 5997831421952, 33503371683954688,
                      123213818923277, 1794, 96105673977137, 7585088),
        "candidate": "0137e5ab1a741e4c3bf00701000000000030437515a2b15216a0",
        "sample": 3143537084327925109,
        "square": (17372889325272, 1995618747),
        "half": (271553062191832, 2811826814609),
        "first": (333906974325571, 18446744073698340199),
        "inverse": (51879773209874, 14033702225847268899),
        "scale": (182753957924859, 6560330886008659858),
        "coefficient": -632138900,
        "total": 1125272442323279360000,
        "quotient": 61,
        "residue": 21053826996711424,
    },
}


def expect(label, actual, expected):
    # Explicit checks also run when PYTHONOPTIMIZE disables assert statements.
    if actual != expected:
        raise AssertionError(f"{label}: expected {expected!r}, got {actual!r}")


def signed(value, bits):
    return value if value < (1 << (bits - 1)) else value - (1 << bits)


def load_jasmin(path):
    # Only deterministic arithmetic exports are called. Lazy loading leaves the
    # application-provided randombytes symbol unused, as it is in these probes.
    lib = C.CDLL(str(path), mode=os.RTLD_LOCAL | os.RTLD_LAZY)
    signatures = {
        "sample_gauss_sigma76_jazz": ([P64, P64, P32, P8], None),
        "fixpoint_half_round_jazz": ([P64], P64),
        "fixpoint_mul_jazz": ([P64, P64, P64], P64),
        "fixpoint_newton_invsqrt_jazz": ([P64, P64, P64, P64], P64),
        "fixpoint_mul_high_jazz": ([P64, P64, U64], P64),
        "fixpoint_mul_rnd13_jazz": ([U64, P64, U8], U32),
        "polyfixveclk_sqnorm2_jazz": ([P32, U64, P32, U64], U64),
        "polyfixveclk_scale_and_check_jazz": ([P32, P32, P64, P64, P8, P64], None),
    }
    for name, (arguments, result) in signatures.items():
        function = getattr(lib, name)
        function.argtypes = arguments
        function.restype = result
    return lib


def replay(mode, fixture, temporary):
    probe_path = temporary / f"reference-mode{mode}.so"
    compiler = shlex.split(os.environ.get("CC", "cc"))
    subprocess.run([
        *compiler, "-O2", "-std=c11", "-Wall", "-Wextra", "-shared", "-fPIC",
        f"-DHAETAE_CONFIG_MODE=HAETAE_MODE{mode}", f"-I{REFERENCE / 'include'}",
        str(PROJECT / "tests/hyperball-norm-boundary.c"),
        str(REFERENCE / "src/fips202.c"), str(REFERENCE / "src/symmetric-shake.c"),
        "-o", str(probe_path),
    ], check=True)
    reference = C.CDLL(str(probe_path))
    reference.hyperball_boundary_constants.argtypes = [P64]
    reference.hyperball_boundary_constants.restype = None
    reference.hyperball_boundary_probe.argtypes = [P8, C.POINTER(Result)]
    reference.hyperball_boundary_probe.restype = None
    constants = (U64 * 8)()
    reference.hyperball_boundary_constants(constants)
    expect("reference mode constants", tuple(constants), fixture["constants"])
    count, left, multiplier, bound, cube0, cube1, three0, three1 = constants

    candidate = (U8 * 26).from_buffer_copy(bytes.fromhex(fixture["candidate"]))
    result = Result()
    reference.hyperball_boundary_probe(candidate, C.byref(result))
    expect("reference candidate acceptance", result.accepted, 1)
    expect("reference sample", result.sample, fixture["sample"])
    for field in ("square", "half", "first", "inverse", "scale"):
        expect(f"reference {field}", tuple(getattr(result, field)), fixture[field])
    coefficient_word = fixture["coefficient"] % (1 << 32)
    expect("reference coefficient", result.coefficient, coefficient_word)
    expect("reference norm residue", result.norm, fixture["residue"])
    first_integer = result.first[0] + (signed(result.first[1], 64) << 48)
    expect("first Newton iterate is negative", first_integer < 0, True)

    library_path = JASMIN / f"build/mode{mode}/lib/libhaetae-mode{mode}-jazz.so"
    jazz = load_jasmin(library_path)
    sample, square, accepted = (U64 * 1)(), (U64 * 2)(), (U32 * 1)()
    jazz.sample_gauss_sigma76_jazz(sample, square, accepted, candidate)
    expect("Jasmin candidate acceptance", accepted[0], result.accepted)
    expect("Jasmin sample", sample[0], result.sample)
    expect("Jasmin square", tuple(square), tuple(result.square))

    events = count + 2
    expect("Gaussian low sum fits", events * square[0] < MODULUS, True)
    high_sum = events * square[1] + (events * square[0] >> 48)
    expect("Gaussian high sum fits", high_sum < MODULUS, True)
    half = (U64 * 2)((events * square[0]) & MASK48, high_sum)
    jazz.fixpoint_half_round_jazz(half)
    expect("Jasmin rounded half", tuple(half), tuple(result.half))

    # Reconstruct the first subtraction's exact limbs from exposed Jasmin mul.
    # __sub_regs leaves its low limb unnormalized; retain that behavior here.
    tmp, cube = (U64 * 2)(), (U64 * 2)(cube0, cube1)
    jazz.fixpoint_mul_jazz(tmp, half, cube)
    neglo = (tmp[0] ^ MASK48) + 1
    neghi = ((tmp[1] ^ (MODULUS - 1)) + (neglo >> 48)) % MODULUS
    first = ((three0 + (neglo & MASK48)) % MODULUS, (three1 + neghi) % MODULUS)
    expect("Jasmin first iterate", first, tuple(result.first))

    inverse, scale = (U64 * 2)(), (U64 * 2)()
    jazz.fixpoint_newton_invsqrt_jazz(inverse, half, cube, (U64 * 2)(three0, three1))
    expect("Jasmin inverse", tuple(inverse), tuple(result.inverse))
    jazz.fixpoint_mul_high_jazz(scale, inverse, multiplier)
    expect("Jasmin scale", tuple(scale), tuple(result.scale))
    expect("Jasmin rounded coefficient",
           jazz.fixpoint_mul_rnd13_jazz(sample[0], scale, 0), coefficient_word)

    y1, y2 = (U32 * 2048)(), (U32 * 2048)()
    state = (U64 * 4)(left, count, bound, 999)
    samples = (U64 * 4096)(*([sample[0]] * count))
    signs = (U8 * 512)()
    jazz.polyfixveclk_scale_and_check_jazz(y1, y2, state, samples, signs, scale)
    expect("Jasmin left vector", list(y1[:left]), [coefficient_word] * left)
    expect("Jasmin right vector", list(y2[:count-left]), [coefficient_word] * (count-left))
    expect("Jasmin left tail", list(y1[left:]), [0] * (2048-left))
    expect("Jasmin right tail", list(y2[count-left:]), [0] * (2048-count+left))
    expect("Jasmin word acceptance", state[3], 1)

    # This exported norm helper has a 4096-cell pointer type. Supply full arrays
    # although it reads only the populated mode-specific prefixes.
    a, b = (U32 * 4096)(*y1), (U32 * 4096)(*y2)
    norm = jazz.polyfixveclk_sqnorm2_jazz(a, left, b, count-left)
    expect("Jasmin norm residue", norm, fixture["residue"])
    integer_norm = sum(signed(word, 32) ** 2 for word in y1[:left])
    integer_norm += sum(signed(word, 32) ** 2 for word in y2[:count-left])
    expect("integer norm", integer_norm, fixture["total"])
    expect("repeated coefficient sum", count * fixture["coefficient"] ** 2, integer_norm)
    expect("quotient and residue", divmod(integer_norm, MODULUS),
           (fixture["quotient"], fixture["residue"]))
    expect("modular acceptance despite integer norm exceeding bound",
           0 <= norm <= bound < MODULUS <= integer_norm, True)
    digest = hashlib.sha256(library_path.read_bytes()).hexdigest()
    print(f"PASS mode {mode}: integer={integer_norm}; residue={norm}; bound={bound}")
    print(f"  Jasmin library SHA256: {digest}")


def main():
    # Existing targets preserve the project's compiler options. Serial builds
    # avoid multiplying the memory demand of the full signing translation unit.
    subprocess.run([
        "make", "-s", "-j1", "-C", str(JASMIN),
        *[f"build/mode{mode}/lib/libhaetae-mode{mode}-jazz.so" for mode in FIXTURES],
    ], check=True)
    with tempfile.TemporaryDirectory(prefix="haetae120-hyperball-boundary-") as directory:
        for mode, fixture in FIXTURES.items():
            replay(mode, fixture, Path(directory))
    print("PASS prescribed candidate streams; no SHAKE seed reachability or exploit claim.")


if __name__ == "__main__":
    main()
