#!/usr/bin/env python3
"""Regenerate actual Jasmin extractions, or compare a fresh extraction to disk."""
import argparse
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

PROJECT = Path(__file__).resolve().parents[1]
ROOT = PROJECT.parent
SOURCE = ROOT / "haetae-jasmin" / "jasmin"

JOBS = [
    ("ntt-composition/NTTProductTarget.ec", "signing_challenge_product.jazz", ["sign_compute_cs2_jazz"]),
    ("ntt-composition/NTTMatrixTarget.ec", "keypair_matrix.jazz", ["keypair_m23_matrix_jazz", "keypair_m5_matrix_jazz", "keypair_copy_ntt_jazz"]),
    ("sampler/SamplerTarget.ec", "hpoly.jazz", [
        "sample_gauss83_jazz", "smulh48_jazz", "approx_exp_jazz",
        "sample_gauss_sigma76_jazz", "sample_gauss_jazz",
    ]),
    ("ntt/HpolyTarget.ec", "hpoly.jazz", ["poly_ntt_jazz", "poly_invntt_jazz"]),
    ("api/ApiBoundaryTarget.ec", "sign.jazz", [
        "_api_copy_addr_to_addr_backward", "_api_zero_raw_len64", "_api_prepare_pre_raw",
    ]),
    ("api/ApiTarget.ec", "sign.jazz", [
        f"cryptolab_haetae_mode{mode}_{name}"
        for mode in (2, 3, 5)
        for name in ("signature_internal_desc", "signature_desc", "sign_desc")
    ]),
    ("api/KeygenTarget.ec", "keypair.jazz", [
        f"cryptolab_haetae_mode{mode}_{name}"
        for mode in (2, 3, 5) for name in ("keypair_internal", "keypair")
    ]),
    ("api/VerifyTarget.ec", "verify.jazz", [
        f"cryptolab_haetae_mode{mode}_{name}"
        for mode in (2, 3, 5)
        for name in ("verify_internal_desc", "verify_desc", "open_desc")
    ]),
]

# These array theories are imported by the existing SHAKE/NTT proofs. Jasmin
# 2026.09 emits only the array model selected for program extraction; obtain
# the legacy proof support from a separate warray extraction of actual inputs.
# Its program is discarded: every verified program remains a barray extraction.
SUPPORT_JOBS = [
    ("hpoly.jazz", "poly_ntt_jazz", ("Array256.ec", "WArray1024.ec")),
    ("sign.jazz", "cryptolab_haetae_mode2_signature_internal_desc",
     ("Array5.ec", "Array24.ec", "Array25.ec")),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    compiler = os.environ.get("JASMIN2EC", "jasmin2ec")
    with tempfile.TemporaryDirectory(prefix="haetae120-extraction-") as tmp:
        out = Path(tmp)
        for target, source, functions in JOBS:
            destination = out / target
            destination.parent.mkdir(parents=True, exist_ok=True)
            command = [compiler, "--array-model=barray", "--arch=x86-64", "--cc=linux",
                       "--output-array=" + str(destination.parent), "-o", str(destination)]
            for function in functions:
                command.extend(["-f", function])
            command.append(str(SOURCE / source))
            subprocess.run(command, check=True)
        support = out / "support"
        support.mkdir()
        with tempfile.TemporaryDirectory(prefix="haetae120-proof-arrays-") as array_tmp:
            for index, (source, function, required) in enumerate(SUPPORT_JOBS):
                arrays = Path(array_tmp) / str(index)
                arrays.mkdir()
                subprocess.run([
                    compiler, "--array-model=warray", "--arch=x86-64", "--cc=linux",
                    "--output-array=" + str(arrays), "-o", str(arrays / "Target.ec"),
                    "-f", function, str(SOURCE / source),
                ], check=True)
                for filename in required:
                    shutil.copyfile(arrays / filename, support / filename)
        fresh = {p.relative_to(out): p for p in out.rglob("*.ec")}
        existing = {p.relative_to(PROJECT / "generated"): p
                    for p in (PROJECT / "generated").rglob("*.ec")}
        if args.check:
            changed = sorted(str(p) for p in fresh.keys() | existing.keys()
                             if p not in fresh or p not in existing
                             or fresh[p].read_bytes() != existing[p].read_bytes())
            if changed:
                raise SystemExit("Extraction drift:\n" + "\n".join(changed))
            print(f"PASS: {len(fresh)} generated files match fresh Jasmin extraction")
        else:
            for relative, path in fresh.items():
                target = PROJECT / "generated" / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                if not target.exists() or path.read_bytes() != target.read_bytes():
                    shutil.copyfile(path, target)
            for stale in existing.keys() - fresh.keys():
                existing[stale].unlink()
            print(f"Wrote {len(fresh)} generated files from current Jasmin sources")


if __name__ == "__main__":
    main()
