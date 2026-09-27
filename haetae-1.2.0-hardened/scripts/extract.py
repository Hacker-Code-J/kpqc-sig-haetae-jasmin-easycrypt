#!/usr/bin/env python3
"""Extract actual materialized production sources into a distinct proof namespace."""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile

from materialize import PROJECT, desired_outputs

JOBS = [
    ("HardenedHyperballTarget.ec", "hyperball.jazz", [
        f"polyfixveclk_sample_hyperball_mode{mode}_jazz" for mode in (2, 3, 5)]),
    ("HardenedSignerTarget.ec", "sign.jazz", [
        f"cryptolab_haetae_mode{mode}_{name}" for mode in (2, 3, 5)
        for name in ("signature_internal_desc", "signature_desc", "sign_desc")]),
    ("HardenedPhaseTarget.ec", "hpoly.jazz", ["polyfixveclk_scale_and_check_jazz"]),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for relative, content in desired_outputs().items():
        path = PROJECT / relative
        if not path.is_file() or path.read_bytes() != content:
            raise SystemExit(f"Run scripts/materialize.py first: {relative}")
    generated = PROJECT / "easycrypt/generated"
    with tempfile.TemporaryDirectory(prefix="haetae120-hardened-extraction-") as temp:
        out = Path(temp)
        for name, source, functions in JOBS:
            command = [os.environ.get("JASMIN2EC", "jasmin2ec"), "--array-model=barray",
                       "--arch=x86-64", "--cc=linux", "--output-array=" + str(out),
                       "-o", str(out / name)]
            for function in functions:
                command += ["-f", function]
            command.append(str(PROJECT / "jasmin" / source))
            subprocess.run(command, check=True)
        fresh = {p.name: p.read_bytes() for p in out.glob("*.ec")}
        existing = {p.name: p.read_bytes() for p in generated.glob("*.ec")}
        changed = sorted(name for name in fresh.keys() | existing.keys()
                         if fresh.get(name) != existing.get(name))
        if args.check and changed:
            raise SystemExit("Fresh extraction drift:\n" + "\n".join(changed))
        if args.write:
            generated.mkdir(parents=True, exist_ok=True)
            for name, content in fresh.items():
                if existing.get(name) != content:
                    (generated / name).write_bytes(content)
            for name in existing.keys() - fresh.keys():
                (generated / name).unlink()
        print(f"PASS: {len(fresh)} hardened extracted files {'match fresh compiler output' if args.check else 'written'}")


if __name__ == "__main__":
    main()
