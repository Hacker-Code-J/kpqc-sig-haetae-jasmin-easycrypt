#!/usr/bin/env python3
"""Extract actual materialized production sources into a distinct proof namespace."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
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


def check_manifest(expected, actual):
    # A compiler rebuilt from the same release need not have identical binary
    # bytes. Its release, extraction options, jobs, sources, and fresh output
    # must still match the recorded artifact exactly.
    for record in (expected, actual):
        if not re.fullmatch(r"[0-9a-f]{64}", record.get("compiler_sha256", "")):
            raise SystemExit("Extraction provenance drift: missing compiler identity")
    recorded = {key: value for key, value in expected.items() if key != "compiler_sha256"}
    replayed = {key: value for key, value in actual.items() if key != "compiler_sha256"}
    if recorded != replayed:
        raise SystemExit("Extraction provenance drift: extraction-manifest.json")


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
    compiler = os.environ.get("JASMIN2EC", "jasmin2ec")
    executable = shutil.which(compiler)
    if executable is None:
        raise SystemExit(f"Missing extraction compiler: {compiler}")
    with tempfile.TemporaryDirectory(prefix="haetae120-hardened-extraction-") as temp:
        out = Path(temp)
        for name, source, functions in JOBS:
            command = [compiler, "--array-model=barray",
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
        manifest_path = PROJECT / "extraction-manifest.json"
        sha256 = lambda data: hashlib.sha256(data).hexdigest()
        manifest = {
            "compiler_version": subprocess.check_output([compiler, "--version"], text=True).strip(),
            "compiler_sha256": sha256(Path(executable).read_bytes()),
            "options": ["--array-model=barray", "--arch=x86-64", "--cc=linux"],
            "jobs": [{"output": name, "source": "jasmin/" + source, "functions": functions}
                     for name, source, functions in JOBS],
            "source_sha256": {str(p.relative_to(PROJECT)): sha256(p.read_bytes())
                              for p in sorted((PROJECT / "jasmin").rglob("*")) if p.is_file()},
            "generated_sha256": {name: sha256(content) for name, content in sorted(fresh.items())},
        }
        manifest_bytes = (json.dumps(manifest, indent=2) + "\n").encode()
        if args.check and changed:
            raise SystemExit("Fresh extraction drift:\n" + "\n".join(changed))
        if args.check:
            if not manifest_path.is_file():
                raise SystemExit("Extraction provenance drift: missing extraction-manifest.json")
            check_manifest(json.loads(manifest_path.read_text()), manifest)
        if args.write:
            generated.mkdir(parents=True, exist_ok=True)
            for name, content in fresh.items():
                if existing.get(name) != content:
                    (generated / name).write_bytes(content)
            for name in existing.keys() - fresh.keys():
                (generated / name).unlink()
            manifest_path.write_bytes(manifest_bytes)
        print("EXTRACTION_COMPILER " + json.dumps({
            "version": manifest["compiler_version"], "sha256": manifest["compiler_sha256"]}))
        print(f"PASS: {len(fresh)} hardened extracted files {'match fresh compiler output' if args.check else 'written'}")


if __name__ == "__main__":
    main()
