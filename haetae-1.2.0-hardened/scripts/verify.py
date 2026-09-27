#!/usr/bin/env python3
"""Freshly check every variant proof and its original local proof dependencies."""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import time

from materialize import PROJECT, ROOT, read_baseline

BASELINE = ROOT / "haetae-1.2.0-easycrypt"
spec = importlib.util.spec_from_file_location("baseline_verification", BASELINE / "scripts/verify.py")
baseline_gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(baseline_gate)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def proof_closure():
    new = sorted([*PROJECT.glob("easycrypt/theories/*.ec"), *PROJECT.glob("easycrypt/proofs/*.ec")])
    required = {line.strip() for line in (PROJECT / "easycrypt/proof-targets.txt").read_text().splitlines()
                if line.strip() and not line.startswith("#")}
    if required != {str(p.relative_to(PROJECT)) for p in new}:
        raise ValueError("The target manifest must cover every variant theory and proof")
    old = sorted([*BASELINE.glob("theories/**/*.ec"), *BASELINE.glob("proofs/**/*.ec")])
    names = {p.stem: p for p in old + new}
    if len(names) != len(old + new):
        raise ValueError("Ambiguous proof namespace")
    visiting, visited, ordered = set(), set(), []

    def visit(path):
        if path in visited:
            return
        if path in visiting:
            raise ValueError(f"Cyclic proof import: {path}")
        visiting.add(path)
        content = baseline_gate.without_comments(path.read_text())
        for imported in re.findall(r"(?m)^require\s+(?:import\s+|export\s+)?([^.]*)\.", content):
            for name in imported.split():
                if name in names:
                    visit(names[name])
        visiting.remove(path)
        visited.add(path)
        ordered.append(path)

    for path in new:
        visit(path)
    # Reuse the existing escape/axiom/opaque/pragma/debug checks. This proof
    # closure permits no project axioms, including the separate NTT parameters.
    baseline_gate.PROJECT = ROOT
    baseline_gate.check_proofs(ordered)
    return new, ordered


def check_arrays():
    hashes = {}
    for path in sorted([*BASELINE.glob("generated/**/*.ec"), *PROJECT.glob("easycrypt/generated/*.ec")]):
        if re.fullmatch(r"[BW]?Array\d+", path.stem):
            value = digest(path)
            if path.name in hashes and hashes[path.name] != value:
                raise ValueError(f"Array namespace depends on search order: {path.name}")
            hashes[path.name] = value


def main():
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    logs = PROJECT / "logs" / stamp
    logs.mkdir(parents=True)
    report = {"result": "RUNNING", "checked_at": stamp,
              "scope": "checked arithmetic and conditional-on-return Hyperball norm safety",
              "complete_api_correctness": False, "retry_termination": False,
              "cache": "-no-eco", "proof_mode": "Proofs:check", "targets": []}

    def save():
        data = json.dumps(report, indent=2) + "\n"
        (logs / "summary.json").write_text(data)
        (PROJECT / "logs/latest.json").write_text(data)

    save()
    try:
        lock, _ = read_baseline()
        report["baseline_commit"] = lock["commit"]
        report["preserved_files"] = len(lock["files"])
        subprocess.run([sys.executable, "scripts/materialize.py", "--check"], cwd=PROJECT, check=True)
        subprocess.run([sys.executable, "scripts/extract.py", "--check"], cwd=PROJECT, check=True)
        check_arrays()
        new, targets = proof_closure()
        report["new_targets"] = [str(p.relative_to(ROOT)) for p in new]
        report["dependency_targets"] = [str(p.relative_to(ROOT)) for p in targets if p not in new]
        sources = {str(p.relative_to(ROOT)): digest(p) for p in targets}
        sources.update({str(p.relative_to(ROOT)): digest(p) for p in PROJECT.glob("easycrypt/generated/*.ec")})
        sources.update({str(p.relative_to(ROOT)): digest(p) for p in PROJECT.glob("overlay/*.jinc")})
        report["source_sha256"] = sources
        save()
        for path in targets:
            relative = str(path.relative_to(ROOT))
            log = logs / (relative.replace("/", "__") + ".log")
            started = time.monotonic()
            print("CHECK", relative, flush=True)
            with log.open("w") as output:
                completed = subprocess.run(["bash", "scripts/verify-one.sh", str(path)], cwd=PROJECT,
                                           stdout=output, stderr=subprocess.STDOUT)
            record = {"target": relative, "sha256": digest(path), "exit_code": completed.returncode,
                      "seconds": round(time.monotonic() - started, 3), "log": str(log.relative_to(PROJECT))}
            report["targets"].append(record)
            save()
            if completed.returncode:
                print("\n".join(log.read_text(errors="replace").replace("\r", "\n").splitlines()[-25:]))
                raise ValueError(f"Proof failed: {relative}")
            print("PASS", relative, flush=True)
        for name, expected in sources.items():
            if digest(ROOT / name) != expected:
                raise ValueError(f"Source changed during verification: {name}")
        read_baseline()
        report["result"] = "PASS"
    except (OSError, ValueError, SystemExit, subprocess.CalledProcessError) as error:
        report.update(result="FAIL", error=str(error))
    save()
    print(f"RESULT {report['result']}: {len(report['targets'])} fresh main targets", flush=True)
    return 0 if report["result"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
