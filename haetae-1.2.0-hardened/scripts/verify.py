#!/usr/bin/env python3
"""Freshly check selected variant proofs and their complete local proof closure."""
import argparse
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
GROUPS = ("all", "gaussian-rate")
spec = importlib.util.spec_from_file_location("baseline_verification", BASELINE / "scripts/verify.py")
baseline_gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(baseline_gate)
strip_baseline_comments = baseline_gate.without_comments


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def proof_text(text):
    # Comments separate tokens in EasyCrypt, including `require(*...*)import`.
    return strip_baseline_comments(text.replace("(*", " (*").replace("*)", "*) "))


def variant_files():
    return sorted([*PROJECT.glob("easycrypt/theories/**/*.ec"),
                   *PROJECT.glob("easycrypt/proofs/**/*.ec")])


def baseline_proof_files():
    return sorted([*BASELINE.glob("theories/**/*.ec"), *BASELINE.glob("proofs/**/*.ec")])


def proof_closure(group="all"):
    if group not in GROUPS:
        raise ValueError(f"Unknown verification group: {group}")
    new = variant_files()
    required = [line.strip() for line in (PROJECT / "easycrypt/proof-targets.txt").read_text().splitlines()
                if line.strip() and not line.lstrip().startswith("#")]
    if len(required) != len(set(required)):
        raise ValueError("Duplicate proof target manifest entry")
    if set(required) != {str(p.relative_to(PROJECT)) for p in new}:
        raise ValueError("The target manifest must cover every variant theory and proof")
    old = baseline_proof_files()
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
        content = proof_text(path.read_text())
        for imported in re.findall(
                r"(?m)(?:^|(?<=\.))\s*require\s+(?:import\s+|export\s+)?([^.]*)\.", content):
            for name in imported.split():
                if name in names:
                    visit(names[name])
        visiting.remove(path)
        visited.add(path)
        ordered.append(path)

    roots = new if group == "all" else [
        path for path in new if path.stem.startswith(("GaussianAcceptance", "GaussianAttempt"))]
    if not roots:
        raise ValueError(f"No verification roots for group {group}")
    for path in roots:
        visit(path)
    # Reuse the existing escape/axiom/opaque/pragma/debug checks. This proof
    # closure permits no project axioms, including the separate NTT parameters.
    # Unselected variant files must pass the same lexical checks.
    previous_project = baseline_gate.PROJECT
    previous_comments = baseline_gate.without_comments
    baseline_gate.PROJECT = ROOT
    baseline_gate.without_comments = proof_text
    try:
        baseline_gate.check_proofs(sorted(set(new) | set(ordered)))
    finally:
        baseline_gate.PROJECT = previous_project
        baseline_gate.without_comments = previous_comments
    return roots, ordered


def control_files():
    return [PROJECT / "scripts/verify.py", PROJECT / "scripts/verify-one.sh",
            PROJECT / "scripts/materialize.py", PROJECT / "scripts/extract.py",
            PROJECT / "baseline-lock.json", PROJECT / "easycrypt/proof-targets.txt",
            BASELINE / "scripts/verify.py"]


def source_files():
    # Generated models stay provenance inputs, not standalone proof targets.
    # Snapshot unselected proofs too: their inventory and guards were checked.
    paths = [*variant_files(), *baseline_proof_files(), *control_files(),
             *BASELINE.glob("generated/**/*.ec"), *PROJECT.glob("easycrypt/generated/**/*.ec"),
             *PROJECT.glob("overlay/*.jinc")]
    for directory in ("jasmin", "include"):
        paths.extend(path for path in (PROJECT / directory).rglob("*") if path.is_file())
    return sorted(set(paths))


def check_hashes(expected, paths):
    for path in paths:
        relative = str(path.relative_to(ROOT))
        if relative not in expected or digest(path) != expected[relative]:
            raise ValueError(f"Source changed during verification: {relative}")


def check_source_snapshot(expected):
    paths = source_files()
    if {str(path.relative_to(ROOT)) for path in paths} != set(expected):
        raise ValueError("Source inventory changed during verification")
    check_hashes(expected, paths)


def check_arrays():
    hashes = {}
    for path in sorted([*BASELINE.glob("generated/**/*.ec"), *PROJECT.glob("easycrypt/generated/**/*.ec")]):
        if re.fullmatch(r"[BW]?Array\d+", path.stem):
            value = digest(path)
            if path.name in hashes and hashes[path.name] != value:
                raise ValueError(f"Array namespace depends on search order: {path.name}")
            hashes[path.name] = value


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--group", choices=GROUPS, default="all")
    args = parser.parse_args(argv)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    logs = PROJECT / "logs" / f"{stamp}-{args.group}"
    logs.mkdir(parents=True)
    report = {"result": "RUNNING", "group": args.group, "phase": "inventory", "checked_at": stamp,
              "scope": "listed component theorems; every selected local proof dependency is a fresh main",
              "complete_api_correctness": False, "retry_termination": False,
              "retry_termination_scope": "Hyperball rejection/retry loop",
              "hyperball_retry_termination": False,
              "gaussian_candidate_retry_model": "explicit iid candidates/bytes; distinct from Hyperball retries",
              "concrete_shake_randomness": False,
              "generated_verification": "fresh extraction, hashes, and array namespaces; imported by proof mains",
              "cache": "-no-eco", "proof_mode": "Proofs:check", "targets": []}

    def save():
        data = json.dumps(report, indent=2) + "\n"
        destinations = [logs / "summary.json", PROJECT / "logs" / f"latest-{args.group}.json"]
        if args.group == "all":
            destinations.append(PROJECT / "logs/latest.json")
        for destination in destinations:
            pending = destination.with_name(f".{destination.name}.{stamp}.tmp")
            pending.write_text(data)
            pending.replace(destination)

    save()
    try:
        sources = {str(path.relative_to(ROOT)): digest(path) for path in source_files()}
        report["source_sha256"] = sources
        report["control_sha256"] = {str(path.relative_to(ROOT)): sources[str(path.relative_to(ROOT))]
                                    for path in control_files()}
        lock, _ = read_baseline()
        report["baseline_commit"] = lock["commit"]
        report["preserved_files"] = len(lock["files"])
        new, targets = proof_closure(args.group)
        report["variant_inventory"] = [str(path.relative_to(ROOT)) for path in variant_files()]
        report["selected_roots"] = [str(path.relative_to(ROOT)) for path in new]
        report["new_targets"] = report["selected_roots"]
        report["dependency_targets"] = [str(path.relative_to(ROOT)) for path in targets if path not in new]
        report["phase"] = "provenance"
        save()
        subprocess.run([sys.executable, "scripts/materialize.py", "--check"], cwd=PROJECT, check=True)
        subprocess.run([sys.executable, "scripts/extract.py", "--check"], cwd=PROJECT, check=True)
        check_arrays()
        check_source_snapshot(sources)
        report["phase"] = "proofs"
        save()
        for path in targets:
            relative = str(path.relative_to(ROOT))
            check_hashes(sources, [path, *control_files()])
            log = logs / (relative.replace("/", "__") + ".log")
            started = time.monotonic()
            print("CHECK", relative, flush=True)
            with log.open("w") as output:
                completed = subprocess.run(["bash", "scripts/verify-one.sh", str(path)], cwd=PROJECT,
                                           stdout=output, stderr=subprocess.STDOUT)
            record = {"target": relative, "sha256": sources[relative], "exit_code": completed.returncode,
                      "seconds": round(time.monotonic() - started, 3), "log": str(log.relative_to(PROJECT))}
            report["targets"].append(record)
            save()
            if completed.returncode:
                print("\n".join(log.read_text(errors="replace").replace("\r", "\n").splitlines()[-25:]))
                raise ValueError(f"Proof failed: {relative}")
            check_hashes(sources, [path, *control_files()])
            print("PASS", relative, flush=True)
        report["phase"] = "snapshot"
        if proof_closure(args.group) != (new, targets):
            raise ValueError("Proof dependency closure changed during verification")
        check_source_snapshot(sources)
        read_baseline()
        report.update(result="PASS", phase="complete")
    except (OSError, ValueError, SystemExit, subprocess.CalledProcessError) as error:
        report.update(result="FAIL", error=str(error))
    save()
    print(f"RESULT {report['result']}: {len(report['targets'])} fresh main targets (group={args.group})", flush=True)
    return 0 if report["result"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
