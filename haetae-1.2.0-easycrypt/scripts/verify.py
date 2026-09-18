#!/usr/bin/env python3
"""Check provenance and freshly verify each selected local EasyCrypt theory."""
import argparse
import csv
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

PROJECT = Path(__file__).resolve().parents[1]
ROOT = PROJECT.parent
PARAMETER_THEORIES = {"theories/ntt/GFq.ec", "theories/ntt/Montgomery.ec"}
OPAQUE_DEFINITION_THEORIES = PARAMETER_THEORIES | {"theories/ntt/Rq.ec"}


def run(command, **kwargs):
    return subprocess.run(command, cwd=PROJECT, check=True, **kwargs)


def without_comments(text):
    output = []
    depth = 0
    i = 0
    while i < len(text):
        if text[i:i + 2] == "(*":
            depth += 1
            i += 2
        elif text[i:i + 2] == "*)" and depth:
            depth -= 1
            i += 2
        else:
            if not depth:
                output.append(text[i])
            elif text[i] == "\n":
                output.append("\n")
            i += 1
    if depth:
        raise ValueError("Unclosed EasyCrypt comment")
    return "".join(output)


def proof_files():
    files = sorted([*PROJECT.glob("theories/**/*.ec"), *PROJECT.glob("proofs/**/*.ec")])
    names = {p.stem: p for p in files}
    if len(names) != len(files):
        raise ValueError("Ambiguous local theory names")
    ordered, visited, visiting = [], set(), set()

    def visit(path):
        if path in visited:
            return
        if path in visiting:
            raise ValueError(f"Cyclic imports at {path}")
        visiting.add(path)
        content = without_comments(path.read_text())
        for imported in re.findall(r"(?m)^require\s+(?:import\s+|export\s+)?([^.]*)\.", content):
            for name in imported.split():
                if name in names:
                    visit(names[name])
        visiting.remove(path)
        visited.add(path)
        ordered.append(path)

    for path in files:
        visit(path)
    return ordered


def check_proofs(files):
    for path in files:
        relative = str(path.relative_to(PROJECT))
        content = without_comments(path.read_text())
        if re.search(r"\b(admit|admitted|abort|sorry)\b", content):
            raise ValueError(f"Proof escape in {relative}")
        if re.search(r"\baxiom\b", content) and relative not in PARAMETER_THEORIES:
            raise ValueError(f"Unlisted project axiom in {relative}")
        if re.search(r"\baxiomatized\s+by\b", content) and relative not in OPAQUE_DEFINITION_THEORIES:
            raise ValueError(f"Unlisted opaque definition in {relative}")
        if re.search(r"\bpragma\b", content):
            raise ValueError(f"Project proof pragmas are not allowed: {relative}")
        if relative not in PARAMETER_THEORIES:
            for statement in re.split(r"\.(?=\s|$)", content):
                if re.match(r"\s*(?:local\s+)?(?:op|type)\b", statement):
                    declaration = statement.partition("=")[0]
                    if "{" in declaration or re.search(r"\bas\s+\w+\s*$", statement):
                        raise ValueError(f"Constrained declaration can introduce an assumption: {relative}")
        if re.search(r"(?m)^\s*print\s+(goal|all)\b", content):
            raise ValueError(f"Debug command in {relative}")
        if re.search(r"\.omx/|restart-backup|/home/", content):
            raise ValueError(f"External legacy path in {relative}")


def check_provenance():
    subprocess.run(["sha256sum", "--check", "--status", "docs/UPSTREAM-SHA256SUMS"],
                   cwd=ROOT, check=True)
    run(["sha256sum", "--check", "--status", "manifests/jasmin-sources.sha256"])
    run(["sha256sum", "--check", "--status", "manifests/extractions.sha256"])
    with (PROJECT / "manifests/ntt-support-origin.tsv").open() as manifest:
        seen = set()
        for row in csv.DictReader(manifest, delimiter="\t"):
            if row["destination"] in seen:
                raise ValueError("Duplicate NTT provenance entry")
            seen.add(row["destination"])
            path = PROJECT / row["destination"]
            if hashlib.sha256(path.read_bytes()).hexdigest() != row["ported_sha256"]:
                raise ValueError(f"Pinned NTT support drift: {row['destination']}")
        expected = {str(p.relative_to(PROJECT)) for p in PROJECT.glob("theories/ntt/*.ec")}
        expected.add("proofs/NTTCorrectness.ec")
        if seen != expected:
            raise ValueError("NTT provenance manifest does not cover the complete local support")
    with (PROJECT / "manifests/shake-support-origin.tsv").open() as manifest:
        seen = set()
        origins = set()
        for row in csv.DictReader(manifest, delimiter="\t"):
            origin = (row["destination"], row["origin_snapshot_path"])
            if origin in origins:
                raise ValueError("Duplicate SHAKE provenance entry")
            origins.add(origin)
            seen.add(row["destination"])
            path = PROJECT / row["destination"]
            if hashlib.sha256(path.read_bytes()).hexdigest() != row["ported_sha256"]:
                raise ValueError(f"SHAKE support drift: {row['destination']}")
        if seen != {"theories/SHAKEBlockSpec.ec", "proofs/SHAKEBlockCorrectness.ec"}:
            raise ValueError("SHAKE provenance manifest does not cover the local support")
    run([sys.executable, "scripts/extract.py", "--check"])
    with tempfile.TemporaryDirectory(prefix="haetae120-reference-constants-") as tmp:
        fresh = Path(tmp) / "ReferenceConstants.ec"
        run([sys.executable, "scripts/reference-constants.py", "--output", str(fresh)])
        if fresh.read_bytes() != (PROJECT / "theories/ReferenceConstants.ec").read_bytes():
            raise ValueError("Reference constants drift")
    # Identically named generated array theories must not depend on search order.
    arrays = {}
    for path in sorted(PROJECT.glob("generated/**/*.ec")):
        if re.fullmatch(r"[BW]?Array\d+", path.stem):
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            if path.name in arrays and arrays[path.name] != digest:
                raise ValueError(f"Conflicting generated array theory: {path.name}")
            arrays[path.name] = digest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--group", choices=("all", "new", "ntt", "generated"), default="all")
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    log_dir = PROJECT / "logs" / f"{stamp}-{args.group}"
    log_dir.mkdir(parents=True)
    results = []
    report = {"group": args.group, "result": "RUNNING", "phase": "provenance",
              "scope": "listed component theorems; not complete KeyGen/Sign/Verify correctness",
              "complete_api_correctness": False,
              "checked_at": stamp, "cache": "-no-eco", "proof_mode": "Proofs:check",
              "targets": results}

    def save_report():
        text = json.dumps(report, indent=2) + "\n"
        (log_dir / "summary.json").write_text(text)
        latest = PROJECT / "logs" / f"latest-{args.group}.json"
        pending = latest.with_suffix(".tmp")
        pending.write_text(text)
        pending.replace(latest)

    save_report()
    try:
        check_provenance()
        local = proof_files()
        check_proofs(local)
        manifest = PROJECT / "manifests/proof-targets.txt"
        required = [line.strip() for line in manifest.read_text().splitlines()
                    if line.strip() and not line.lstrip().startswith("#")]
        discovered = [str(p.relative_to(PROJECT)) for p in local]
        if len(required) != len(set(required)) or set(required) != set(discovered):
            raise ValueError("Proof target manifest does not match the complete local theory set")
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        report.update(result="FAIL", error=str(error))
        save_report()
        print(f"RESULT FAIL group={args.group} phase=provenance: {error}", file=sys.stderr)
        return 1
    if args.group == "new":
        targets = [p for p in local if "ntt" not in p.parts and p.name != "NTTCorrectness.ec"]
    elif args.group == "ntt":
        targets = [p for p in local if "ntt" in p.parts or p.name == "NTTCorrectness.ec"]
    elif args.group == "generated":
        targets = []
    else:
        targets = local
    if args.group in ("all", "generated"):
        targets = sorted(PROJECT.glob("generated/**/*.ec")) + targets
    if not targets:
        report.update(result="FAIL", error="No verification targets")
        save_report()
        return 1
    report["phase"] = "proofs"
    save_report()
    for path in targets:
        relative = str(path.relative_to(PROJECT))
        log = log_dir / (relative.replace("/", "__") + ".log")
        started = time.monotonic()
        print(f"CHECK {relative}", flush=True)
        with log.open("w") as output:
            result = subprocess.run(["bash", "scripts/verify-one.sh", relative],
                                    cwd=PROJECT, stdout=output, stderr=subprocess.STDOUT)
        record = {"target": relative, "exit_code": result.returncode,
                  "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                  "seconds": round(time.monotonic() - started, 3),
                  "log": str(log.relative_to(PROJECT))}
        results.append(record)
        print(f"{'PASS' if result.returncode == 0 else 'FAIL'} {relative} ({record['seconds']}s)", flush=True)
        if result.returncode:
            print("\n".join(log.read_text(errors="replace").replace("\r", "\n").splitlines()[-30:]))
            break
    success = len(results) == len(targets) and all(r["exit_code"] == 0 for r in results)
    report.update(result="PASS" if success else "FAIL", phase="complete")
    save_report()
    print(f"RESULT {report['result']} group={args.group} checked={len(results)}/{len(targets)} cache=-no-eco")
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
