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

# Keep the historical TSV pins authoritative. Only these reviewed 2026.09
# file bytes may replace their exact historical counterparts; editing a TSV
# or the descriptive migration manifest cannot authorize another port.
REVIEWED_SUPPORT_PORTS = {
    "theories/ntt/Fq.ec": (
        "9a74258fb09e829679562b6a940777ef522232d6400d9acba6c3bcead29216b9",
        "e280e74e4942c3678120aa66b8e7b38bb0ed900cf69e67785a855e9c5a4ef5a3",
    ),
    "theories/ntt/NTT_Fq.ec": (
        "62181de33a8ff2e730f7773f0e8148c0eee6f27c7509dfc1e9e60e6258e6d074",
        "73abcb9f5ff33862c4784853102cddcb5e13a8f4d4d401139fdb0323a258b2de",
    ),
    "theories/ntt/NTTFullSpec.ec": (
        "949f925251d048642a3d4d222b59d7acdf85cf27a0fa6016fabf5df4a5645516",
        "5292e64f614fc2120d756894de44f68dd00fe7ef017dd8b7b77e803c437fc474",
    ),
    "theories/ntt/NTTFullAlgebra.ec": (
        "e5cade55a560aed0112fce32651f1c2c97c1fdf605944fe67034a40234924fdc",
        "a11ae0c7de30934f6cb810e042a45ea1d55d3981033402797c83114b85ab5bd8",
    ),
    "proofs/SHAKEBlockCorrectness.ec": (
        "d8a0dbd8d2546670ad57cdcb8a392f81f16ec1c2025d8cb234f663482cb96cbd",
        "61a7b169987983ca6d355cb75f9d379843dee0d39a0d53824d0ee39b296518a4",
    ),
}


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


def check_target_manifests(files):
    discovered = {str(path.relative_to(PROJECT)) for path in files}

    def check_manifest(name, expected):
        manifest = PROJECT / "manifests" / name
        required = [line.strip() for line in manifest.read_text().splitlines()
                    if line.strip() and not line.lstrip().startswith("#")]
        if len(required) != len(set(required)):
            raise ValueError(f"Duplicate proof target in {name}")
        if set(required) != expected:
            missing = sorted(expected - set(required))
            unexpected = sorted(set(required) - expected)
            raise ValueError(f"{name} target coverage mismatch: "
                             f"missing={missing}, unexpected={unexpected}")
        return set(required)

    check_manifest("proof-targets.txt", discovered)
    # NTT composition theories live beside other local component proofs,
    # outside the pinned historical theories/ntt support directory. Requiring
    # exact manifest coverage prevents a new NTT file silently missing --group ntt.
    composition = {name for name in discovered
                   if Path(name).parent in (Path("theories"), Path("proofs"))
                   and Path(name).name.startswith("NTT")
                   and name != "proofs/NTTCorrectness.ec"}
    return check_manifest("ntt-composition-targets.txt", composition)


def select_targets(files, group, composition):
    ntt = {path for path in files
           if "ntt" in path.relative_to(PROJECT).parts
           or path.name == "NTTCorrectness.ec"
           or str(path.relative_to(PROJECT)) in composition}
    if group == "new":
        return [path for path in files if path not in ntt]
    if group == "ntt":
        return [path for path in files if path in ntt]
    if group == "generated":
        return []
    return list(files)


def check_support_file(destination, pinned_sha256, label):
    allowed = {pinned_sha256}
    if destination in REVIEWED_SUPPORT_PORTS:
        historical, current = REVIEWED_SUPPORT_PORTS[destination]
        if pinned_sha256 != historical:
            raise ValueError(f"{label} historical support pin drift: {destination}")
        allowed.add(current)
    actual = hashlib.sha256((PROJECT / destination).read_bytes()).hexdigest()
    if actual not in allowed:
        raise ValueError(f"{label} support drift: {destination}")


def check_provenance():
    run(["sha256sum", "--check", "--status", "manifests/ntt-common-source.sha256"])
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
            check_support_file(row["destination"], row["ported_sha256"], "NTT")
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
            check_support_file(row["destination"], row["ported_sha256"], "SHAKE")
        if seen != {"theories/SHAKEBlockSpec.ec", "proofs/SHAKEBlockCorrectness.ec"}:
            raise ValueError("SHAKE provenance manifest does not cover the local support")
    run([sys.executable, "scripts/extract.py", "--check"])
    with tempfile.TemporaryDirectory(prefix="haetae120-reference-constants-") as tmp:
        fresh = Path(tmp) / "ReferenceConstants.ec"
        run([sys.executable, "scripts/reference-constants.py", "--output", str(fresh)])
        if fresh.read_bytes() != (PROJECT / "theories/ReferenceConstants.ec").read_bytes():
            raise ValueError("Reference constants drift")
        hyperball = Path(tmp) / "HyperballReferenceConstants.ec"
        run([sys.executable, "scripts/hyperball-reference-constants.py", "--output", str(hyperball)])
        if hyperball.read_bytes() != (PROJECT / "theories/HyperballReferenceConstants.ec").read_bytes():
            raise ValueError("Hyperball reference constants drift")
        gaussian = Path(tmp) / "CDTGaussianCertificate.ec"
        run([sys.executable, "scripts/gaussian-cdt-certificate.py", "--output", str(gaussian)])
        if gaussian.read_bytes() != (PROJECT / "theories/CDTGaussianCertificate.ec").read_bytes():
            raise ValueError("Gaussian mathematical certificate drift")
        exponential = Path(tmp) / "ApproxExpCertificate.ec"
        run([sys.executable, "scripts/approx-exp-certificate.py", "--output", str(exponential)])
        if exponential.read_bytes() != (PROJECT / "theories/ApproxExpCertificate.ec").read_bytes():
            raise ValueError("Approximate exponential certificate drift")
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
        composition = check_target_manifests(local)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        report.update(result="FAIL", error=str(error))
        save_report()
        print(f"RESULT FAIL group={args.group} phase=provenance: {error}", file=sys.stderr)
        return 1
    targets = select_targets(local, args.group, composition)
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
