#!/usr/bin/env python3
"""Run the public artifact checks, keeping new results separate from history."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED_PARTS = {".git", ".omx", ".agents", ".codex", ".aws", ".vscode", "__pycache__"}
RUNTIME_PATHS = {Path("build"), Path("logs"), Path("HAETAE/reference_implementation/build")}
RUNTIME_PATHS.update(Path(project) / name for project in
                     ("haetae-jasmin", "haetae-easycrypt", "haetae-hardened")
                     for name in ("build", "logs"))
MATERIALIZED = {"jasmin", "include", "test", "kat", "benchmark"}


def runtime_path(relative):
    return bool(EXCLUDED_PARTS.intersection(relative.parts)) or any(
        relative == runtime or runtime in relative.parents for runtime in RUNTIME_PATHS)


def source_snapshot():
    manifest = ROOT / "SOURCE-MANIFEST.json"
    metadata = {}
    if manifest.exists():
        if manifest.is_symlink():
            raise ValueError("Symbolic source manifest")
        content = manifest.read_bytes()
        metadata = json.loads(content)
        names = metadata["files"]
        actual_names = set()
        for directory, subdirs, filenames in os.walk(ROOT):
            relative_dir = Path(directory).relative_to(ROOT)
            subdirs[:] = [name for name in subdirs if not runtime_path(relative_dir / name)
                          and not (relative_dir == Path("env") and name in {
                              "_opam", ".opam-root", "provers", "downloads", "config"})
                          and not (relative_dir == Path("haetae-hardened") and name in MATERIALIZED)]
            for filename in filenames:
                relative = relative_dir / filename
                if relative == Path("SOURCE-MANIFEST.json") or (
                        relative.suffix in {".eco", ".pyc"} and str(relative) not in names):
                    continue
                if relative in {Path("env/bootstrap.log"), Path("env/installed-packages.txt")}:
                    continue
                actual_names.add(str(relative))
        if actual_names != set(names):
            raise ValueError("Source inventory drift: " + ", ".join(sorted(actual_names ^ set(names))))
        identity = {"git_commit": metadata.get("base_commit"), "dirty": metadata.get("dirty"),
                    "manifest_sha256": hashlib.sha256(content).hexdigest()}
    else:
        if not (ROOT / ".git").exists():
            raise ValueError("A Git checkout or exported SOURCE-MANIFEST.json is required")
        names = subprocess.check_output(["git", "ls-files", "-co", "--exclude-standard", "-z"], cwd=ROOT).decode().split("\0")
        names = {name for name in names if name and not runtime_path(Path(name))
                 and not (Path(name).name.startswith(".env") and Path(name).name != ".env.example")
                 and (ROOT / name).exists()}
        commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True)
        identity = {"git_commit": commit.stdout.strip() if commit.returncode == 0 else None,
                    "dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT))}
    files = {}
    for name in sorted(names):
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"Unsafe source path: {name}")
        path = ROOT / relative
        if any(part.is_symlink() for part in (path, *path.parents) if part != ROOT):
            raise ValueError(f"Symbolic source path: {name}")
        if not path.is_file():
            raise ValueError(f"Missing source: {name}")
        files[name] = hashlib.sha256(path.read_bytes()).hexdigest()
        if metadata and files[name] != metadata["files"][name]:
            raise ValueError(f"Source hash drift: {name}")
    if not files:
        raise ValueError("Empty source snapshot")
    identity["files"] = files
    return identity


def steps(mode, jobs):
    result = [
        ("environment", ["bash", "scripts/check-environment.sh"]),
        ("evidence", [sys.executable, "scripts/check-evidence.py"]),
        ("evidence-regressions", [sys.executable, "tests/test_evidence.py"]),
        ("runner-regressions", [sys.executable, "tests/test_reproduction.py"]),
        ("environment-regressions", [sys.executable, "tests/test_environment.py"]),
        ("source-export-regressions", [sys.executable, "tests/test_export_source.py"]),
        ("upstream-hashes", ["sha256sum", "--check", "--status", "docs/UPSTREAM-SHA256SUMS"]),
        ("jasmin-tests", ["make", "-C", "haetae-jasmin", f"-j{jobs}", "test"]),
        ("easycrypt-gates", ["make", "-C", "haetae-easycrypt", "test-gate"]),
        ("ntt-target-gate", [sys.executable, "haetae-easycrypt/tests/test_ntt_targets.py"]),
        ("hardened-prepare", [sys.executable, "haetae-hardened/scripts/materialize.py"]),
    ]
    for name in ("materialize", "layout-migration", "publication-migration", "extraction-provenance", "verification-gate",
                 "gaussian-rate-gate", "gaussian-renyi-gate", "hyperball-renyi-gate"):
        result.append(("hardened-" + name, [sys.executable, f"haetae-hardened/tests/{name}.py"]))
    result.append(("hardened-tests", ["make", "-C", "haetae-hardened", f"-j{jobs}", "test"]))
    if mode == "full":
        result.extend([
            ("reference-kat", ["bash", "scripts/check-baseline.sh"]),
            ("hyperball-certificate", [sys.executable, "haetae-easycrypt/scripts/hyperball-tail-certificate.py", "--check"]),
            ("baseline-boundary", ["make", "-C", "haetae-easycrypt", "test-hyperball-boundary"]),
            ("hardened-boundary", [sys.executable, "haetae-hardened/tests/checked-hyperball.py"]),
            ("jasmin-ct", ["make", "-C", "haetae-jasmin", "sampler-ct"]),
            ("hardened-ct", ["bash", "haetae-hardened/scripts/check-ct.sh"]),
            ("baseline-proofs", ["make", "-C", "haetae-easycrypt", "verify"]),
            ("hardened-proofs", [sys.executable, "haetae-hardened/scripts/verify.py", "--group", "all"]),
        ])
    return result


def run(mode, output, jobs):
    output = output.resolve()
    root = ROOT.resolve()
    if output == root or (root in output.parents and not output.is_relative_to(root / "build")):
        raise ValueError("Output must be outside the source tree or inside its root build/ directory")
    output.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    report = {"mode": mode, "result": "RUNNING", "started_at": datetime.now(timezone.utc).isoformat(),
              "scope": "component claims and tests; not complete signature correctness or security",
              "steps": []}
    plan = steps(mode, jobs)
    report["planned_steps"] = [name for name, _ in plan]

    def save():
        report["seconds"] = round(time.monotonic() - started, 3)
        temporary = output / "summary.tmp"
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(output / "summary.json")

    save()
    try:
        report["source"] = source_snapshot()
        report["verification_options"] = {name: os.environ.get(name) for name in
                                          ("EC_TIMEOUT", "EC_MAX_PROVERS", "WHY3_SERVER_SOCKET")}
        save()
        for index, (name, command) in enumerate(plan, 1):
            log = output / f"{index:02d}-{name}.log"
            record = {"name": name, "command": command, "result": "RUNNING", "log": log.name}
            report["steps"].append(record)
            save()
            print(f"RUN {name} -> {log}", flush=True)
            step_started = time.monotonic()
            with log.open("w") as stream:
                process = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
            record.update(exit_code=process.returncode, result="PASS" if process.returncode == 0 else "FAIL",
                          seconds=round(time.monotonic() - step_started, 3),
                          log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
            save()
            if process.returncode:
                report["result"] = "FAIL"
                print("\n".join(log.read_text(errors="replace").splitlines()[-25:]), file=sys.stderr)
                break
        else:
            report["result"] = "PASS"
    except (OSError, ValueError, subprocess.CalledProcessError, KeyboardInterrupt) as error:
        report.update(result="FAIL", error=type(error).__name__ + ": " + str(error))
        if report["steps"] and report["steps"][-1]["result"] == "RUNNING":
            report["steps"][-1].update(result="FAIL", error=report["error"])
    finally:
        if "source" in report:
            try:
                report["source_unchanged"] = source_snapshot() == report["source"]
                if not report["source_unchanged"]:
                    report.update(result="FAIL", error="Source snapshot changed during verification")
            except (OSError, ValueError, subprocess.CalledProcessError) as error:
                report.update(result="FAIL", source_unchanged=False, error=str(error))
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        save()
        print(f"RESULT {report['result']}: {output / 'summary.json'}", flush=True)
    return 0 if report["result"] == "PASS" else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("quick", "full"))
    parser.add_argument("--output", type=Path, help="New result directory; must not already exist")
    parser.add_argument("--jobs", type=int, default=int(os.environ.get("JOBS", "2")))
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    output = args.output or ROOT / "build/reproduction" / (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ") + "-" + args.mode)
    if output.exists():
        parser.error("Output directory already exists; previous evidence will not be overwritten")
    try:
        return run(args.mode, output, args.jobs)
    except ValueError as error:
        parser.error(str(error))


if __name__ == "__main__":
    sys.exit(main())
