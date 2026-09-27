#!/usr/bin/env python3
"""Materialize a separate, hash-pinned HAETAE 1.2.0 hardening overlay."""
import argparse
import hashlib
import json
from pathlib import Path
import re

PROJECT = Path(__file__).resolve().parents[1]
ROOT = PROJECT.parent
BASE = ROOT / "haetae-1.2.0-jasmin"
LOCK = PROJECT / "baseline-lock.json"
COPY_DIRS = {"jasmin", "include", "test", "kat", "benchmark"}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_baseline():
    lock = json.loads(LOCK.read_text())
    data = {}
    for name, expected in lock["files"].items():
        path = ROOT / name
        if not path.is_file() or path.is_symlink():
            raise SystemExit(f"Missing or symbolic baseline input: {name}")
        content = path.read_bytes()
        if digest(content) != expected:
            raise SystemExit(f"Pinned baseline drift: {name}")
        data[name] = content
    return lock, data


def function_span(source, name):
    starts = list(re.finditer(r"(?m)^fn " + re.escape(name) + r"\(", source))
    if len(starts) != 1:
        raise SystemExit(f"Expected one function {name}, found {len(starts)}")
    start = starts[0].start()
    end = source.find("\n}\n", start)
    if end < 0:
        raise SystemExit(f"Missing function terminator: {name}")
    return start, end + 3


def replace_function(source, fragment, name):
    start, end = function_span(source, name)
    a, b = function_span(fragment, name)
    return source[:start] + fragment[a:b] + source[end:]


def safe_target(relative):
    relative = Path(relative)
    if relative.is_absolute() or ".." in relative.parts:
        raise SystemExit(f"Invalid materialization target: {relative}")
    target = PROJECT / relative
    for ancestor in (target, *target.parents):
        if ancestor == PROJECT:
            break
        if ancestor.is_symlink():
            raise SystemExit(f"Symbolic materialization path: {ancestor}")
    if not target.resolve().is_relative_to(PROJECT):
        raise SystemExit(f"Escaping materialization target: {relative}")
    return target


def desired_outputs():
    lock, baseline = read_baseline()
    overlay = {name: (PROJECT / "overlay" / name).read_bytes() for name in (
        "checked_hyperball.jinc", "sign-scale-and-check.jinc",
        "hyperball-phase-wrappers.jinc")}
    outputs = {}
    prefix = "haetae-1.2.0-jasmin/"
    for name, content in baseline.items():
        if name.startswith(prefix):
            relative = name[len(prefix):]
            if Path(relative).parts[0] in COPY_DIRS:
                outputs[relative] = content
    phase = outputs["jasmin/hyperball_phase.jinc"].decode()
    for name in ("_polyfixveclk_scale_and_check", "_polyfixveclk_scale_and_check_values"):
        phase = replace_function(phase, overlay["hyperball-phase-wrappers.jinc"].decode(), name)
    outputs["jasmin/hyperball_phase.jinc"] = overlay["checked_hyperball.jinc"] + b"\n" + phase.encode()
    sign = outputs["jasmin/sign.jazz"].decode()
    outputs["jasmin/sign.jazz"] = replace_function(
        sign, overlay["sign-scale-and-check.jinc"].decode(), "_sf_scale_and_check").encode()
    # Distinct binary names and SONAMEs prevent confusing the variant with the baseline.
    outputs["build/baseline.mk"] = baseline[prefix + "Makefile"].replace(b"-jazz", b"-hardened-jazz")
    provenance = {
        "baseline_commit": lock["commit"],
        "baseline_lock_sha256": digest(LOCK.read_bytes()),
        "overlay_sha256": {name: digest(content) for name, content in overlay.items()},
        "materialized_sha256": {name: digest(content) for name, content in sorted(outputs.items())},
    }
    outputs["build/materialization.json"] = (json.dumps(provenance, indent=2) + "\n").encode()
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check existing materialization without writing")
    args = parser.parse_args()
    outputs = desired_outputs()
    # Validate every ancestor before any write: a symlinked jasmin/ directory
    # must never redirect an overlay into the preserved baseline.
    destinations = {name: safe_target(name) for name in outputs}
    # Unexpected source files would change wildcard dependencies; reject them explicitly.
    extra = sorted(str(p.relative_to(PROJECT)) for directory in COPY_DIRS
                   for p in (PROJECT / directory).rglob("*") if p.is_file()
                   and str(p.relative_to(PROJECT)) not in outputs)
    if extra:
        raise SystemExit("Unexpected materialized input(s): " + ", ".join(extra))
    for relative, content in outputs.items():
        path = destinations[relative]
        if path.exists() and path.read_bytes() == content:
            continue
        if args.check:
            raise SystemExit(f"Materialization drift: {relative}")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    print(f"PASS: {len(outputs)} hardened outputs {'match' if args.check else 'materialized from'} pinned baseline and overlay")


if __name__ == "__main__":
    main()
