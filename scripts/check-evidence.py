#!/usr/bin/env python3
"""Check the portable historical evidence without following recorded host paths."""
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]


def historical_path_id(path):
    """Identify a recorded host path without requiring its spelling in the index."""
    return hashlib.sha256(path.encode("utf-8")).hexdigest()


def safe_file(root, name):
    relative = PurePosixPath(name)
    if relative.is_absolute() or not relative.parts or ".." in relative.parts:
        raise ValueError(f"Invalid evidence path: {name}")
    path = root.joinpath(*relative.parts)
    for parent in (path, *path.parents):
        if parent == root:
            break
        if parent.is_symlink():
            raise ValueError(f"Symbolic evidence path: {name}")
    if not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"Missing or escaping evidence: {name}")
    return path


def check_evidence(root, manifest):
    index = json.loads(safe_file(root, "index.json").read_text())
    version = index.get("schema_version")
    if version not in (1, 2):
        raise ValueError("Unsupported evidence index")
    files, originals = {}, {}
    for row in index["files"]:
        name = row["path"]
        if name in files:
            raise ValueError(f"Duplicate evidence path: {name}")
        data = safe_file(root, name).read_bytes()
        if len(data) != row["bytes"] or hashlib.sha256(data).hexdigest() != row["sha256"]:
            raise ValueError(f"Evidence hash or size mismatch: {name}")
        files[name] = row
        if version == 1:
            identities = [historical_path_id(path) for path in
                          (row["original_path"], *row.get("historical_aliases", []))]
        else:
            identities = [row["historical_path_sha256"], *row.get("historical_alias_sha256", [])]
            if any(not isinstance(value, str) or len(value) != 64 or
                   any(char not in "0123456789abcdef" for char in value) for value in identities):
                raise ValueError(f"Invalid historical path identity: {name}")
        for original in identities:
            if original in originals and originals[original] != name:
                raise ValueError(f"Ambiguous historical evidence path: {original}")
            originals[original] = name

    for key in ("summary", "validation_record"):
        anchor = manifest["full_replay"][key]
        if index["anchors"][key] != anchor or files[anchor["path"]]["sha256"] != anchor["sha256"]:
            raise ValueError(f"Historical evidence anchor mismatch: {key}")
    summary = json.loads(safe_file(root, index["anchors"]["summary"]["path"]).read_text())
    result = json.loads(safe_file(root, index["anchors"]["validation_record"]["path"]).read_text())
    targets = summary["targets"]
    groups = Counter(row["group"] for row in targets.values())
    if summary["status"] != "PASS" or result["status"] != "PASS" or \
            summary["total"] != len(targets) or summary["passed"] != len(targets) or summary["failed"] != 0 or \
            result["primary_targets"] != len(targets) or groups != result["groups"] or \
            groups != index["historical_primary_targets"]:
        raise ValueError("Historical target counts or status mismatch")
    for identity, row in targets.items():
        if row["id"] != identity or row["status"] != "PASS" or row["exit_code"] != 0:
            raise ValueError(f"Historical target did not pass: {identity}")
        if historical_path_id(row["log"]) not in originals:
            raise ValueError(f"Missing final historical log: {identity}")
        mains = [originals[historical_path_id(arg)] for arg in row["command"]
                 if arg.endswith(".ec") and historical_path_id(arg) in originals]
        if len(mains) != 1 or files[mains[0]]["sha256"] != row["source_sha256"]:
            raise ValueError(f"Historical checked source mismatch: {identity}")
    return len(files), len(targets)


if __name__ == "__main__":
    try:
        manifest = json.loads((ROOT / "haetae-easycrypt/manifests/2026.09-migration.json").read_text())
        files, targets = check_evidence(ROOT / "evidence/toolchain-migration", manifest)
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit(f"FAIL: {error}") from error
    print(f"PASS: {files} historical evidence files; {targets} final target sources and logs. "
          "This checks archived evidence, not current proofs.")
