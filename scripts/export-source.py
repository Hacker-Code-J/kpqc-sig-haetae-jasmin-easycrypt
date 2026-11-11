#!/usr/bin/env python3
"""Export the current source tree without Git history, caches or local state."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


EXCLUDED_PARTS = {".git", ".omx", ".agents", ".codex", ".aws", ".vscode",
                  "__pycache__"}
RUNTIME_PATHS = {Path("build"), Path("logs"), Path("HAETAE/reference_implementation/build")}
RUNTIME_PATHS.update(Path(project) / directory
                     for project in ("haetae-jasmin", "haetae-easycrypt", "haetae-hardened")
                     for directory in ("build", "logs"))


def export_source(root, destination):
    root, destination = root.resolve(), destination.resolve()
    if destination == root or root in destination.parents:
        raise ValueError("Choose a destination outside the source repository")
    if destination.exists():
        raise ValueError("Destination must not already exist")
    names = subprocess.check_output(
        ["git", "ls-files", "-co", "--exclude-standard", "-z"], cwd=root).decode().split("\0")
    sources = []
    for name in sorted(set(names) - {""}):
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"Unsafe source path: {name}")
        if EXCLUDED_PARTS.intersection(relative.parts) or relative.name.startswith(".env") and relative.name != ".env.example":
            continue
        if any(relative == runtime or runtime in relative.parents for runtime in RUNTIME_PATHS):
            continue
        path = root / relative
        if any(part.is_symlink() for part in (path, *path.parents) if part != root):
            raise ValueError(f"Symbolic source path: {name}")
        if path.is_file():
            sources.append((name, path))
    if not sources:
        raise ValueError("No source files found")
    try:
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root,
                                         stderr=subprocess.DEVNULL).decode().strip()
    except subprocess.CalledProcessError:
        commit = None
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=root))
    destination.mkdir(parents=True)
    hashes = {}
    for name, path in sources:
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, target)
        hashes[name] = hashlib.sha256(target.read_bytes()).hexdigest()
    report = {"kind": "working-tree source snapshot", "base_commit": commit,
              "dirty": dirty, "files": hashes}
    (destination / "SOURCE-MANIFEST.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        report = export_source(root, args.destination)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Export failed: {error}\n")
    print(f"Exported {len(report['files'])} files to {args.destination}; dirty={report['dirty']}")


if __name__ == "__main__":
    main()
