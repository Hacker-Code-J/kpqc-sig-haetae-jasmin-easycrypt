#!/usr/bin/env python3
"""Guard against writing through links, baseline drift, and ambiguous overlays."""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

PROJECT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("hardened_materialize", PROJECT / "scripts/materialize.py")
materialize = importlib.util.module_from_spec(spec)
spec.loader.exec_module(materialize)


class MaterializationTests(unittest.TestCase):
    def test_parent_symlink_cannot_write_into_baseline(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "variant"
            baseline = root / "original"
            project.mkdir()
            baseline.mkdir()
            original = baseline / "phase.jinc"
            original.write_text("preserved\n")
            (project / "jasmin").symlink_to(baseline, target_is_directory=True)
            outputs = {"build/early.txt": b"must not write", "jasmin/phase.jinc": b"overlay"}
            with patch.object(materialize, "PROJECT", project), \
                 patch.object(materialize, "desired_outputs", return_value=outputs), \
                 patch("sys.argv", ["materialize.py"]):
                with self.assertRaisesRegex(SystemExit, "Symbolic"):
                    materialize.main()
            self.assertEqual(original.read_text(), "preserved\n")
            self.assertFalse((project / "build/early.txt").exists())

    def test_leaf_symlink_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            project = Path(temp)
            (project / "a").symlink_to(project / "missing")
            with patch.object(materialize, "PROJECT", project):
                with self.assertRaisesRegex(SystemExit, "Symbolic"):
                    materialize.safe_target("a")

    def test_absolute_and_parent_paths_rejected(self):
        for path in ("../old/file", "/tmp/unrelated-file"):
            with self.assertRaisesRegex(SystemExit, "Invalid"):
                materialize.safe_target(path)

    def test_duplicate_or_missing_function_rejected(self):
        function = "fn checked() {\n}\n"
        for source in ("", function + function):
            with self.assertRaisesRegex(SystemExit, "Expected one"):
                materialize.replace_function(source, function, "checked")

    def test_baseline_drift_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "source").write_bytes(b"modified")
            lock = root / "lock.json"
            lock.write_text(json.dumps({"files": {"source": hashlib.sha256(b"original").hexdigest()}}))
            with patch.object(materialize, "ROOT", root), patch.object(materialize, "LOCK", lock):
                with self.assertRaisesRegex(SystemExit, "baseline drift"):
                    materialize.read_baseline()


if __name__ == "__main__":
    unittest.main()
