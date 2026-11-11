#!/usr/bin/env python3
"""The reproduction entry point must fail closed and preserve prior reports."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("reproduce", ROOT / "scripts/reproduce.py")
reproduce = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reproduce)


class ReproductionTests(unittest.TestCase):
    @staticmethod
    def source_fixture(root):
        (root / "input.txt").write_text("source bytes\n")
        (root / "SOURCE-MANIFEST.json").write_text(json.dumps({"files": {
            "input.txt": hashlib.sha256((root / "input.txt").read_bytes()).hexdigest()}}))

    def test_failure_stops_later_checks_and_records_exit_code(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.source_fixture(root)
            plan = [("bad", [sys.executable, "-c", "raise SystemExit(7)"]),
                    ("must-not-run", [sys.executable, "-c", "raise SystemExit(0)"])]
            with patch.object(reproduce, "ROOT", root), patch.object(reproduce, "steps", return_value=plan):
                self.assertEqual(reproduce.run("quick", root / "build/results", 1), 1)
            report = json.loads((root / "build/results/summary.json").read_text())
            self.assertEqual(report["result"], "FAIL")
            self.assertEqual(len(report["steps"]), 1)
            self.assertEqual(report["steps"][0]["exit_code"], 7)

    def test_success_requires_all_steps_and_preserves_existing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.source_fixture(root)
            plan = [("first", [sys.executable, "-c", "print('checked')"]),
                    ("second", [sys.executable, "-c", "print('checked again')"])]
            with patch.object(reproduce, "ROOT", root), patch.object(reproduce, "steps", return_value=plan):
                self.assertEqual(reproduce.run("full", root / "build/results", 1), 0)
                original = (root / "build/results/summary.json").read_bytes()
                with self.assertRaises(FileExistsError):
                    reproduce.run("full", root / "build/results", 1)
                self.assertEqual((root / "build/results/summary.json").read_bytes(), original)
            report = json.loads(original)
            self.assertEqual(report["result"], "PASS")
            self.assertEqual(len(report["steps"]), len(plan))
            self.assertTrue(all(len(step["log_sha256"]) == 64 for step in report["steps"]))

    def test_missing_executable_does_not_claim_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.source_fixture(root)
            with patch.object(reproduce, "ROOT", root), patch.object(reproduce, "steps", return_value=[
                    ("missing", [str(root / "absent-command")])]):
                self.assertEqual(reproduce.run("quick", root / "build/results", 1), 1)
            report = json.loads((root / "build/results/summary.json").read_text())
            self.assertEqual(report["result"], "FAIL")
            self.assertIn("FileNotFoundError", report["error"])

    def test_full_checks_materialize_before_proofs_and_never_write_extraction(self):
        plan = reproduce.steps("full", 2)
        names = [name for name, _ in plan]
        self.assertLess(names.index("hardened-prepare"), names.index("hardened-proofs"))
        self.assertIn("baseline-proofs", names)
        self.assertTrue(all("--write" not in command for _, command in plan))

    def test_source_changed_during_execution_cannot_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.source_fixture(root)
            command = [sys.executable, "-c", "from pathlib import Path; Path('input.txt').write_text('changed')"]
            with patch.object(reproduce, "ROOT", root), patch.object(reproduce, "steps", return_value=[("mutate", command)]):
                self.assertEqual(reproduce.run("quick", root / "build/results", 1), 1)
            report = json.loads((root / "build/results/summary.json").read_text())
            self.assertEqual(report["result"], "FAIL")
            self.assertFalse(report["source_unchanged"])

    def test_exported_source_hash_and_inventory_are_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.source_fixture(root)
            with patch.object(reproduce, "ROOT", root):
                self.assertIn("input.txt", reproduce.source_snapshot()["files"])
                (root / "unlisted.ec").write_text("axiom unexpected : false.")
                with self.assertRaisesRegex(ValueError, "inventory drift"):
                    reproduce.source_snapshot()

    def test_historical_log_and_build_directories_remain_pinned(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.source_fixture(root)
            manifest = root / "SOURCE-MANIFEST.json"
            metadata = json.loads(manifest.read_text())
            historical = (
                "archive/legacy/haetae-topdown-easycrypt/logs/verify-all-summary.txt",
                "evidence/build/source-record.txt",
            )
            for name in historical:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("historical evidence\n")
                metadata["files"][name] = hashlib.sha256(path.read_bytes()).hexdigest()
            manifest.write_text(json.dumps(metadata))
            runtime = root / "haetae-easycrypt/logs/new.log"
            runtime.parent.mkdir(parents=True)
            runtime.write_text("new execution log\n")
            with patch.object(reproduce, "ROOT", root):
                snapshot = reproduce.source_snapshot()
                self.assertTrue(all(name in snapshot["files"] for name in historical))
                (root / historical[0]).write_text("changed historical result\n")
                with self.assertRaisesRegex(ValueError, "Source hash drift"):
                    reproduce.source_snapshot()

    def test_output_inside_source_is_rejected_before_writing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.source_fixture(root)
            output = root / "custom-results"
            with patch.object(reproduce, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "outside the source tree"):
                    reproduce.run("quick", output, 1)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
