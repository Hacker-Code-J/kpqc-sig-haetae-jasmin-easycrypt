#!/usr/bin/env python3
"""Keep layout edits distinct from unreviewed source or evidence changes."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

PROJECT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("materialize", PROJECT / "scripts/materialize.py")
materialize = importlib.util.module_from_spec(spec)
spec.loader.exec_module(materialize)


class LayoutMigrationTests(unittest.TestCase):
    def test_paths_are_mapped_once_and_collisions_rejected(self):
        files = {"haetae-1.2.0-jasmin/Makefile": "pin", "docs/HAETAE-1.2.0.md": "doc"}
        mapped = materialize.relocate_files(files)
        self.assertEqual(mapped, {"haetae-jasmin/Makefile": "pin", "docs/HAETAE.md": "doc"})
        self.assertEqual(materialize.relocate_files(mapped), mapped)
        files["haetae-jasmin/Makefile"] = "pin"
        with self.assertRaisesRegex(SystemExit, "collision"):
            materialize.relocate_files(files)

    def test_exact_bytes_only_and_historical_lock_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "haetae-jasmin/Makefile"
            source.parent.mkdir()
            before, after = b"old layout\n", b"new layout\n"
            source.write_bytes(after)
            old, new = map(materialize.digest, (before, after))
            lock = root / "baseline-lock.json"
            lock.write_text(json.dumps({"files": {"haetae-1.2.0-jasmin/Makefile": old}}))
            original_lock = lock.read_bytes()
            ledger = root / "layout-migration.json"
            ledger.write_text(json.dumps({"files": {
                "haetae-jasmin/Makefile": {"before_sha256": old, "after_sha256": new}}}))
            with patch.object(materialize, "ROOT", root), patch.object(materialize, "LOCK", lock), \
                    patch.object(materialize, "LAYOUT_SHA256", materialize.digest(ledger.read_bytes())):
                self.assertEqual(materialize.read_baseline()[1], {"haetae-jasmin/Makefile": after})
                self.assertEqual(lock.read_bytes(), original_lock)
                source.write_bytes(after + b"unreviewed")
                with self.assertRaisesRegex(SystemExit, "Pinned baseline drift"):
                    materialize.read_baseline()
                source.write_bytes(after)
                lock.write_text(json.dumps({"files": {"haetae-1.2.0-jasmin/Makefile": "0" * 64}}))
                with self.assertRaisesRegex(SystemExit, "Pinned baseline drift"):
                    materialize.read_baseline()
                lock.write_bytes(original_lock)
                ledger.write_bytes(ledger.read_bytes() + b"\n")
                with self.assertRaisesRegex(SystemExit, "layout migration"):
                    materialize.read_baseline()


if __name__ == "__main__":
    unittest.main()
