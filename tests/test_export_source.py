#!/usr/bin/env python3
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("export_source", Path(__file__).resolve().parents[1] / "scripts/export-source.py")
export = importlib.util.module_from_spec(spec)
spec.loader.exec_module(export)


class ExportTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.root = self.base / "source"
        self.root.mkdir()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        (self.root / "source.py").write_text("print('source')\n")

    def test_exports_source_but_not_local_state(self):
        for name in ("build/output", "logs/result", ".omx/state", ".aws/credentials", ".env"):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("excluded")
        (self.root / ".env.example").write_text("EXAMPLE=value\n")
        historical = self.root / "archive/legacy/project/logs/summary.txt"
        historical.parent.mkdir(parents=True)
        historical.write_text("historical evidence\n")
        target = self.base / "export"
        report = export.export_source(self.root, target)
        self.assertEqual(set(report["files"]), {"source.py", ".env.example", "archive/legacy/project/logs/summary.txt"})
        self.assertTrue(report["dirty"])
        self.assertEqual(json.loads((target / "SOURCE-MANIFEST.json").read_text()), report)
        self.assertFalse((target / ".git").exists())

    def test_rejects_links_and_existing_or_nested_destinations(self):
        target = self.base / "export"
        (self.root / "link").symlink_to(self.root / "source.py")
        with self.assertRaisesRegex(ValueError, "Symbolic"):
            export.export_source(self.root, target)
        self.assertFalse(target.exists())
        with self.assertRaisesRegex(ValueError, "outside"):
            export.export_source(self.root, self.root / "nested")
        target.mkdir()
        with self.assertRaisesRegex(ValueError, "already exist"):
            export.export_source(self.root, target)


if __name__ == "__main__":
    unittest.main()
