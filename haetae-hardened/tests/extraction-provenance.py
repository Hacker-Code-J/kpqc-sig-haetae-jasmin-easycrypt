#!/usr/bin/env python3
"""Replay binds extraction inputs and outputs, not one host's compiler build."""
import copy
import importlib.util
from pathlib import Path
import sys
import unittest

PROJECT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT / "scripts"))
spec = importlib.util.spec_from_file_location("hardened_extract", PROJECT / "scripts/extract.py")
extract = importlib.util.module_from_spec(spec)
spec.loader.exec_module(extract)


class ExtractionProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.record = {
            "compiler_version": "Jasmin Compiler 2026.09.0",
            "compiler_sha256": "a" * 64,
            "options": ["--array-model=barray", "--arch=x86-64", "--cc=linux"],
            "jobs": [{"output": "Target.ec", "source": "jasmin/target.jazz", "functions": ["target"]}],
            "source_sha256": {"jasmin/target.jazz": "b" * 64},
            "generated_sha256": {"Target.ec": "c" * 64},
        }

    def test_same_release_rebuilt_compiler_can_reproduce_exact_artifact(self):
        rebuilt = copy.deepcopy(self.record)
        rebuilt["compiler_sha256"] = "d" * 64
        extract.check_manifest(self.record, rebuilt)
        self.assertEqual(self.record["compiler_sha256"], "a" * 64)

    def test_release_inputs_options_jobs_and_outputs_remain_exact(self):
        for key in self.record:
            if key == "compiler_sha256":
                continue
            changed = copy.deepcopy(self.record)
            changed[key] = "unreviewed"
            with self.subTest(key=key), self.assertRaisesRegex(SystemExit, "provenance drift"):
                extract.check_manifest(self.record, changed)

    def test_missing_or_invalid_compiler_identity_is_rejected(self):
        for value in (None, "", "unknown", "g" * 64):
            changed = copy.deepcopy(self.record)
            if value is None:
                changed.pop("compiler_sha256")
            else:
                changed["compiler_sha256"] = value
            with self.subTest(value=value), self.assertRaisesRegex(SystemExit, "provenance drift"):
                extract.check_manifest(self.record, changed)


if __name__ == "__main__":
    unittest.main()
