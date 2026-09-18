#!/usr/bin/env python3
"""Ensure the proof gate rejects altered C-derived Hyperball constants."""
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

PROJECT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("haetae_verify", PROJECT / "scripts/verify.py")
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)


class HyperballProvenanceTests(unittest.TestCase):
    def test_changed_scale_is_rejected_without_editing_the_live_theory(self):
        target = PROJECT / "theories/HyperballReferenceConstants.ec"
        original_read = Path.read_bytes
        original = original_read(target)
        needle = b"W64.of_int 2643021496320"
        self.assertIn(needle, original)
        altered = original.replace(needle, b"W64.of_int 2643021496321", 1)

        def read_bytes(path):
            return altered if path == target else original_read(path)

        # The independent C emitter runs normally. Only this process's final
        # read of the expected theory is changed; concurrent proof runs see the
        # untouched source file, and no project input needs to be restored.
        with patch.object(Path, "read_bytes", read_bytes):
            with self.assertRaisesRegex(ValueError, "Hyperball reference constants drift"):
                VERIFY.check_provenance()
        self.assertEqual(original_read(target), original)


if __name__ == "__main__":
    unittest.main()
