#!/usr/bin/env python3
"""Apply the existing EOF regression suite to the variant's own proof runner."""
import importlib.util
from pathlib import Path
import unittest

PROJECT = Path(__file__).resolve().parents[1]
source = PROJECT.parent / "haetae-1.2.0-easycrypt/tests/test_verification_gate.py"
spec = importlib.util.spec_from_file_location("original_gate_regressions", source)
original = importlib.util.module_from_spec(spec)
spec.loader.exec_module(original)
original.PROJECT = PROJECT
original.RUNNER = PROJECT / "scripts/verify-one.sh"
VerificationGateTests = original.VerificationGateTests

if __name__ == "__main__":
    unittest.main()
