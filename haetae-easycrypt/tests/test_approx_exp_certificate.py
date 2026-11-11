#!/usr/bin/env python3
"""Reject wrong Bernstein signs, false polynomial links and coefficient drift."""
import copy
import importlib.util
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


PROJECT = Path(__file__).resolve().parents[1]
RUNNER = PROJECT / "scripts/verify-one.sh"
SPEC = importlib.util.spec_from_file_location(
    "approx_exp_certificate", PROJECT / "scripts/approx-exp-certificate.py"
)
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)


class ApproxExpCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = GENERATOR.certificate(GENERATOR.REFERENCE)
        cls.live = PROJECT / "theories/ApproxExpCertificate.ec"
        cls.original = cls.live.read_bytes()

    def check_copy(self, data):
        with tempfile.TemporaryDirectory(prefix="haetae120-exp-certificate-test-") as directory:
            root = Path(directory)
            module_name = "TestApproxExpCertificate"
            certificate = GENERATOR.generate(GENERATOR.REFERENCE, data)
            (root / f"{module_name}.ec").write_text(certificate)
            proof = (PROJECT / "proofs/ApproxExpCertificateChecks.ec").read_text()
            proof = re.sub(r"\bApproxExpCertificate\b", module_name, proof)
            names = re.findall(r"(?m)^op\s+(?:\[opaque\]\s+)?(aec_\w+)\s*:", certificate)
            for name in names:
                proof = re.sub(rf"\b{name}\b", f"{module_name}.{name}", proof)
            source = root / "ApproxExpCertificateChecks.ec"
            source.write_text(proof)
            environment = os.environ.copy()
            environment.pop("WHY3_SERVER_SOCKET", None)
            result = subprocess.run(
                ["bash", str(RUNNER), str(source)], cwd=PROJECT,
                env=environment, text=True, capture_output=True, timeout=120,
            )
        self.assertEqual(self.live.read_bytes(), self.original, "live certificate changed")
        return result

    def assert_math_rejected(self, data):
        result = self.check_copy(data)
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, "altered mathematical certificate was accepted")
        self.assertIn("[critical]", output)
        self.assertNotIn("parse error", output)
        self.assertNotIn("cannot locate", output)
        self.assertRegex(output, r"cannot close goals|cannot save an incomplete proof|not a valid equation|ring")

    def test_original_full_certificate_checker(self):
        result = self.check_copy(self.data)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_negative_control_with_consistent_power_coefficients(self):
        data = copy.deepcopy(self.data)
        row = data["rows"][0]
        row["bernstein"][0] = -1
        row["power"] = GENERATOR.to_power(row["bernstein"])
        self.assert_math_rejected(data)

    def test_consistent_positive_rows_for_the_wrong_polynomial(self):
        data = copy.deepcopy(self.data)
        row = data["rows"][0]
        row["bernstein"] = [value + 1 for value in row["bernstein"]]
        row["power"] = GENERATOR.to_power(row["bernstein"])
        self.assertTrue(all(value >= 0 for value in row["bernstein"]))
        self.assert_math_rejected(data)

    def test_changed_reference_coefficient_is_rejected(self):
        data = copy.deepcopy(self.data)
        data["coefficients"][0] += 1
        self.assert_math_rejected(data)


if __name__ == "__main__":
    unittest.main()
