#!/usr/bin/env python3
"""Check that altered analytic certificates and table provenance are rejected."""
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
    "gaussian_certificate", PROJECT / "scripts/gaussian-cdt-certificate.py"
)
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)


class GaussianCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = GENERATOR.certificate(GENERATOR.REFERENCE)
        cls.live = PROJECT / "theories/CDTGaussianCertificate.ec"
        cls.original = cls.live.read_bytes()

    def check_copy(self, data, proof):
        with tempfile.TemporaryDirectory(prefix="haetae120-cdt-certificate-test-") as directory:
            root = Path(directory)
            # Use an unambiguous module name: a same-name temporary module
            # could otherwise lose to the project's -I search-path entries.
            module_name = "TestGaussianCertificate"
            certificate = GENERATOR.generate(GENERATOR.REFERENCE, data)
            (root / f"{module_name}.ec").write_text(certificate)
            source = root / proof
            proof_text = (PROJECT / "proofs" / proof).read_text()
            if proof == "CDTGaussianTableBridge.ec":
                # Exercise the actual table-identity proof itself. Later
                # lemmas use the original certificate-checker namespace and
                # are validated by the complete project gate instead.
                end = proof_text.index("\nqed.", proof_text.index("lemma gi_actual_thresholds"))
                proof_text = proof_text[:end + len("\nqed.")] + "\n"
                proof_text = re.sub(r"\bCDTGaussianCertificateChecks\b", "", proof_text)
            proof_text = re.sub(r"\bCDTGaussianCertificate\b", module_name, proof_text)
            names = re.findall(r"(?m)^op\s+(?:\[opaque\]\s+)?(gi_\w+)\s*:", certificate)
            for name in names:
                proof_text = re.sub(rf"\b{name}\b", f"{module_name}.{name}", proof_text)
            source.write_text(proof_text)
            environment = os.environ.copy()
            environment.pop("WHY3_SERVER_SOCKET", None)
            result = subprocess.run(
                ["bash", str(RUNNER), str(source)], cwd=PROJECT,
                env=environment, text=True, capture_output=True, timeout=120,
            )
        self.assertEqual(self.live.read_bytes(), self.original, "live certificate changed")
        return result

    def test_original_certificate_and_table_identity(self):
        for proof in ("CDTGaussianCertificateChecks.ec", "CDTGaussianTableBridge.ec"):
            with self.subTest(proof=proof):
                result = self.check_copy(self.data, proof)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_wrong_squaring_step_is_rejected_by_the_proof(self):
        data = copy.deepcopy(self.data)
        lower, upper = data["squaring"][1]
        data["squaring"][1] = (lower + 1, upper)
        result = self.check_copy(data, "CDTGaussianCertificateChecks.ec")
        self.assertNotEqual(result.returncode, 0, "altered squaring certificate was accepted")
        self.assertIn("cannot close goals", result.stdout + result.stderr)

    def test_changed_comparison_table_is_rejected_by_the_bridge(self):
        data = copy.deepcopy(self.data)
        data["thresholds"][0] += 1
        result = self.check_copy(data, "CDTGaussianTableBridge.ec")
        self.assertNotEqual(result.returncode, 0, "a different implementation table was accepted")
        self.assertIn("cannot close goals", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
