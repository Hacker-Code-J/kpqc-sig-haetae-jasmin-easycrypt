#!/usr/bin/env python3
"""Check Renyi group coverage and isolation using the pinned rate-gate fixtures."""
import importlib.util
import json
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location(
    "gaussian_rate_gate_tests", Path(__file__).with_name("gaussian-rate-gate.py"))
rate_tests = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rate_tests)
gate = rate_tests.gate
PROOF = rate_tests.PROOF


class GaussianRenyiGateTests(rate_tests.GaussianRateGateTests):
    def setUp(self):
        super().setUp()
        self.renyi = {}
        dependency = "Helper"
        for name in ("Spec", "Moment", "Conditioning", "KernelBounds", "Actual", "Production"):
            directory = "theories" if name == "Spec" else "proofs"
            stem = f"GaussianRenyi{name}"
            self.renyi[name] = self.add_variant(
                f"easycrypt/{directory}/{stem}.ec", f"require import {dependency}.\n" + PROOF)
            dependency = stem
        self.write_manifest()
        self.historical_reports = {self.latest: self.historical}
        for group in ("all", "gaussian-rate"):
            path = self.project / "logs" / f"latest-{group}.json"
            path.write_text(json.dumps({"historical": group}) + "\n")
            self.historical_reports[path] = path.read_bytes()

    def assert_historical_reports_preserved(self):
        for path, content in self.historical_reports.items():
            self.assertEqual(path.read_bytes(), content, path.name)

    def test_prefix_roots_cover_recursive_theories_and_future_proofs(self):
        future_spec = self.add_variant("easycrypt/theories/deep/GaussianRenyiFutureSpec.ec")
        future_proof = self.add_variant(
            "easycrypt/proofs/deep/GaussianRenyiFuture.ec", "require import GaussianRenyiFutureSpec.\n" + PROOF)
        prefix_only = self.add_variant("easycrypt/proofs/GaussianRenyi.ec")
        decoys = [self.add_variant(f"easycrypt/proofs/{name}.ec")
                  for name in ("OtherGaussianRenyi", "gaussianRenyiOther")]
        self.write_manifest()
        roots, closure = gate.proof_closure("gaussian-renyi")
        self.assertEqual(set(roots), {*self.renyi.values(), future_spec, future_proof, prefix_only})
        self.assertLess(closure.index(future_spec), closure.index(future_proof))
        for path in decoys:
            self.assertNotIn(path, closure)

    def test_rate_roots_stay_isolated_until_renyi_is_imported(self):
        roots, closure = gate.proof_closure("gaussian-rate")
        self.assertEqual(set(roots), {self.acceptance, self.attempt})
        self.assertTrue(set(self.renyi.values()).isdisjoint(closure))
        self.acceptance.write_text("require import Helper GaussianRenyiMoment.\n" + PROOF)
        imported_roots, imported_closure = gate.proof_closure("gaussian-rate")
        self.assertEqual(imported_roots, roots)
        self.assertIn(self.renyi["Spec"], imported_closure)
        self.assertIn(self.renyi["Moment"], imported_closure)
        self.assertNotIn(self.renyi["Actual"], imported_closure)
        self.assertLess(imported_closure.index(self.renyi["Moment"]), imported_closure.index(self.acceptance))

    def test_renyi_closure_checks_recursive_imports_from_old_group(self):
        roots, closure = gate.proof_closure("gaussian-renyi")
        self.assertEqual(set(roots), set(self.renyi.values()))
        self.assertTrue({self.acceptance, self.attempt, self.other}.isdisjoint(closure))
        helper = self.add_variant("easycrypt/theories/nested/ImportedRate.ec",
                                  "require import GaussianAttemptExpectation.\n" + PROOF)
        self.renyi["Actual"].write_text("require import GaussianRenyiKernelBounds ImportedRate.\n" + PROOF)
        self.write_manifest()
        imported_roots, imported_closure = gate.proof_closure("gaussian-renyi")
        self.assertEqual(imported_roots, roots)
        self.assertLess(imported_closure.index(self.attempt), imported_closure.index(helper))
        self.assertLess(imported_closure.index(helper), imported_closure.index(self.renyi["Actual"]))
        code, report = self.run_gate("gaussian-renyi")
        self.assertEqual(code, 0, report)
        self.assertEqual(self.compiled, imported_closure)
        self.assertEqual(len(self.compiled), len(set(self.compiled)))
        self.assertEqual(set(report["dependency_targets"]),
                         {str(path.relative_to(self.root)) for path in imported_closure if path not in roots})

    def test_default_all_still_includes_new_and_old_roots(self):
        roots, closure = gate.proof_closure()
        self.assertEqual(set(roots), set(self.variants.values()))
        code, report = self.run_gate("all", default=True)
        self.assertEqual(code, 0, report)
        self.assertEqual(self.compiled, closure)
        self.assertEqual(json.loads(self.latest.read_text()), report)
        rate_report = self.project / "logs/latest-gaussian-rate.json"
        self.assertEqual(rate_report.read_bytes(), self.historical_reports[rate_report])
        self.assertFalse((self.project / "logs/latest-gaussian-renyi.json").exists())

    def test_renyi_report_preserves_all_older_reports_and_provenance(self):
        code, report = self.run_gate("gaussian-renyi")
        self.assertEqual(code, 0, report)
        self.assertEqual(report["group"], "gaussian-renyi")
        self.assertEqual(set(report["selected_roots"]),
                         {str(path.relative_to(self.root)) for path in self.renyi.values()})
        self.assertEqual(len(report["variant_inventory"]), len(self.variants))
        self.assertEqual(self.baseline_reads.call_count, 2)
        self.assertEqual([command[1:] for command in self.commands[:2]],
                         [["scripts/materialize.py", "--check"], ["scripts/extract.py", "--check"]])
        for path in gate.control_files():
            self.assertEqual(report["control_sha256"][str(path.relative_to(self.root))], self.digest(path))
        self.assertIn(str(self.acceptance.relative_to(self.root)), report["source_sha256"])
        self.assertFalse(report["hyperball_retry_termination"])
        self.assertFalse(report["concrete_shake_randomness"])
        self.assert_historical_reports_preserved()

    def test_renyi_failure_preserves_all_older_reports(self):
        self.proof_exit = 23
        code, report = self.run_gate("gaussian-renyi")
        self.assertEqual(code, 1, report)
        self.assertEqual(report["result"], "FAIL")
        self.assertEqual(report["targets"][0]["exit_code"], 23)
        self.assert_historical_reports_preserved()

    def test_renyi_inventory_requires_selected_and_unselected_files(self):
        for path in (self.renyi["Spec"], self.other):
            with self.subTest(path=path.name):
                omitted = str(path.relative_to(self.project))
                self.write_manifest([name for name in self.variants if name != omitted])
                with self.assertRaisesRegex(ValueError, "manifest must cover every"):
                    gate.proof_closure("gaussian-renyi")
        self.write_manifest([*self.variants, "easycrypt/theories/GaussianRenyiSpec.ec"])
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            gate.proof_closure("gaussian-renyi")

    def test_renyi_guard_rejects_escape_in_unselected_old_group(self):
        self.acceptance.write_text("axiom(* separator *)unproved : false.\n")
        with self.assertRaisesRegex(ValueError, "project axiom"):
            gate.proof_closure("gaussian-renyi")

    def test_renyi_snapshot_rejects_unselected_old_group_change(self):
        self.mutate = lambda _path: self.acceptance.write_text(PROOF + "lemma later : true by trivial.\n")
        code, report = self.run_gate("gaussian-renyi")
        self.assertEqual(code, 1, report)
        self.assertIn("Source changed", report["error"])
        self.assert_historical_reports_preserved()

    def test_empty_renyi_group_does_not_fall_back_to_rate(self):
        for path in self.renyi.values():
            path.unlink()
            self.variants.pop(str(path.relative_to(self.project)))
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "No verification roots for group gaussian-renyi"):
            gate.proof_closure("gaussian-renyi")
        self.assertEqual(set(gate.proof_closure("gaussian-rate")[0]), {self.acceptance, self.attempt})


def load_tests(loader, tests, pattern):
    # Reuse the old fixtures without rerunning their separately maintained tests.
    return unittest.TestSuite(GaussianRenyiGateTests(name)
                              for name in sorted(GaussianRenyiGateTests.__dict__)
                              if name.startswith("test_"))


if __name__ == "__main__":
    unittest.main()
