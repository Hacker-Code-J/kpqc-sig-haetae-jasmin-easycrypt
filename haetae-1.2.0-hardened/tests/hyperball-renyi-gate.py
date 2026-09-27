#!/usr/bin/env python3
"""Check Hyperball Renyi group isolation with the existing temporary fixtures."""
import importlib.util
import json
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location(
    "gaussian_renyi_gate_tests", Path(__file__).with_name("gaussian-renyi-gate.py"))
renyi_tests = importlib.util.module_from_spec(spec)
spec.loader.exec_module(renyi_tests)
gate = renyi_tests.gate
PROOF = renyi_tests.PROOF


class HyperballRenyiGateTests(renyi_tests.GaussianRenyiGateTests):
    def setUp(self):
        super().setUp()
        self.hyperball = {}
        dependency = "Helper"
        for name in ("Product", "Map", "Payload"):
            stem = f"HyperballRenyi{name}"
            self.hyperball[name] = self.add_variant(
                f"easycrypt/proofs/{stem}.ec", f"require import {dependency}.\n" + PROOF)
            dependency = stem
        self.write_manifest()
        path = self.project / "logs/latest-gaussian-renyi.json"
        path.write_text('{"historical":"gaussian-renyi"}\n')
        self.historical_reports[path] = path.read_bytes()

    def test_prefix_selection_includes_recursive_and_future_roots(self):
        future_spec = self.add_variant("easycrypt/theories/deep/HyperballRenyiFutureSpec.ec")
        future_proof = self.add_variant(
            "easycrypt/proofs/deep/HyperballRenyiFuture.ec", "require import HyperballRenyiFutureSpec.\n" + PROOF)
        prefix_only = self.add_variant("easycrypt/proofs/HyperballRenyi.ec")
        decoys = [self.add_variant(f"easycrypt/proofs/{name}.ec")
                  for name in ("OtherHyperballRenyi", "hyperballRenyiOther")]
        self.write_manifest()
        roots, closure = gate.proof_closure("hyperball-renyi")
        self.assertEqual(set(roots), {*self.hyperball.values(), future_spec, future_proof, prefix_only})
        self.assertLess(closure.index(future_spec), closure.index(future_proof))
        for path in decoys:
            self.assertNotIn(path, closure)

    def test_old_focused_groups_include_hyperball_only_when_imported(self):
        for group, consumer in (("gaussian-rate", self.acceptance),
                                ("gaussian-renyi", self.renyi["Actual"])):
            with self.subTest(group=group):
                roots, closure = gate.proof_closure(group)
                self.assertTrue(set(self.hyperball.values()).isdisjoint(closure))
                original = consumer.read_text()
                consumer.write_text("require import HyperballRenyiProduct.\n" + original)
                imported_roots, imported_closure = gate.proof_closure(group)
                self.assertEqual(imported_roots, roots)
                self.assertIn(self.hyperball["Product"], imported_closure)
                self.assertNotIn(self.hyperball["Payload"], imported_closure)
                self.assertLess(imported_closure.index(self.hyperball["Product"]),
                                imported_closure.index(consumer))
                consumer.write_text(original)

    def test_hyperball_replays_complete_cross_group_dependency_closure(self):
        roots, closure = gate.proof_closure("hyperball-renyi")
        self.assertEqual(set(roots), set(self.hyperball.values()))
        self.assertTrue({self.acceptance, self.attempt, *self.renyi.values()}.isdisjoint(closure))
        helper = self.add_variant("easycrypt/theories/nested/SharedGaussian.ec",
                                  "require import GaussianRenyiProduction GaussianAttemptExpectation.\n" + PROOF)
        self.hyperball["Payload"].write_text("require import HyperballRenyiMap SharedGaussian.\n" + PROOF)
        self.write_manifest()
        imported_roots, imported_closure = gate.proof_closure("hyperball-renyi")
        self.assertEqual(imported_roots, roots)
        self.assertLess(imported_closure.index(self.old_base), imported_closure.index(self.old_leaf))
        self.assertLess(imported_closure.index(self.attempt), imported_closure.index(helper))
        self.assertLess(imported_closure.index(self.renyi["Production"]), imported_closure.index(helper))
        self.assertLess(imported_closure.index(helper), imported_closure.index(self.hyperball["Payload"]))
        code, report = self.run_gate("hyperball-renyi")
        self.assertEqual(code, 0, report)
        self.assertEqual(self.compiled, imported_closure)
        self.assertEqual(len(self.compiled), len(set(self.compiled)))
        self.assertEqual(set(report["dependency_targets"]),
                         {str(path.relative_to(self.root)) for path in imported_closure if path not in roots})

    def test_default_all_includes_hyperball_and_keeps_focused_reports(self):
        roots, closure = gate.proof_closure()
        self.assertEqual(set(roots), set(self.variants.values()))
        code, report = self.run_gate("all", default=True)
        self.assertEqual(code, 0, report)
        self.assertEqual(self.compiled, closure)
        self.assertEqual(json.loads(self.latest.read_text()), report)
        for group in ("gaussian-rate", "gaussian-renyi"):
            path = self.project / "logs" / f"latest-{group}.json"
            self.assertEqual(path.read_bytes(), self.historical_reports[path])
        self.assertFalse((self.project / "logs/latest-hyperball-renyi.json").exists())

    def test_hyperball_report_preserves_older_reports_and_provenance(self):
        code, report = self.run_gate("hyperball-renyi")
        self.assertEqual(code, 0, report)
        self.assertEqual(report["group"], "hyperball-renyi")
        self.assertEqual(set(report["selected_roots"]),
                         {str(path.relative_to(self.root)) for path in self.hyperball.values()})
        self.assertEqual(len(report["variant_inventory"]), len(self.variants))
        self.assertEqual(self.baseline_reads.call_count, 2)
        self.assertEqual([command[1:] for command in self.commands[:2]],
                         [["scripts/materialize.py", "--check"], ["scripts/extract.py", "--check"]])
        for path in gate.control_files():
            self.assertEqual(report["control_sha256"][str(path.relative_to(self.root))], self.digest(path))
        for path in (self.acceptance, self.renyi["Actual"]):
            self.assertIn(str(path.relative_to(self.root)), report["source_sha256"])
        self.assertNotIn(self.project / "easycrypt/generated/HardenedHyperballTarget.ec", self.compiled)
        self.assertFalse(report["hyperball_retry_termination"])
        self.assertFalse(report["concrete_shake_randomness"])
        self.assert_historical_reports_preserved()

    def test_hyperball_failure_preserves_older_reports(self):
        self.proof_exit = 29
        code, report = self.run_gate("hyperball-renyi")
        self.assertEqual(code, 1, report)
        self.assertEqual(report["result"], "FAIL")
        self.assertEqual(report["targets"][0]["exit_code"], 29)
        self.assert_historical_reports_preserved()

    def test_hyperball_binds_each_control_hash_during_replay(self):
        for path in gate.control_files():
            with self.subTest(path=path.name):
                original = path.read_bytes()
                self.compiled.clear()
                self.mutate = lambda _target: path.write_bytes(original + b"\n# concurrent change\n")
                code, report = self.run_gate("hyperball-renyi")
                self.assertEqual(code, 1, report)
                self.assertIn("Source changed", report["error"])
                self.assertEqual(len(self.compiled), 1)
                self.assert_historical_reports_preserved()
                path.write_bytes(original)

    def test_hyperball_snapshot_covers_selected_unselected_and_generated(self):
        paths = (self.hyperball["Payload"], self.renyi["Actual"], self.acceptance,
                 self.project / "easycrypt/generated/HardenedHyperballTarget.ec")
        for path in paths:
            with self.subTest(path=path.name):
                original = path.read_bytes()
                self.mutate = lambda _target: path.write_bytes(original + b"\n(* concurrent change *)\n")
                code, report = self.run_gate("hyperball-renyi")
                self.assertEqual(code, 1, report)
                self.assertIn("Source changed", report["error"])
                self.assert_historical_reports_preserved()
                path.write_bytes(original)

    def test_hyperball_inventory_remains_global_and_rejects_duplicates(self):
        for path in (self.hyperball["Product"], self.renyi["Spec"], self.other):
            with self.subTest(path=path.name):
                omitted = str(path.relative_to(self.project))
                self.write_manifest([name for name in self.variants if name != omitted])
                with self.assertRaisesRegex(ValueError, "manifest must cover every"):
                    gate.proof_closure("hyperball-renyi")
        self.write_manifest([*self.variants, "easycrypt/proofs/HyperballRenyiProduct.ec"])
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            gate.proof_closure("hyperball-renyi")

    def test_hyperball_guard_covers_unselected_old_groups(self):
        for path in (self.acceptance, self.renyi["Actual"]):
            with self.subTest(path=path.name):
                original = path.read_text()
                path.write_text("axiom(* separator *)unproved : false.\n")
                with self.assertRaisesRegex(ValueError, "project axiom"):
                    gate.proof_closure("hyperball-renyi")
                path.write_text(original)

    def test_empty_hyperball_group_does_not_select_another_group(self):
        for path in self.hyperball.values():
            path.unlink()
            self.variants.pop(str(path.relative_to(self.project)))
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "No verification roots for group hyperball-renyi"):
            gate.proof_closure("hyperball-renyi")
        self.assertEqual(set(gate.proof_closure("gaussian-renyi")[0]), set(self.renyi.values()))

    def test_hyperball_dependency_cycle_is_rejected(self):
        self.hyperball["Product"].write_text("require import HyperballRenyiPayload.\n" + PROOF)
        with self.assertRaisesRegex(ValueError, "Cyclic proof import"):
            gate.proof_closure("hyperball-renyi")


def load_tests(loader, tests, pattern):
    # Earlier suites run separately; only their fixtures are inherited here.
    return unittest.TestSuite(HyperballRenyiGateTests(name)
                              for name in sorted(HyperballRenyiGateTests.__dict__)
                              if name.startswith("test_"))


if __name__ == "__main__":
    unittest.main()
