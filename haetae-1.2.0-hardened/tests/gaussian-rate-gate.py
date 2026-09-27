#!/usr/bin/env python3
"""Exercise group selection and provenance failures without replaying large proofs."""
from contextlib import ExitStack, redirect_stdout
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
PROJECT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT / "scripts"))
spec = importlib.util.spec_from_file_location("gaussian_rate_gate", PROJECT / "scripts/verify.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
materialize = sys.modules["materialize"]

PROOF = "require import AllCore.\nlemma closed : true by trivial.\n"


class GaussianRateGateTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="haetae-gaussian-rate-gate-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.project = self.root / "variant"
        self.baseline = self.root / "original"
        self.variants = {}
        self.compiled = []
        self.commands = []
        self.mutate = None
        self.proof_exit = 0
        for directory in ("scripts", "easycrypt/proofs", "easycrypt/theories", "easycrypt/generated",
                          "overlay", "jasmin", "include", "logs"):
            (self.project / directory).mkdir(parents=True)
        for directory in ("scripts", "theories", "proofs", "generated/sampler"):
            (self.baseline / directory).mkdir(parents=True)
        for name in ("verify.py", "verify-one.sh", "materialize.py", "extract.py"):
            (self.project / "scripts" / name).write_bytes((PROJECT / "scripts" / name).read_bytes())
        (self.baseline / "scripts/verify.py").write_text("# pinned lexical guard fixture\n")
        self.old_base = self.baseline / "theories/OldBase.ec"
        self.old_base.write_text(PROOF)
        self.old_leaf = self.baseline / "proofs/OldLeaf.ec"
        self.old_leaf.write_text("require import OldBase.\nlemma leaf : true by trivial.\n")
        self.preserved = self.baseline / "preserved.c"
        self.preserved.write_text("/* original implementation fixture */\n")
        array = "from Jasmin require import JByte_array.\nclone include ByteArray with op size <= 8.\n"
        (self.baseline / "generated/sampler/BArray8.ec").write_text(array)
        (self.project / "easycrypt/generated/BArray8.ec").write_text(array)
        (self.project / "easycrypt/generated/HardenedHyperballTarget.ec").write_text(
            "require import BArray8.\nmodule M = {}.\n")
        (self.project / "overlay/checked.jinc").write_text("// pinned overlay fixture\n")
        (self.project / "jasmin/checked.jazz").write_text("// materialized source fixture\n")
        (self.project / "include/checked.h").write_text("/* materialized header fixture */\n")
        self.helper = self.add_variant("easycrypt/theories/Helper.ec", "require import OldLeaf.\n" + PROOF)
        self.acceptance = self.add_variant("easycrypt/proofs/GaussianAcceptanceActual.ec",
                                           "require import Helper.\n" + PROOF)
        self.attempt = self.add_variant("easycrypt/proofs/GaussianAttemptExpectation.ec",
                                        "require import GaussianAcceptanceActual.\n" + PROOF)
        self.other = self.add_variant("easycrypt/proofs/CheckedOther.ec")
        self.write_manifest()
        self.pins = {str(path.relative_to(self.root)): self.digest(path)
                     for path in (self.old_base, self.old_leaf, self.preserved)}
        (self.project / "baseline-lock.json").write_text(json.dumps({"commit": "fixture", "files": self.pins}))
        self.latest = self.project / "logs/latest.json"
        self.latest.write_text('{"historical":"keep this report"}\n')
        self.historical = self.latest.read_bytes()
        stack = ExitStack()
        self.addCleanup(stack.close)
        for name, value in (("PROJECT", self.project), ("ROOT", self.root), ("BASELINE", self.baseline)):
            stack.enter_context(patch.object(gate, name, value))
        stack.enter_context(patch.object(materialize, "ROOT", self.root))
        stack.enter_context(patch.object(materialize, "LOCK", self.project / "baseline-lock.json"))
        self.baseline_reads = stack.enter_context(patch.object(gate, "read_baseline", wraps=gate.read_baseline))

    @staticmethod
    def digest(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def add_variant(self, relative, content=PROOF):
        path = self.project / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        self.variants[relative] = path
        return path

    def write_manifest(self, entries=None):
        entries = sorted(self.variants) if entries is None else entries
        (self.project / "easycrypt/proof-targets.txt").write_text(
            "  # The complete variant inventory, including unselected files.\n" + "\n".join(entries) + "\n")

    def fake_run(self, command, **kwargs):
        self.commands.append(command)
        self.assertEqual(kwargs["cwd"], self.project)
        if command[:2] == ["bash", "scripts/verify-one.sh"]:
            target = Path(command[2])
            self.compiled.append(target)
            kwargs["stdout"].write("fixture main check\n")
            if self.mutate is not None:
                self.mutate(target)
            return subprocess.CompletedProcess(command, self.proof_exit)
        self.assertIn(command[1:], (["scripts/materialize.py", "--check"], ["scripts/extract.py", "--check"]))
        self.assertTrue(kwargs["check"])
        return subprocess.CompletedProcess(command, 0)

    def run_gate(self, group="gaussian-rate", *, default=False):
        args = [] if default else ["--group", group]
        with patch.object(gate.subprocess, "run", side_effect=self.fake_run), redirect_stdout(io.StringIO()):
            code = gate.main(args)
        report = json.loads((self.project / "logs" / f"latest-{group}.json").read_text())
        return code, report

    def test_default_all_preserves_api_and_latest_report(self):
        roots, closure = gate.proof_closure()
        self.assertEqual(set(roots), set(self.variants.values()))
        self.assertIn(self.old_base, closure)
        code, report = self.run_gate("all", default=True)
        self.assertEqual(code, 0, report)
        self.assertEqual(report["group"], "all")
        self.assertEqual(json.loads(self.latest.read_text()), report)
        self.assertEqual(set(self.compiled), set(closure))

    def test_focused_group_checks_full_closure_and_retains_provenance(self):
        code, report = self.run_gate()
        self.assertEqual(code, 0, report)
        self.assertEqual(self.compiled, [self.old_base, self.old_leaf, self.helper, self.acceptance, self.attempt])
        self.assertEqual(set(report["selected_roots"]),
                         {str(path.relative_to(self.root)) for path in (self.acceptance, self.attempt)})
        self.assertEqual(len(report["variant_inventory"]), 4)
        self.assertEqual(self.latest.read_bytes(), self.historical)
        self.assertFalse((self.project / "logs/latest-all.json").exists())
        self.assertEqual(self.baseline_reads.call_count, 2)
        self.assertEqual([command[1:] for command in self.commands[:2]],
                         [["scripts/materialize.py", "--check"], ["scripts/extract.py", "--check"]])
        self.assertFalse(report["hyperball_retry_termination"])
        self.assertEqual(report["retry_termination_scope"], "Hyperball rejection/retry loop")
        self.assertIn("iid", report["gaussian_candidate_retry_model"])
        self.assertFalse(report["concrete_shake_randomness"])
        self.assertIn("fresh extraction", report["generated_verification"])
        for relative in ("scripts/verify.py", "scripts/verify-one.sh", "easycrypt/proof-targets.txt"):
            key = str((self.project / relative).relative_to(self.root))
            self.assertEqual(report["control_sha256"][key], self.digest(self.project / relative))
        self.assertIn(str(self.other.relative_to(self.root)), report["source_sha256"])
        self.assertIn("variant/easycrypt/generated/HardenedHyperballTarget.ec", report["source_sha256"])
        self.assertNotIn(self.project / "easycrypt/generated/HardenedHyperballTarget.ec", self.compiled)

    def test_new_matching_roots_and_transitive_dependencies_are_discovered(self):
        future = self.add_variant("easycrypt/proofs/nested/GaussianAcceptanceFuture.ec", PROOF)
        counter = self.add_variant("easycrypt/theories/GaussianAttemptCountSpec.ec", "  require import Helper.\n" + PROOF)
        dependency = self.add_variant("easycrypt/theories/deep/DynamicDependency.ec", PROOF)
        self.acceptance.write_text("  require(* separator *)import Helper. require export DynamicDependency.\n" + PROOF)
        self.write_manifest()
        roots, closure = gate.proof_closure("gaussian-rate")
        self.assertEqual(set(roots), {self.acceptance, self.attempt, future, counter})
        self.assertIn(dependency, closure)
        self.assertLess(closure.index(dependency), closure.index(self.acceptance))
        self.assertLess(closure.index(self.old_base), closure.index(self.helper))
        self.assertEqual(len(closure), len(set(closure)))
        self.assertNotIn(self.other, closure)

    def test_omitted_group_root_is_rejected(self):
        self.add_variant("easycrypt/proofs/GaussianAttemptNew.ec")
        with self.assertRaisesRegex(ValueError, "manifest must cover every"):
            gate.proof_closure("gaussian-rate")

    def test_omitted_unselected_file_is_rejected(self):
        self.write_manifest([name for name in self.variants if name != "easycrypt/proofs/CheckedOther.ec"])
        with self.assertRaisesRegex(ValueError, "manifest must cover every"):
            gate.proof_closure("gaussian-rate")

    def test_extra_and_duplicate_manifest_entries_are_rejected(self):
        for entry, message in (("easycrypt/proofs/Absent.ec", "manifest must cover every"),
                               ("easycrypt/proofs/CheckedOther.ec", "Duplicate")):
            with self.subTest(entry=entry):
                self.write_manifest([*self.variants, entry])
                with self.assertRaisesRegex(ValueError, message):
                    gate.proof_closure("gaussian-rate")

    def test_escape_in_unselected_variant_is_rejected(self):
        for source in ("lemma bad : false. proof. admit. qed.\n",
                       "axiom(* separator *)unproved : false.\n",
                       "print(* separator *)goal 1.\n"):
            with self.subTest(source=source):
                self.other.write_text(source)
                with self.assertRaisesRegex(ValueError, "Proof escape|project axiom|Debug command"):
                    gate.proof_closure("gaussian-rate")

    def test_selected_dependency_cycle_is_rejected(self):
        self.helper.write_text("require import GaussianAcceptanceActual.\n" + PROOF)
        with self.assertRaisesRegex(ValueError, "Cyclic proof import"):
            gate.proof_closure("gaussian-rate")

    def test_ambiguous_namespace_is_rejected(self):
        self.add_variant("easycrypt/proofs/OldBase.ec")
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "Ambiguous proof namespace"):
            gate.proof_closure("gaussian-rate")

    def test_empty_or_unknown_group_is_rejected(self):
        self.acceptance.unlink()
        self.attempt.unlink()
        self.variants.pop("easycrypt/proofs/GaussianAcceptanceActual.ec")
        self.variants.pop("easycrypt/proofs/GaussianAttemptExpectation.ec")
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "No verification roots"):
            gate.proof_closure("gaussian-rate")
        with self.assertRaisesRegex(ValueError, "Unknown verification group"):
            gate.proof_closure("not-a-group")

    def test_guard_module_globals_are_restored(self):
        original_project = gate.baseline_gate.PROJECT
        original_comments = gate.baseline_gate.without_comments
        gate.proof_closure("gaussian-rate")
        self.assertEqual(gate.baseline_gate.PROJECT, original_project)
        self.assertIs(gate.baseline_gate.without_comments, original_comments)
        self.other.write_text("axiom escape : false.\n")
        with self.assertRaises(ValueError):
            gate.proof_closure("gaussian-rate")
        self.assertEqual(gate.baseline_gate.PROJECT, original_project)
        self.assertIs(gate.baseline_gate.without_comments, original_comments)

    def test_each_control_file_is_bound_during_proof_execution(self):
        for relative in ("scripts/verify.py", "scripts/verify-one.sh", "easycrypt/proof-targets.txt",
                         "scripts/materialize.py", "scripts/extract.py", "baseline-lock.json"):
            with self.subTest(relative=relative):
                target = self.project / relative
                original = target.read_bytes()
                self.compiled.clear()
                self.mutate = lambda _path: target.write_bytes(original + b"\n# concurrent change\n")
                code, report = self.run_gate()
                self.assertEqual(code, 1, report)
                self.assertIn("Source changed", report["error"])
                self.assertEqual(len(self.compiled), 1)
                self.assertEqual(self.latest.read_bytes(), self.historical)
                target.write_bytes(original)

    def test_unselected_source_change_is_rejected(self):
        self.mutate = lambda _path: self.other.write_text(PROOF + "lemma later : true by trivial.\n")
        code, report = self.run_gate()
        self.assertEqual(code, 1, report)
        self.assertIn("Source changed", report["error"])

    def test_generated_and_materialized_source_changes_are_rejected(self):
        for relative in ("easycrypt/generated/HardenedHyperballTarget.ec", "jasmin/checked.jazz"):
            with self.subTest(relative=relative):
                path = self.project / relative
                original = path.read_bytes()
                self.mutate = lambda _target: path.write_bytes(original + b"\n// changed\n")
                code, report = self.run_gate()
                self.assertEqual(code, 1, report)
                self.assertIn("Source changed", report["error"])
                path.write_bytes(original)

    def test_new_source_added_during_execution_is_rejected(self):
        self.mutate = lambda _path: self.add_variant("easycrypt/proofs/GaussianAttemptLate.ec")
        code, report = self.run_gate()
        self.assertEqual(code, 1, report)
        self.assertIn("manifest must cover every", report["error"])

    def test_array_namespace_drift_is_rejected_before_proof_execution(self):
        (self.project / "easycrypt/generated/BArray8.ec").write_text("different array theory\n")
        code, report = self.run_gate()
        self.assertEqual(code, 1, report)
        self.assertIn("Array namespace", report["error"])
        self.assertFalse(self.compiled)

    def test_original_baseline_checks_run_before_and_after_proofs(self):
        self.preserved.write_text("changed before verification\n")
        code, report = self.run_gate()
        self.assertEqual(code, 1, report)
        self.assertIn("Pinned baseline drift", report["error"])
        self.assertFalse(self.compiled)
        self.preserved.write_text("/* original implementation fixture */\n")
        self.mutate = lambda _path: self.preserved.write_text("changed during verification\n")
        code, report = self.run_gate()
        self.assertEqual(code, 1, report)
        self.assertIn("Pinned baseline drift", report["error"])
        self.assertTrue(self.compiled)

    def test_proof_failure_never_publishes_pass(self):
        self.proof_exit = 17
        code, report = self.run_gate()
        self.assertEqual(code, 1, report)
        self.assertEqual(report["result"], "FAIL")
        self.assertEqual(report["targets"][0]["exit_code"], 17)
        self.assertEqual(len(self.compiled), 1)
        self.assertEqual(self.latest.read_bytes(), self.historical)


if __name__ == "__main__":
    unittest.main()
