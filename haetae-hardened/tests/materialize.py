#!/usr/bin/env python3
"""Guard against writing through links, baseline drift, and ambiguous overlays."""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

PROJECT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("hardened_materialize", PROJECT / "scripts/materialize.py")
materialize = importlib.util.module_from_spec(spec)
spec.loader.exec_module(materialize)


class MaterializationTests(unittest.TestCase):
    def test_parent_symlink_cannot_write_into_baseline(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "variant"
            baseline = root / "original"
            project.mkdir()
            baseline.mkdir()
            original = baseline / "phase.jinc"
            original.write_text("preserved\n")
            (project / "jasmin").symlink_to(baseline, target_is_directory=True)
            outputs = {"build/early.txt": b"must not write", "jasmin/phase.jinc": b"overlay"}
            with patch.object(materialize, "PROJECT", project), \
                 patch.object(materialize, "desired_outputs", return_value=outputs), \
                 patch("sys.argv", ["materialize.py"]):
                with self.assertRaisesRegex(SystemExit, "Symbolic"):
                    materialize.main()
            self.assertEqual(original.read_text(), "preserved\n")
            self.assertFalse((project / "build/early.txt").exists())

    def test_leaf_symlink_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            project = Path(temp)
            (project / "a").symlink_to(project / "missing")
            with patch.object(materialize, "PROJECT", project):
                with self.assertRaisesRegex(SystemExit, "Symbolic"):
                    materialize.safe_target("a")

    def test_absolute_and_parent_paths_rejected(self):
        for path in ("../old/file", "/tmp/unrelated-file"):
            with self.assertRaisesRegex(SystemExit, "Invalid"):
                materialize.safe_target(path)

    def test_duplicate_or_missing_function_rejected(self):
        function = "fn checked() {\n}\n"
        for source in ("", function + function):
            with self.assertRaisesRegex(SystemExit, "Expected one"):
                materialize.replace_function(source, function, "checked")

    def test_baseline_drift_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "source").write_bytes(b"modified")
            lock = root / "lock.json"
            lock.write_text(json.dumps({"files": {"source": hashlib.sha256(b"original").hexdigest()}}))
            with patch.object(materialize, "ROOT", root), patch.object(materialize, "LOCK", lock):
                with self.assertRaisesRegex(SystemExit, "baseline drift"):
                    materialize.read_baseline()

    def test_matching_baseline_rejects_internal_and_external_parent_symlinks(self):
        for external in (False, True):
            with self.subTest(external=external), tempfile.TemporaryDirectory() as temp:
                root = Path(temp) / "root"
                root.mkdir()
                original = (Path(temp) if external else root) / "real-sources"
                original.mkdir()
                (original / "source.jazz").write_bytes(b"pinned production")
                (root / "sources").symlink_to(original, target_is_directory=True)
                lock = root / "baseline-lock.json"
                lock.write_text(json.dumps({"files": {
                    "sources/source.jazz": materialize.digest(b"pinned production")}}))
                with patch.object(materialize, "ROOT", root), patch.object(materialize, "LOCK", lock):
                    with self.assertRaisesRegex(SystemExit, "Symbolic baseline input path"):
                        materialize.read_baseline()


class ToolchainMigrationTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.name = "haetae-easycrypt/generated/Target.ec"
        self.path = self.root / self.name
        self.path.parent.mkdir(parents=True)
        self.path.write_bytes(b"new extraction")
        self.lock = self.root / "baseline-lock.json"
        self.old_hash = materialize.digest(b"old extraction")
        self.lock.write_text(json.dumps({"commit": "baseline", "files": {self.name: self.old_hash}}))
        self.lock_bytes = self.lock.read_bytes()
        self.migration = self.root / "toolchain-migration-lock.json"
        self.entries = {self.name: {"baseline_sha256": self.old_hash,
                                   "migrated_sha256": materialize.digest(self.path.read_bytes())}}
        self.write_migration()
        for key, value in (("ROOT", self.root), ("LOCK", self.lock)):
            patcher = patch.object(materialize, key, value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def write_migration(self):
        self.migration.write_text(json.dumps({"baseline_commit": "baseline",
            "baseline_lock_sha256": materialize.digest(self.lock.read_bytes()), "files": self.entries}))

    def test_explicit_migration_keeps_historical_lock(self):
        lock, sources = materialize.read_baseline()
        self.assertEqual(lock["files"][self.name], self.old_hash)
        self.assertEqual(sources[self.name], b"new extraction")
        self.assertEqual(self.lock.read_bytes(), self.lock_bytes)

    def test_changed_migrated_file_and_missing_file_rejected(self):
        self.path.write_bytes(b"unrecorded change")
        with self.assertRaisesRegex(SystemExit, "baseline drift"):
            materialize.read_baseline()
        self.path.unlink()
        with self.assertRaisesRegex(SystemExit, "inventory drift"):
            materialize.read_baseline()

    def test_old_hash_and_lock_binding_cannot_be_rewritten(self):
        self.entries[self.name]["baseline_sha256"] = "0" * 64
        self.write_migration()
        with self.assertRaisesRegex(SystemExit, "migration hash"):
            materialize.read_baseline()
        self.lock.write_bytes(self.lock_bytes + b"\n")
        with self.assertRaisesRegex(SystemExit, "historical baseline lock"):
            materialize.read_baseline()

    def test_explicit_deletion_rejects_reappearance(self):
        self.entries[self.name]["migrated_sha256"] = None
        self.path.unlink()
        self.write_migration()
        self.assertEqual(materialize.read_baseline()[1], {})
        self.path.write_bytes(b"reappeared")
        with self.assertRaisesRegex(SystemExit, "inventory drift"):
            materialize.read_baseline()

    def test_explicit_addition_and_unlisted_addition(self):
        added = "haetae-easycrypt/generated/support/Array5.ec"
        path = self.root / added
        path.parent.mkdir()
        path.write_bytes(b"support array")
        with self.assertRaisesRegex(SystemExit, "inventory drift"):
            materialize.read_baseline()
        self.entries[added] = {"baseline_sha256": None,
                               "migrated_sha256": materialize.digest(path.read_bytes())}
        self.write_migration()
        self.assertEqual(materialize.read_baseline()[1][added], b"support array")
        path.write_bytes(b"changed array")
        with self.assertRaisesRegex(SystemExit, "baseline drift"):
            materialize.read_baseline()

    def test_production_proof_archive_and_escaping_overrides_rejected(self):
        for name in ("haetae-jasmin/jasmin/sign.jazz", "archive/legacy/old.ec",
                     "HAETAE/reference_implementation/sign.c",
                     "haetae-easycrypt/proofs/Proof.ec",
                     "haetae-easycrypt/theories/Spec.ec",
                     "haetae-easycrypt/generated/../../../escaped.ec", "/tmp/escaped.ec"):
            with self.subTest(name=name):
                self.entries[name] = {"baseline_sha256": None, "migrated_sha256": "1" * 64}
                self.write_migration()
                with self.assertRaisesRegex(SystemExit, "Invalid toolchain|cannot replace"):
                    materialize.read_baseline()
                del self.entries[name]

    def test_unlisted_production_change_still_fails(self):
        production = "haetae-jasmin/jasmin/sign.jazz"
        path = self.root / production
        path.parent.mkdir(parents=True)
        path.write_bytes(b"modified production")
        lock = json.loads(self.lock.read_text())
        lock["files"][production] = materialize.digest(b"pinned production")
        self.lock.write_text(json.dumps(lock))
        self.write_migration()
        with self.assertRaisesRegex(SystemExit, "baseline drift"):
            materialize.read_baseline()

    def test_historical_pass_change_rejected_even_with_matching_migration_hash(self):
        name = "haetae-easycrypt/manifests/verification-results.json"
        path = self.root / name
        path.parent.mkdir()
        original = b'{"result":"PASS","checked_at":"historical"}\n'
        path.write_bytes(b'{"result":"PASS","checked_at":"forged-new-run"}\n')
        lock = json.loads(self.lock.read_text())
        lock["files"][name] = materialize.digest(original)
        self.lock.write_text(json.dumps(lock))
        self.entries[name] = {"baseline_sha256": materialize.digest(original),
                              "migrated_sha256": materialize.digest(path.read_bytes())}
        self.write_migration()
        with self.assertRaisesRegex(SystemExit, "historical records"):
            materialize.read_baseline()

    def test_historical_copy_must_equal_the_original_pinned_record(self):
        name = "haetae-easycrypt/manifests/verification-results.json"
        copy = "haetae-easycrypt/manifests/history/2026.03/verification-results.json"
        original = self.root / name
        original.parent.mkdir()
        original.write_bytes(b'{"result":"PASS","checked_at":"historical"}\n')
        lock = json.loads(self.lock.read_text())
        lock["files"][name] = materialize.digest(original.read_bytes())
        self.lock.write_text(json.dumps(lock))
        target = self.root / copy
        target.parent.mkdir(parents=True)
        target.write_bytes(original.read_bytes())
        self.entries[copy] = {"baseline_sha256": None,
                              "migrated_sha256": materialize.digest(target.read_bytes())}
        self.write_migration()
        self.assertEqual(materialize.read_baseline()[1][copy], original.read_bytes())
        target.write_bytes(b'{"result":"PASS","checked_at":"forged-new-run"}\n')
        self.entries[copy]["migrated_sha256"] = materialize.digest(target.read_bytes())
        self.write_migration()
        with self.assertRaisesRegex(SystemExit, "Historical copy must match"):
            materialize.read_baseline()

    def test_unlisted_verification_metadata_is_not_migratable(self):
        for tail in ("scripts/unlisted_verify.py", "tests/test_verification_gate.py", "docs/result.md",
                     "manifests/new-results.json"):
            with self.subTest(tail=tail):
                name = "haetae-easycrypt/" + tail
                self.entries[name] = {"baseline_sha256": None, "migrated_sha256": "1" * 64}
                self.write_migration()
                with self.assertRaisesRegex(SystemExit, "historical records"):
                    materialize.read_baseline()
                del self.entries[name]

    def test_ntt_additions_require_exact_reviewed_paths_and_bytes(self):
        for tail, expected in materialize.NTT_ADDITIONS.items():
            with self.subTest(tail=tail):
                name = "haetae-easycrypt/" + tail
                path = self.root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                content = (PROJECT.parent / name).read_bytes()
                self.assertEqual(materialize.digest(content), expected)
                path.write_bytes(content)
                self.entries[name] = {"baseline_sha256": None, "migrated_sha256": expected}
                self.write_migration()
                self.assertEqual(materialize.read_baseline()[1][name], content)
                changed = content + b"\n(* unreviewed NTT extension *)\n"
                path.write_bytes(changed)
                self.entries[name]["migrated_sha256"] = materialize.digest(changed)
                self.write_migration()
                with self.assertRaisesRegex(SystemExit, "exact reviewed hash pair"):
                    materialize.read_baseline()
                path.write_bytes(content)
                del self.entries[name]

    def test_ntt_additions_cannot_replace_existing_baseline_proofs(self):
        tail, expected = next(iter(materialize.NTT_ADDITIONS.items()))
        name = "haetae-easycrypt/" + tail
        lock = json.loads(self.lock.read_text())
        lock["files"][name] = "0" * 64
        self.lock.write_text(json.dumps(lock))
        self.entries[name] = {"baseline_sha256": "0" * 64, "migrated_sha256": expected}
        self.write_migration()
        with self.assertRaisesRegex(SystemExit, "exact reviewed hash pair"):
            materialize.read_baseline()

    def prepare_reviewed_proof_port(self, tail="proofs/ApiBoundaryCorrectness.ec"):
        name = "haetae-easycrypt/" + tail
        old, new = {**materialize.PROOF_PORTS, **materialize.MODEL_IMPORTS,
                    **materialize.CONTROL_PORTS}[tail]
        content = (PROJECT.parent / name).read_bytes()
        self.assertEqual(materialize.digest(content), new)
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        lock = json.loads(self.lock.read_text())
        lock["files"][name] = old
        self.lock.write_text(json.dumps(lock))
        self.entries[name] = {"baseline_sha256": old, "migrated_sha256": new}
        self.write_migration()
        return name, path

    def test_exact_reviewed_proof_port_is_accepted(self):
        for tail in (*materialize.PROOF_PORTS, *materialize.MODEL_IMPORTS,
                     *materialize.CONTROL_PORTS):
            with self.subTest(tail=tail):
                name, path = self.prepare_reviewed_proof_port(tail)
                self.assertEqual(materialize.read_baseline()[1][name], path.read_bytes())

    def test_ported_theorem_change_rejected_even_with_matching_ledger(self):
        for tail in (*materialize.PROOF_PORTS, *materialize.MODEL_IMPORTS,
                     *materialize.CONTROL_PORTS):
            with self.subTest(tail=tail):
                name, path = self.prepare_reviewed_proof_port(tail)
                original = path.read_bytes()
                if tail in materialize.MODEL_IMPORTS:
                    changed = original.replace(b"JModel_x86", b"JModel_ARM", 1)
                elif tail in materialize.CONTROL_PORTS:
                    changed = original + b"\n# unapproved control modification\n"
                else:
                    changed = original.replace(b"lemma ", b"lemma changed_", 1)
                self.assertNotEqual(changed, original)
                path.write_bytes(changed)
                self.entries[name]["migrated_sha256"] = materialize.digest(changed)
                self.write_migration()
                with self.assertRaisesRegex(SystemExit, "exact reviewed hash pair"):
                    materialize.read_baseline()
                path.write_bytes(original)
                self.entries[name]["migrated_sha256"] = materialize.digest(original)

    def test_other_proof_cannot_reuse_approved_port_hashes(self):
        for tail, unlisted in (("proofs/ApiBoundaryCorrectness.ec", "proofs/OtherProof.ec"),
                               ("theories/ntt/Fq.ec", "theories/ntt/OtherModel.ec"),
                               ("scripts/verify.py", "scripts/other_verify.py")):
            with self.subTest(tail=tail):
                name, _ = self.prepare_reviewed_proof_port(tail)
                other = "haetae-easycrypt/" + unlisted
                self.entries[other] = dict(self.entries[name])
                self.write_migration()
                with self.assertRaisesRegex(SystemExit, "cannot replace"):
                    materialize.read_baseline()
                del self.entries[other]

    def test_reviewed_hashes_do_not_allow_unrecorded_proof_bytes(self):
        for tail in (*materialize.PROOF_PORTS, *materialize.MODEL_IMPORTS,
                     *materialize.CONTROL_PORTS):
            with self.subTest(tail=tail):
                _, path = self.prepare_reviewed_proof_port(tail)
                original = path.read_bytes()
                path.write_bytes(original + b"\n(* unrecorded modification *)\n")
                with self.assertRaisesRegex(SystemExit, "Pinned baseline drift"):
                    materialize.read_baseline()
                path.write_bytes(original)

    def test_symbolic_migration_lock_is_rejected(self):
        content = self.migration.read_bytes()
        self.migration.unlink()
        target = self.root / "other.json"
        target.write_bytes(content)
        self.migration.symlink_to(target)
        with self.assertRaisesRegex(SystemExit, "Symbolic baseline input path"):
            materialize.read_baseline()


if __name__ == "__main__":
    unittest.main()
