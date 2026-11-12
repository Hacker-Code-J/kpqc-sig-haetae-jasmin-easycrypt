#!/usr/bin/env python3
"""Publication prose may change without authorizing source or result rewrites."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

PROJECT = Path(__file__).resolve().parents[1]
ROOT = PROJECT.parent
spec = importlib.util.spec_from_file_location("materialize", PROJECT / "scripts/materialize.py")
materialize = importlib.util.module_from_spec(spec)
spec.loader.exec_module(materialize)


class PublicationMigrationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.lock = self.root / "baseline-lock.json"
        self.source = self.root / "README.md"
        self.original, self.renamed, self.published = b"historical readme", b"renamed readme", b"public readme"
        self.lock.write_text(json.dumps({"files": {"README.md": materialize.digest(self.original)}}))
        self.lock_bytes = self.lock.read_bytes()
        self.layout = self.root / "layout-migration.json"
        self.layout.write_text(json.dumps({"files": {"README.md": {
            "before_sha256": materialize.digest(self.original),
            "after_sha256": materialize.digest(self.renamed)}}}))
        self.publication = self.root / "publication-migration.json"
        self.files = {"README.md": {"before_sha256": materialize.digest(self.renamed),
                                    "after_sha256": materialize.digest(self.published)}}
        self.source.write_bytes(self.published)
        for key, value in (("ROOT", self.root), ("LOCK", self.lock),
                           ("LAYOUT_SHA256", materialize.digest(self.layout.read_bytes()))):
            patcher = patch.object(materialize, key, value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def check(self):
        self.publication.write_text(json.dumps({"files": self.files}))
        with patch.object(materialize, "PUBLICATION_SHA256", materialize.digest(self.publication.read_bytes())):
            return materialize.read_baseline()

    def test_exact_document_transition_follows_layout_without_rewriting_history(self):
        self.assertEqual(self.check()[1]["README.md"], self.published)
        self.assertEqual(self.lock.read_bytes(), self.lock_bytes)

    def test_unreviewed_bytes_and_wrong_prior_hash_are_rejected(self):
        self.source.write_bytes(self.published + b"unreviewed")
        with self.assertRaisesRegex(SystemExit, "baseline drift"):
            self.check()
        self.source.write_bytes(self.published)
        self.files["README.md"]["before_sha256"] = "0" * 64
        with self.assertRaisesRegex(SystemExit, "baseline drift"):
            self.check()

    def test_publication_cannot_authorize_proof_production_or_historical_results(self):
        for name in ("haetae-easycrypt/proofs/Proof.ec", "haetae-jasmin/jasmin/sign.jazz",
                     "haetae-easycrypt/manifests/verification-results.json",
                     "haetae-easycrypt/manifests/history/2026.03/README.md",
                     "haetae-easycrypt/proofs/README.md", "haetae-easycrypt/unreviewed.md",
                     "archive/legacy/haetae-topdown-easycrypt/logs/verify-all-summary.txt",
                     "archive/legacy/haetae-topdown-easycrypt/algebraist-guide/references.bib",
                     "../README.md"):
            with self.subTest(name=name):
                self.files[name] = self.files["README.md"]
                with self.assertRaisesRegex(SystemExit, "publication document"):
                    self.check()
                del self.files[name]

    def test_changed_publication_ledger_is_rejected(self):
        self.check()
        expected = materialize.digest(self.publication.read_bytes())
        self.publication.write_bytes(self.publication.read_bytes() + b"\n")
        with patch.object(materialize, "PUBLICATION_SHA256", expected):
            with self.assertRaisesRegex(SystemExit, "publication migration"):
                materialize.read_baseline()


class PublicationSnapshotTests(unittest.TestCase):
    def test_current_publication_snapshot_materializes(self):
        _, files = materialize.read_baseline()
        for name in sorted(materialize.PUBLICATION_DOCUMENTS - {"README.md"}):
            with self.subTest(document=name):
                self.assertEqual(files[name], (ROOT / name).read_bytes())

    def test_further_readme_drift_is_rejected(self):
        read_bytes = Path.read_bytes
        for name in sorted(materialize.PUBLICATION_DOCUMENTS - {"README.md"}):
            document = ROOT / name

            def altered_bytes(path):
                data = read_bytes(path)
                return data + b"\nUnreviewed change.\n" if path == document else data

            with self.subTest(document=name), patch.object(Path, "read_bytes", altered_bytes):
                with self.assertRaisesRegex(SystemExit, "Pinned baseline drift:"):
                    materialize.read_baseline()


if __name__ == "__main__":
    unittest.main()
