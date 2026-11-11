"""Reject altered historical evidence and unsafe index paths."""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "check_evidence", Path(__file__).resolve().parents[1] / "scripts/check-evidence.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        source = b"lemma closed : true by trivial.\n"
        summary = {"status": "PASS", "total": 1, "passed": 1, "failed": 0, "targets": {
            "fixture": {"id": "fixture", "group": "original", "status": "PASS", "exit_code": 0,
                        "source_sha256": hashlib.sha256(source).hexdigest(),
                        "command": ["check", "/historical/source.ec"], "log": "/historical/check.log"}}}
        result = {"status": "PASS", "primary_targets": 1, "groups": {"original": 1}}
        blobs = {"source.ec": source, "check.log": b"checked\n",
                 "summary.json": json.dumps(summary).encode(), "result.json": json.dumps(result).encode()}
        rows = []
        for name, data in blobs.items():
            (self.root / name).write_bytes(data)
            rows.append({"path": name, "original_path": "/historical/" + name,
                         "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()})
        anchors = {key: {"path": name, "sha256": hashlib.sha256(blobs[name]).hexdigest()}
                   for key, name in (("summary", "summary.json"), ("validation_record", "result.json"))}
        self.index = {"schema_version": 1, "historical_primary_targets": {"original": 1},
                      "anchors": anchors, "files": rows}
        self.manifest = {"full_replay": json.loads(json.dumps(anchors))}
        self.write_index()

    def write_index(self):
        (self.root / "index.json").write_text(json.dumps(self.index))

    def test_complete_evidence_passes(self):
        self.assertEqual(checker.check_evidence(self.root, self.manifest), (4, 1))

    def test_source_change_is_rejected_even_with_new_index_hash(self):
        data = b"axiom escape : false.\n"
        (self.root / "source.ec").write_bytes(data)
        with self.assertRaisesRegex(ValueError, "hash or size mismatch"):
            checker.check_evidence(self.root, self.manifest)
        row = self.index["files"][0]
        row.update(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
        self.write_index()
        with self.assertRaisesRegex(ValueError, "checked source mismatch"):
            checker.check_evidence(self.root, self.manifest)

    def test_missing_final_log_and_duplicate_path_are_rejected(self):
        self.index["files"] = [row for row in self.index["files"] if row["path"] != "check.log"]
        self.write_index()
        with self.assertRaisesRegex(ValueError, "Missing final historical log"):
            checker.check_evidence(self.root, self.manifest)
        self.index["files"].append(self.index["files"][0])
        self.write_index()
        with self.assertRaisesRegex(ValueError, "Duplicate evidence path"):
            checker.check_evidence(self.root, self.manifest)

    def test_anchor_cannot_be_replaced_in_index(self):
        self.index["anchors"]["summary"] = {"path": "result.json", "sha256": "0" * 64}
        self.write_index()
        with self.assertRaisesRegex(ValueError, "anchor mismatch"):
            checker.check_evidence(self.root, self.manifest)

    def test_path_escape_and_symlink_are_rejected(self):
        for name in ("../outside", "/tmp/outside"):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "Invalid evidence path"):
                checker.safe_file(self.root, name)
        (self.root / "linked.ec").symlink_to(self.root / "source.ec")
        with self.assertRaisesRegex(ValueError, "Symbolic evidence path"):
            checker.safe_file(self.root, "linked.ec")


if __name__ == "__main__":
    unittest.main()
