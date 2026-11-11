#!/usr/bin/env python3
"""Regression tests for complete EasyCrypt proof checking at end of file."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


PROJECT = Path(__file__).resolve().parents[1]
RUNNER = PROJECT / "scripts" / "verify-one.sh"
PRELUDE = "require import AllCore.\n"


class VerificationGateTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="haetae120-gate-test-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.source = self.root / "GateFixture.ec"
        self.environment = os.environ.copy()
        self.environment.pop("WHY3_SERVER_SOCKET", None)
        self.environment["EC_TIMEOUT"] = "2"
        self.environment["EC_MAX_PROVERS"] = "1"

    def run_source(self, text, *, environment=None):
        self.source.write_text(text)
        result = subprocess.run(
            ["bash", str(RUNNER), str(self.source)],
            cwd=PROJECT,
            env=environment or self.environment,
            text=True,
            capture_output=True,
            timeout=60,
        )
        self.assertEqual(self.source.read_text(), text, "runner modified the input")
        return result

    def assert_compiles(self, source):
        result = self.run_source(source)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def assert_rejected(self, source):
        result = self.run_source(source)
        self.assertNotEqual(result.returncode, 0, "incomplete source was accepted")

    def test_closed_theory_and_inline_proof(self):
        self.assert_compiles(PRELUDE + """
theory Closed.
lemma checked : true.
proof. trivial. qed.
end Closed.
lemma outside : true by exact Closed.checked.
""")

    def test_closed_clone_and_proof_without_proof_keyword(self):
        self.assert_compiles(PRELUDE + """
theory Dummy.
axiom checked : true.
end Dummy.
clone Dummy as Cloned proof checked by trivial.
lemma no_keyword : true.
trivial.
qed.
""")

    def test_closed_realize_obligation(self):
        self.assert_compiles(PRELUDE + """
require Subtype.
subtype small = { x : int | 0 <= x < 3 }.
realize inhabited. by exists 0. qed.
""")

    def test_source_directory_import_still_resolves(self):
        (self.root / "GateDependency.ec").write_text(
            PRELUDE + "lemma ready : true by trivial.\n"
        )
        self.assert_compiles(PRELUDE + """
require import GateDependency.
lemma checked : true by exact GateDependency.ready.
""")

    def test_pending_false_goal_at_eof_is_rejected(self):
        self.assert_rejected(PRELUDE + "lemma pending : false.\nproof.\n")

    def test_solved_proof_without_qed_is_rejected(self):
        self.assert_rejected(PRELUDE + "lemma pending : true.\nproof. trivial.\n")

    def test_bare_lemma_at_eof_is_rejected(self):
        self.assert_rejected(PRELUDE + "lemma pending : false.\n")

    def test_pending_clone_obligation_at_eof_is_rejected(self):
        self.assert_rejected(PRELUDE + """
theory Dummy.
axiom unchecked : false.
end Dummy.
clone Dummy as Cloned proof *.
""")

    def test_truncated_command_is_rejected(self):
        self.assert_rejected(PRELUDE + "lemma unfinished :")

    def test_snapshot_basename_cleanup_and_compiler_exit_status(self):
        compiler = self.root / "compiler-probe"
        capture = self.root / "capture.json"
        compiler.write_text("""#!/usr/bin/env python3
import json
import os
from pathlib import Path
import sys

source = next(Path(arg) for arg in sys.argv[1:] if arg.endswith('.ec'))
Path(os.environ['GATE_CAPTURE']).write_text(json.dumps({
    'source': str(source), 'text': source.read_text(), 'args': sys.argv[1:],
}))
sys.exit(int(os.environ['GATE_EXIT']))
""")
        compiler.chmod(0o755)
        environment = self.environment | {
            "EASYCRYPT": str(compiler), "GATE_CAPTURE": str(capture)
        }
        source_text = PRELUDE + "lemma checked : true by trivial.\n"
        for status in (0, 17):
            with self.subTest(compiler_exit=status):
                environment["GATE_EXIT"] = str(status)
                result = self.run_source(source_text, environment=environment)
                self.assertEqual(result.returncode, status, result.stderr)
                observed = json.loads(capture.read_text())
                snapshot = Path(observed["source"])
                self.assertEqual(snapshot.name, self.source.name)
                self.assertNotEqual(snapshot, self.source)
                self.assertTrue(observed["text"].startswith(source_text))
                self.assertFalse(snapshot.exists(), "temporary source leaked")
                self.assertFalse(snapshot.parent.exists(), "temporary directory leaked")
                self.assertIn("-no-eco", observed["args"])
                self.assertIn("Proofs:check", observed["args"])


if __name__ == "__main__":
    if not shutil.which(os.environ.get("EASYCRYPT", "easycrypt")):
        raise SystemExit("EasyCrypt is required for the verification gate regression tests")
    unittest.main()
