#!/usr/bin/env python3
"""Check the selected CT checker, including overrides, before reproducing claims."""
from contextlib import redirect_stdout
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("environment_check", ROOT / "env/check.py")
environment = importlib.util.module_from_spec(spec)
spec.loader.exec_module(environment)


class EnvironmentTests(unittest.TestCase):
    def check_fixture(self, *, version="2026.09.0", override=False, missing=False,
                      socket_error=None):
        with tempfile.TemporaryDirectory() as directory:
            prefix = Path(directory)
            binary_dir = prefix / "bin"
            binary_dir.mkdir()
            versions = {"jasminc": "2026.09.0", "jasmin2ec": "2026.09.0", "jasmin-ct": version,
                        "why3": "1.8.2", "alt-ergo": "2.6.0", "cvc4": "1.8", "cvc5": "1.2.1", "z3": "4.12.6"}
            tools = set(versions) | {"make", "cc", "cmake", "sha256sum", "python3", "opam", "easycrypt"}
            for name in tools:
                (binary_dir / name).write_text("fixture " + name)
            alternate = prefix / "selected-ct"
            alternate.write_text("explicitly selected CT checker")
            selected = str(alternate) if override else "jasmin-ct"
            expected_hash = hashlib.sha256((alternate if override else binary_dir / "jasmin-ct").read_bytes()).hexdigest()
            calls = []

            def which(command):
                if command == selected and missing:
                    return None
                if command == str(alternate):
                    return str(alternate)
                return str(binary_dir / command) if command in tools else None

            def run(command, **kwargs):
                calls.append(command)
                name = command[0]
                if name == selected:
                    output = "Jasmin Compiler " + version if version is not None else ""
                elif name in versions:
                    output = versions[name]
                elif name == "easycrypt":
                    output = ("Jasmin@/fixture/models\nknown provers: Alt-Ergo@2.6.0, "
                              "CVC4@1.8.0, CVC5@1.2.1, Z3@4.12.6\n")
                elif command == ["opam", "var", "prefix"]:
                    output = str(prefix)
                else:
                    output = "ocaml 5.4.0\neasycrypt 2026.09\njasmin 2026.09.0\nwhy3 1.8.2\n"
                return subprocess.CompletedProcess(command, 0, stdout=output, stderr="")

            output = io.StringIO()
            settings = {"JASMIN_CT": selected} if override else {}
            with patch.dict(environment.os.environ, settings, clear=True), \
                    patch.object(environment.shutil, "which", side_effect=which), \
                    patch.object(environment.subprocess, "run", side_effect=run), \
                    patch.object(environment.platform, "system", return_value="Linux"), \
                    patch.object(environment.platform, "machine", return_value="x86_64"), \
                    patch.object(environment.socket, "socket") as socket_factory, redirect_stdout(output):
                socket_factory.return_value.__enter__.return_value.bind.side_effect = socket_error
                status = environment.main()
            return status, json.loads(output.getvalue()), calls, selected, expected_hash

    def test_ct_checker_is_versioned_and_hashed(self):
        status, report, calls, selected, expected_hash = self.check_fixture()
        self.assertFalse(status, report)
        self.assertIn([selected, "--version"], calls)
        self.assertEqual(report["tools"]["jasmin-ct"]["sha256"], expected_hash)

    def test_override_is_the_checker_actually_checked(self):
        status, report, calls, selected, expected_hash = self.check_fixture(override=True)
        self.assertFalse(status, report)
        self.assertIn([selected, "--version"], calls)
        self.assertNotIn(["jasmin-ct", "--version"], calls)
        self.assertEqual(report["tools"]["jasmin-ct"]["sha256"], expected_hash)

    def test_wrong_version_override_is_rejected(self):
        status, report, _, _, _ = self.check_fixture(version="2026.03.0", override=True)
        self.assertTrue(status)
        self.assertTrue(any("Expected jasmin-ct 2026.09.0" in error for error in report["errors"]))

    def test_missing_override_does_not_fall_back_to_default(self):
        status, report, calls, _, _ = self.check_fixture(override=True, missing=True)
        self.assertTrue(status)
        self.assertTrue(any("Missing jasmin-ct" in error for error in report["errors"]))
        self.assertNotIn(["jasmin-ct", "--version"], calls)

    def test_success_exit_without_version_is_rejected(self):
        status, report, _, _, _ = self.check_fixture(version=None, override=True)
        self.assertTrue(status)
        self.assertTrue(any("Expected jasmin-ct 2026.09.0" in error for error in report["errors"]))

    def test_local_socket_support_is_reported(self):
        status, report, _, _, _ = self.check_fixture()
        self.assertFalse(status, report)
        self.assertEqual(report["local_unix_socket"], "PASS")

    def test_denied_local_socket_fails_environment_check(self):
        status, report, _, _, _ = self.check_fixture(
            socket_error=PermissionError(1, "Operation not permitted"))
        self.assertTrue(status)
        self.assertEqual(report["local_unix_socket"], "FAIL")
        self.assertTrue(any("EasyCrypt requires local Unix sockets" in error
                            and "Operation not permitted" in error
                            for error in report["errors"]))


if __name__ == "__main__":
    unittest.main()
