#!/usr/bin/env python3
"""Check the selected CT checker, including overrides, before reproducing claims."""
from contextlib import redirect_stdout
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
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


class BootstrapPrerequisiteTests(unittest.TestCase):
    def bootstrap_fixture(self, release, package_status="missing", args=()):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            env_dir, binary_dir, modules = (root / name for name in
                                            ("env", "bin", "modules"))
            for path in (env_dir, binary_dir, modules):
                path.mkdir()
            script = env_dir / "bootstrap.sh"
            script.write_bytes((ROOT / "env/bootstrap.sh").read_bytes())
            (env_dir / "opam-switch.export").write_bytes(
                (ROOT / "env/opam-switch.export").read_bytes())
            calls = root / "calls"
            for command in ("git", "make", "cc", "c++", "wget", "unzip", "cvc4"):
                path = binary_dir / command
                path.write_text("#!/bin/sh\nexit 0\n")
                path.chmod(0o755)
            programs = {
                "python3": "exec " + shlex.quote(sys.executable) + ' "$@"\n',
                "uname": ('case "$1" in -s) echo Linux;; '
                          '-m) echo x86_64;; *) exit 1;; esac\n'),
                "dpkg-query": (
                    'echo dpkg-query >> "$BOOTSTRAP_CALLS"\n'
                    '[ "$BOOTSTRAP_PACKAGE_STATUS" != missing ] || exit 1\n'
                    'printf %s "$BOOTSTRAP_PACKAGE_STATUS"\n'),
                "opam": (
                    'printf "opam %s\\n" "$*" >> "$BOOTSTRAP_CALLS"\n'
                    'if [ "$1 $2" = "switch import" ]; then\n'
                    '  [ -f "$3" ] || exit 89\n'
                    'fi\n'
                    '[ "$1 $2" != "switch create" ] || exit 97\n'
                    'exit 0\n'),
            }
            for name, body in programs.items():
                path = binary_dir / name
                path.write_text("#!/bin/sh\n" + body)
                path.chmod(0o755)
            action = ("raise OSError('release metadata unavailable')" if release is None
                      else "return " + repr(release))
            (modules / "platform.py").write_text(
                "def freedesktop_os_release():\n    " + action + "\n")
            settings = {**os.environ, "PATH": str(binary_dir) + os.pathsep + os.defpath,
                        "PYTHONPATH": str(modules), "PYTHONDONTWRITEBYTECODE": "1",
                        "BOOTSTRAP_CALLS": str(calls),
                        "BOOTSTRAP_PACKAGE_STATUS": package_status}
            process = subprocess.run(["bash", str(script), *args], cwd=root,
                                     env=settings, capture_output=True, text=True)
            return (process, calls.read_text() if calls.exists() else "",
                    (env_dir / "downloads").exists())

    def test_missing_debian_package_fails_before_environment_mutation(self):
        for release in ({"ID": "ubuntu", "ID_LIKE": "debian"},
                        {"ID": "debian"},
                        {"ID": "linuxmint", "ID_LIKE": "ubuntu debian"}):
            with self.subTest(release=release):
                process, calls, created = self.bootstrap_fixture(release)
                self.assertEqual(process.returncode, 2)
                self.assertIn("python3-distutils", process.stderr)
                self.assertIn("Ubuntu 22.04", process.stderr)
                self.assertNotIn("opam ", calls)
                self.assertFalse(created)

    def test_installed_package_reaches_unchanged_exact_prover_versions(self):
        process, calls, _ = self.bootstrap_fixture(
            {"ID": "ubuntu", "ID_LIKE": "debian"}, "installed")
        self.assertEqual(process.returncode, 97)  # Fixture stops before real installation.
        self.assertIn("--packages=ocaml-base-compiler.5.2.1,alt-ergo.2.6.0,z3.4.12.6",
                      calls)

    def test_non_debian_or_unidentified_hosts_skip_debian_package_gate(self):
        for release in ({"ID": "fedora", "ID_LIKE": "rhel"}, None):
            with self.subTest(release=release):
                process, calls, _ = self.bootstrap_fixture(release)
                self.assertEqual(process.returncode, 97)
                self.assertNotIn("dpkg-query", calls)

    def test_help_remains_nonmutating(self):
        process, calls, created = self.bootstrap_fixture(
            {"ID": "ubuntu", "ID_LIKE": "debian"}, args=("--help",))
        self.assertEqual(process.returncode, 0)
        self.assertFalse(calls)
        self.assertFalse(created)

    def test_ci_baseline_installs_the_registered_system_dependency(self):
        workflow = (ROOT / ".github/workflows/reproduce.yml").read_text()
        self.assertIn("runs-on: ubuntu-22.04", workflow)
        self.assertIn("python3 python3-distutils", workflow)


if __name__ == "__main__":
    unittest.main()
