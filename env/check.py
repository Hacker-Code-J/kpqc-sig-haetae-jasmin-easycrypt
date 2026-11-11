#!/usr/bin/env python3
"""Check the supported proof toolchain without changing its configuration."""
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import socket
import subprocess
import sys
import tempfile


def main():
    errors, tools = [], {}
    if (platform.system(), platform.machine()) != ("Linux", "x86_64"):
        errors.append("Supported platform is Linux x86-64")
    local_socket = "PASS"
    try:
        with tempfile.TemporaryDirectory(prefix="haetae-socket-", dir="/tmp") as directory:
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as probe:
                probe.bind(str(Path(directory) / "probe.socket"))
                probe.listen(1)
    except OSError as error:
        local_socket = "FAIL"
        errors.append("EasyCrypt requires local Unix sockets for why3server: "
                      f"{error}. Run in a Linux environment that permits local sockets.")
    commands = {
        "jasminc": (os.environ.get("JASMINC", "jasminc"), ["-version"], "2026.09.0"),
        "jasmin2ec": (os.environ.get("JASMIN2EC", "jasmin2ec"), ["--version"], "2026.09.0"),
        "jasmin-ct": (os.environ.get("JASMIN_CT", "jasmin-ct"), ["--version"], "2026.09.0"),
        "why3": (os.environ.get("WHY3", "why3"), ["--version"], "1.8.2"),
        "alt-ergo": ("alt-ergo", ["--version"], "2.6.0"),
        "cvc4": ("cvc4", ["--version"], "1.8"),
        "cvc5": ("cvc5", ["--version"], "1.2.1"),
        "z3": ("z3", ["--version"], "4.12.6"),
    }
    for name, (command, args, version) in commands.items():
        path = shutil.which(command)
        if not path:
            errors.append(f"Missing {name}: {command}")
            continue
        result = subprocess.run([command, *args], capture_output=True, text=True)
        output = (result.stdout + result.stderr).strip()
        tools[name] = {"version": output.splitlines()[0] if output else "", "sha256": hashlib.sha256(Path(path).read_bytes()).hexdigest()}
        if result.returncode or not re.search(r"(?<![\d.])" + re.escape(version) + r"(?![\d.])", output):
            errors.append(f"Expected {name} {version}, found: {tools[name]['version']}")
    for command in ("make", "cc", "cmake", "sha256sum", "python3", "opam"):
        if not shutil.which(command):
            errors.append(f"Missing {command}")
    easycrypt = os.environ.get("EASYCRYPT", "easycrypt")
    executable = shutil.which(easycrypt)
    if not executable:
        errors.append("Missing EasyCrypt")
    else:
        config = subprocess.run([easycrypt, "config"], capture_output=True, text=True)
        output = config.stdout + config.stderr
        match = re.search(r"^known provers: (.*)$", output, re.M)
        provers = match.group(1) if match else ""
        tools["easycrypt"] = {"sha256": hashlib.sha256(Path(executable).read_bytes()).hexdigest(),
                              "known_provers": provers}
        if config.returncode:
            errors.append("EasyCrypt config failed")
        if not re.search(r"Jasmin@", output):
            errors.append("EasyCrypt cannot find the Jasmin model library")
        for prover in ("Alt-Ergo@2.6.0", "CVC4@1.8.0", "CVC5@1.2.1", "Z3@4.12.6"):
            if prover not in provers.split(", "):
                errors.append(f"EasyCrypt does not detect required prover {prover}; run env/bootstrap.sh")
        # EasyCrypt's release binary does not print a version; use installed
        # package metadata and bind it to the selected executable's prefix.
        if shutil.which("opam"):
            prefix = subprocess.run(["opam", "var", "prefix"], capture_output=True, text=True)
            packages = subprocess.run(["opam", "list", "--installed", "--short", "--columns=name,version"],
                                      capture_output=True, text=True)
            installed = dict(line.split() for line in packages.stdout.splitlines() if len(line.split()) == 2)
            if prefix.returncode or packages.returncode or installed.get("easycrypt") != "2026.09":
                errors.append("Active opam switch must contain easycrypt.2026.09")
            elif Path(executable).resolve().parent != Path(prefix.stdout.strip()).resolve() / "bin":
                errors.append("Selected EasyCrypt executable does not belong to the active opam switch")
            tools["opam_packages"] = {name: installed.get(name) for name in ("ocaml", "easycrypt", "jasmin", "why3")}
    print(json.dumps({"result": "FAIL" if errors else "PASS", "platform": platform.platform(),
                      "local_unix_socket": local_socket, "tools": tools, "errors": errors}, indent=2))
    return bool(errors)


if __name__ == "__main__":
    sys.exit(main())
