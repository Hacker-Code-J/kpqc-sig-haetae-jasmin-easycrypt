#!/usr/bin/env python3
"""Materialize a separate, hash-pinned HAETAE hardening overlay."""
import argparse
import hashlib
import json
from pathlib import Path
import re

PROJECT = Path(__file__).resolve().parents[1]
ROOT = PROJECT.parent
BASE = ROOT / "haetae-jasmin"
LOCK = PROJECT / "baseline-lock.json"
# Historical records retain their original paths and bytes on disk.
LAYOUT_PATHS = {
    "HAETAE-1.2.0": "HAETAE",
    "haetae-1.2.0-jasmin": "haetae-jasmin",
    "haetae-1.2.0-easycrypt": "haetae-easycrypt",
    "haetae-1.2.0-hardened": "haetae-hardened",
    "docs/HAETAE-1.2.0.md": "docs/HAETAE.md",
    "docs/haetae-1.2.0-jasmin-validation.md": "docs/haetae-jasmin-validation.md",
}
LAYOUT_SHA256 = "cddcaa784b1c62d06b1c8f787cd43951e0d7842f9f3cd42627ed493809f7fe23"
PUBLICATION_SHA256 = "921b86b43c0797f02e9b8e079755db675d835b9e68601c3eb355520b6d0f8888"
PUBLICATION_DOCUMENTS = {"README.md", "haetae-easycrypt/README.md", "haetae-easycrypt/VALIDATION.md"}
COPY_DIRS = {"jasmin", "include", "test", "kat", "benchmark"}
MIGRATABLE_METADATA = {
    "README.md", "VALIDATION.md", "scripts/extract.py", "scripts/verify-one.sh",
    "manifests/extractions.sha256", "manifests/toolchain.json",
}
MIGRATION_RECORDS = {
    "manifests/2026.09-all-targets.txt", "manifests/2026.09-generated-targets.txt",
    "manifests/2026.09-migration.json", "manifests/2026.09-new-targets.txt",
    "manifests/2026.09-ntt-targets.txt", "manifests/history/2026.03/README.md",
}
HISTORICAL_COPIES = {
    "manifests/history/2026.03/" + name: "manifests/" + name for name in (
        "extractions.sha256", "jasmin-sources.sha256", "ntt-assumptions.md",
        "ntt-support-origin.tsv", "proof-targets.txt", "shake-support-origin.tsv",
        "specification-sources.json", "toolchain.json", "verification-results.json")
}
# Reviewed 2026.09 proof-body ports are bound to exact paths and both complete
# file hashes. A ledger edit cannot authorize another statement or tactic.
PROOF_PORTS = {
    "proofs/ApiBoundaryCorrectness.ec": (
        "929f693d09fdfd2662252ff97793faee6dca3444509ea3724d1c4831c6513c09",
        "13567181a73b2f9f46d900eb45b0d1493010be942a2d23f1139bf144bc645acd",
    ),
    "proofs/ApproxExpPolynomialBound.ec": (
        "64bae21468cdd3020c77cc249283a416e755fbfc74839b2534d419de049a0e53",
        "52b2a8f5c0daa77277e14e2b6ad81a9d58a77722d45c74b05b579620796659f4",
    ),
    "proofs/DistributionIntervalBounds.ec": (
        "5e27c935050752d0a49de9e3d84ab7916c58ac514dcde0cb3cdf68137eb454f9",
        "bfdc700dc1b30d821b3f21f347e5392c5cb14980fc874495938ac61d08363be7",
    ),
    "proofs/GaussianLatticeMgf.ec": (
        "cefc8173a1430421579b1b548d790e260734a3422d258caf62d3689641335fd0",
        "faaeee4f5fef7f501ccb9309e11a83c33185ba050135f6ea7597fc6e658d9584",
    ),
    "proofs/GaussianRefillCorrectness.ec": (
        "34708c3cd7bba616ce808b11d11887bac3252761b6ae5b0a269953f0b6520c5c",
        "377d7198d333af8155c8c094f5ed442956e9127ff4f67aef70ccdca423e04626",
    ),
    "proofs/GaussianSignBits.ec": (
        "1959b48191b9f5d47cca00d7b4ec44541479ea7ab2ca4f226050867d70dca530",
        "27ab5e5df9fe5bc960df87e7d2edb98b047bdb2784b764801ce15600e5e82a58",
    ),
    "proofs/GaussianStreamBuffer.ec": (
        "1bbb799c26501a407fa5ef203866b685cf1ab9ba3e2dc84350de87816b1a21b5",
        "85a7a7072f8574806ca7c7de6a75098767e3d2f9ecf150e01a59c51433f1530b",
    ),
    "proofs/GaussianUnusedBits.ec": (
        "e58d83e1f11a570b52eb4d34f1c220e9d57e98b6e5e5764fc9cf2a4cf8cf6436",
        "fdae11ecc882b9b9934e1d6c07fc6501991fda05536c8f3247cb4229945adb1c",
    ),
    "proofs/HyperballIidPayloadBatch.ec": (
        "5ab0fbed2682b935f1a3aa33babd2a6bb9b1a9ed3e249d5ebd534d90c4257b4f",
        "8680fc4769982b244f13ef38b3d88434c276044acbd8038d30971e6fcaef5fe0",
    ),
    "proofs/HyperballMulBounds.ec": (
        "3a4e08c2860a199c154f3ec1a33dd542cfc448ad5dfc930ae7d472a25af2d61f",
        "8cbcea5892139e39e787fba436d86971cc1eac54e9922a0931ae726fca5cdc0f",
    ),
    "proofs/HyperballResultProperties.ec": (
        "da02813b5027cd2c34de24f52745b1db84bdc63f8f92fbe0f662a5a866ed59e4",
        "2239d4a3d388a5c4a30759693bb6bb8e18438f456eac38baa5492da2c149823b",
    ),
    "proofs/HyperballSafeCorrectness.ec": (
        "8542b133d3c0861e1e707dc6bd5826220251cbca67287b9199063774b66fa1cd",
        "a28cec3b2bbbb78600b07c3616bb2a10d43e5926c04c2271ae676230a11b9157",
    ),
    "proofs/HyperballSafeScale.ec": (
        "6f6238b1ecdae2a356ca6f2ad5ace2252c58e96ec5c578448229128d2a3bab8f",
        "7b5bdbe53e5481fc7e23b8f6397284f5ad8f138a561b97c13809cd8ec86ac9db",
    ),
    "proofs/HyperballScaleCorrectness.ec": (
        "76dac2aa2df4e5b82a77f401826646a1fa55b12233bb445fab786fa8c6916eb3",
        "807683fd5595817c806aaf2fc19d487340c2f5c3bffb3860c581a804d16edbf9",
    ),
    "proofs/SHAKEBlockCorrectness.ec": (
        "d8a0dbd8d2546670ad57cdcb8a392f81f16ec1c2025d8cb234f663482cb96cbd",
        "61a7b169987983ca6d355cb75f9d379843dee0d39a0d53824d0ee39b296518a4",
    ),
    "proofs/SigmaConditionalCorrectness.ec": (
        "c0d75baab02a78a2abb0021644afc5343f8c4552e0d932fcf0bc22a770f2601c",
        "3b8f3c08486d3fa0cc8269d49d20a1d1f4af39c1154556ddd71e76819c7fe7a6",
    ),
    "proofs/SigmaJointCorrectness.ec": (
        "0b73f992d237ea3bb974b746206f7e0774e787469b2d0c2218d26bc99a610247",
        "2db443f8c86c98947aa2b9bd82e8691ca217d1fce63932543d05f6e2b324b2fc",
    ),
    "theories/HyperballScaleSpec.ec": (
        "95584269d8a50bc2f132a979633b3936e518f41376869f459a01c4a1ed9481e4",
        "fe413013fb5c3edc2f51fc1de3cf356894f3aebedece3e2c57df75d3f635dc1d",
    ),
    "theories/SHAKEStreamSpec.ec": (
        "2b52cb33ec60a423339cfa930a7b01d60a5a079f10bab6f1edf3bdb884476f56",
        "e3cebfff9bfa5071757694fcb886cbddf32cd77991a9e845042a4cf4950813be",
    ),
    "theories/ntt/NTTFullAlgebra.ec": (
        "e5cade55a560aed0112fce32651f1c2c97c1fdf605944fe67034a40234924fdc",
        "a11ae0c7de30934f6cb810e042a45ea1d55d3981033402797c83114b85ab5bd8",
    ),
    "theories/ntt/NTTFullSpec.ec": (
        "949f925251d048642a3d4d222b59d7acdf85cf27a0fa6016fabf5df4a5645516",
        "5292e64f614fc2120d756894de44f68dd00fe7ef017dd8b7b77e803c437fc474",
    ),
    "theories/ntt/NTT_Fq.ec": (
        "62181de33a8ff2e730f7773f0e8148c0eee6f27c7509dfc1e9e60e6258e6d074",
        "73abcb9f5ff33862c4784853102cddcb5e13a8f4d4d401139fdb0323a258b2de",
    ),
}

# This separately reviewed compatibility edit only renames the x86 model
# import from JModel to JModel_x86; it is not a proof-body port.
MODEL_IMPORTS = {
    "theories/ntt/Fq.ec": (
        "9a74258fb09e829679562b6a940777ef522232d6400d9acba6c3bcead29216b9",
        "e280e74e4942c3678120aa66b8e7b38bb0ed900cf69e67785a855e9c5a4ef5a3",
    ),
}
# Preserve historical source pins while accepting the exact reviewed
# extraction, target-inventory, assumption documentation, and gate updates.
CONTROL_PORTS = {
    "manifests/extractions.sha256": (
        "b42fe9c04fb5b55bb02a87246e7c5cf2946fa8183839bd69c707f1a3782fdd85",
        "2dea9cbc8a5d50a568262c6618f7bd7ce35a3191f017fa7835c434ebece6403b",
    ),
    "manifests/ntt-assumptions.md": (
        "bb2aba3945187276f8e73507fdf14b8f62a6fb8cbef29a69e97cb380d1721403",
        "c7c01146deec7fb87c6f7ee034627f44e00784b4ee06eacb90d0c06b282847c1",
    ),
    "manifests/proof-targets.txt": (
        "d182a9d2cf0837f72ab057b8d8c8a5d465f0332fcac662acbc53dd033dc44e63",
        "923f18b92ffe16f31a5ea903615475c4c806bfefb915bedf20dbcbe5bcfde1ca",
    ),
    "scripts/extract.py": (
        "70cf6ba98410b2d2b9d91b7df775de46f124be35f7f39cb75e19661cff0bfed4",
        "f36c9a62565bf6f794e5094f6afc6b60ff1b6391aae2366c6c6bbf3d86640cd3",
    ),
    "scripts/verify-one.sh": (
        "10d03a0248c89077d01476bfe241d254e6c1c5f75391bf375ce2e12457974227",
        "74eab9dbbc2441788821fe2f1cab53eafcde1b499baaee248d52c81d9625c186",
    ),
    "scripts/verify.py": (
        "31f24b12ee7dca5f3edc0d0c895ee42a077e82837bd44b171ccee74994631587",
        "eb5aba4e6ee6aa687a5a69db2b06cbd9eee729e1b2f19a41343b977e9fcafb95",
    ),
    "tests/test_hyperball_provenance.py": (
        "6a73110aec7538f18432fafc6be00696a74b155105d6c123c454750fe9f25eb1",
        "6c5a4f9f9332291c167edfe1b5b89231b1412621ff0e508a9f5099358b3c684d",
    ),
}

# Additive NTT composition sources and their exact manifest/control bytes.
# Pinning these inputs does not itself assert successful proof replay.
NTT_ADDITIONS = {
    "manifests/ntt-common-source.sha256": "3dfcadb7766228ddec8622334bda577415fccfc132c884727f724d9a6b436a31",
    "manifests/ntt-composition-targets.txt": "60f91ef4627dd202c4cf9f506a0351b6a8dfa8cd69ecd91f40566c925ae849cb",
    "proofs/NTTCompositionInstance.ec": "8549b5499e46d15c5bb68d972016e26e9edf98e062da08890b4a1942f6c0468d",
    "proofs/NTTMatrixCorrectness.ec": "f6c963b4e99bcb249d342891731a4e238dc0ab23e228b87a3708382c180fa821",
    "proofs/NTTMatrixProductCorrectness.ec": "b5543f4b6b9e92c549a7e7deb0c43d160e6c52d109eb03c06d9443d6b92c72e3",
    "proofs/NTTMontgomeryBounds.ec": "39211e95a6f0386fa54f50bc0397a92f3e017955933f70fb623a0d515fec3c91",
    "proofs/NTTPointwiseCorrectness.ec": "e5bcb1eaa655190c63775efcde7fe01164746f5f42ff3276daacd726164daf97",
    "proofs/NTTProductCorrectness.ec": "37cad32099f147427678a4a4ff832ae8f6e0e3b922b2469128182320f8ca6823",
    "proofs/NTTVectorCorrectness.ec": "d26873df4a69f53b009d87b2eda8f299bd26226adc17f7a11708fdb3583fc259",
    "proofs/NTTVectorTotal.ec": "9c626a87ecd6ed727d9755a551cebf444bb07319db1944174579cd0e7b3dd169",
    "tests/test_ntt_targets.py": "f36722477d434f35b274d5df659b706bd6f162c6927bcd4b535601cca01badb6",
    "theories/NTTComposition.ec": "61ad40c725798ce6a3cecaf324be066dd07bd06c89a4cc8ebd0a4ce4f45bd393",
    "theories/NTTProductExpansion.ec": "b855c12e68c8a36e11e363bc4dcab5cae42c555d28bde0e7ae073f75cdc8e5ce",
    "theories/NTTTransformAlgebra.ec": "ba0704134fd98c715c7bee67deb78650b3cc91c25dc13bcb2ff6bee5fb0cde0e",
    "theories/NTTVectorSpec.ec": "9a6649c94e0ea0dae81a8c7897d33975a754144fdf06bf47a628966ed71a7662",
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def relocate_files(files):
    relocated = {}
    for name, value in files.items():
        head, separator, tail = name.partition("/")
        current = LAYOUT_PATHS.get(name, LAYOUT_PATHS.get(head, head) + separator + tail)
        if current in relocated:
            raise SystemExit(f"Layout path collision: {current}")
        relocated[current] = value
    return relocated


def layout_inputs():
    path = safe_baseline_path(LOCK.with_name("layout-migration.json").relative_to(ROOT))
    if not path.exists():
        return {}
    content = path.read_bytes()
    if digest(content) != LAYOUT_SHA256:
        raise SystemExit("Unreviewed layout migration ledger")
    return json.loads(content)["files"]


def publication_inputs():
    path = safe_baseline_path(LOCK.with_name("publication-migration.json").relative_to(ROOT))
    if not path.exists():
        return {}
    content = path.read_bytes()
    if digest(content) != PUBLICATION_SHA256:
        raise SystemExit("Unreviewed publication migration ledger")
    files = json.loads(content)["files"]
    if not files.keys() <= PUBLICATION_DOCUMENTS:
        raise SystemExit("Unlisted publication document")
    return files


def safe_baseline_path(name):
    relative = Path(name)
    if relative.is_absolute() or ".." in relative.parts:
        raise SystemExit(f"Invalid baseline input: {name}")
    path = ROOT / relative
    for ancestor in (path, *path.parents):
        if ancestor == ROOT:
            break
        if ancestor.is_symlink():
            raise SystemExit(f"Symbolic baseline input path: {ancestor}")
    if not path.resolve().is_relative_to(ROOT.resolve()):
        raise SystemExit(f"Escaping baseline input: {name}")
    return path


def migration_inputs(lock):
    """Apply an explicit toolchain ledger without replacing the historical lock.

    Generated models, listed metadata and exact reviewed proof/model-import/
    control ports can migrate. Other sources and historical records retain pins.
    """
    path = safe_baseline_path(LOCK.with_name("toolchain-migration-lock.json").relative_to(ROOT))
    if not path.exists():
        return {}
    if path.is_symlink() or not path.is_file():
        raise SystemExit("Missing or symbolic toolchain migration lock")
    migration = json.loads(path.read_text())
    if migration.get("baseline_lock_sha256") != digest(LOCK.read_bytes()) or \
            migration.get("baseline_commit") != lock.get("commit"):
        raise SystemExit("Toolchain migration does not match the historical baseline lock")
    changes = relocate_files(migration["files"])
    prefix = "haetae-easycrypt/"
    for name, hashes in changes.items():
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts or not name.startswith(prefix):
            raise SystemExit(f"Invalid toolchain migration input: {name}")
        tail = name[len(prefix):]
        old, new = hashes["baseline_sha256"], hashes["migrated_sha256"]
        if tail in HISTORICAL_COPIES:
            if old is not None or new != lock["files"].get(prefix + HISTORICAL_COPIES[tail]):
                raise SystemExit(f"Historical copy must match the original baseline record: {name}")
        elif tail in PROOF_PORTS:
            if (old, new) != PROOF_PORTS[tail]:
                raise SystemExit(f"Proof port differs from the exact reviewed hash pair: {name}")
        elif tail in MODEL_IMPORTS:
            if (old, new) != MODEL_IMPORTS[tail]:
                raise SystemExit(f"Model import differs from the exact reviewed hash pair: {name}")
        elif tail in CONTROL_PORTS:
            if (old, new) != CONTROL_PORTS[tail]:
                raise SystemExit(f"Control port differs from the exact reviewed hash pair: {name}")
        elif tail in NTT_ADDITIONS:
            if (old, new) != (None, NTT_ADDITIONS[tail]):
                raise SystemExit(f"NTT addition differs from the exact reviewed hash pair: {name}")
        elif not ((tail.startswith("generated/") and tail.endswith(".ec"))
                  or tail in MIGRATABLE_METADATA
                  or (tail in MIGRATION_RECORDS and old is None)):
            raise SystemExit(f"Toolchain migration cannot replace production sources, proofs or historical records: {name}")
        if old != lock["files"].get(name) or old == new or \
                any(value is not None and not re.fullmatch(r"[0-9a-f]{64}", value)
                    for value in (old, new)):
            raise SystemExit(f"Invalid toolchain migration hash: {name}")
    expected = {name for name in lock["files"] if name.startswith(prefix + "generated/")}
    for name, hashes in changes.items():
        if name.startswith(prefix + "generated/"):
            if hashes["migrated_sha256"] is None:
                expected.discard(name)
            else:
                expected.add(name)
    generated = safe_baseline_path(prefix + "generated")
    actual = {str(path.relative_to(ROOT)) for path in generated.rglob("*")
              if path.is_file() or path.is_symlink()}
    if actual != expected:
        raise SystemExit("Toolchain generated inventory drift: " + ", ".join(sorted(actual ^ expected)))
    return changes


def read_baseline():
    lock = json.loads(safe_baseline_path(LOCK.relative_to(ROOT)).read_text())
    lock["files"] = relocate_files(lock["files"])
    changes = migration_inputs(lock)
    layout = layout_inputs()
    publication = publication_inputs()
    data = {}
    for name in sorted(lock["files"].keys() | changes.keys()):
        expected = (changes[name]["migrated_sha256"] if name in changes else lock["files"][name])
        path = safe_baseline_path(name)
        if expected is None:
            if path.exists() or path.is_symlink():
                raise SystemExit(f"Removed toolchain input has reappeared: {name}")
            continue
        if not path.is_file() or path.is_symlink():
            raise SystemExit(f"Missing or symbolic baseline input: {name}")
        content = path.read_bytes()
        actual = digest(content)
        allowed = {expected}
        for edits in (layout, publication):
            entry = edits.get(name)
            if entry and entry["before_sha256"] in allowed:
                allowed.add(entry["after_sha256"])
        if actual not in allowed:
            raise SystemExit(f"Pinned baseline drift: {name}")
        data[name] = content
    return lock, data


def function_span(source, name):
    starts = list(re.finditer(r"(?m)^fn " + re.escape(name) + r"\(", source))
    if len(starts) != 1:
        raise SystemExit(f"Expected one function {name}, found {len(starts)}")
    start = starts[0].start()
    end = source.find("\n}\n", start)
    if end < 0:
        raise SystemExit(f"Missing function terminator: {name}")
    return start, end + 3


def replace_function(source, fragment, name):
    start, end = function_span(source, name)
    a, b = function_span(fragment, name)
    return source[:start] + fragment[a:b] + source[end:]


def safe_target(relative):
    relative = Path(relative)
    if relative.is_absolute() or ".." in relative.parts:
        raise SystemExit(f"Invalid materialization target: {relative}")
    target = PROJECT / relative
    for ancestor in (target, *target.parents):
        if ancestor == PROJECT:
            break
        if ancestor.is_symlink():
            raise SystemExit(f"Symbolic materialization path: {ancestor}")
    if not target.resolve().is_relative_to(PROJECT):
        raise SystemExit(f"Escaping materialization target: {relative}")
    return target


def desired_outputs():
    lock, baseline = read_baseline()
    overlay = {name: (PROJECT / "overlay" / name).read_bytes() for name in (
        "checked_hyperball.jinc", "sign-scale-and-check.jinc",
        "hyperball-phase-wrappers.jinc")}
    outputs = {}
    prefix = "haetae-jasmin/"
    for name, content in baseline.items():
        if name.startswith(prefix):
            relative = name[len(prefix):]
            if Path(relative).parts[0] in COPY_DIRS:
                outputs[relative] = content
    phase = outputs["jasmin/hyperball_phase.jinc"].decode()
    for name in ("_polyfixveclk_scale_and_check", "_polyfixveclk_scale_and_check_values"):
        phase = replace_function(phase, overlay["hyperball-phase-wrappers.jinc"].decode(), name)
    outputs["jasmin/hyperball_phase.jinc"] = overlay["checked_hyperball.jinc"] + b"\n" + phase.encode()
    sign = outputs["jasmin/sign.jazz"].decode()
    outputs["jasmin/sign.jazz"] = replace_function(
        sign, overlay["sign-scale-and-check.jinc"].decode(), "_sf_scale_and_check").encode()
    # Distinct binary names and SONAMEs prevent confusing the variant with the baseline.
    outputs["build/baseline.mk"] = baseline[prefix + "Makefile"].replace(b"-jazz", b"-hardened-jazz")
    provenance = {
        "baseline_commit": lock["commit"],
        "baseline_lock_sha256": digest(LOCK.read_bytes()),
        "overlay_sha256": {name: digest(content) for name, content in overlay.items()},
        "materialized_sha256": {name: digest(content) for name, content in sorted(outputs.items())},
    }
    migration = LOCK.with_name("toolchain-migration-lock.json")
    if migration.exists():
        provenance["toolchain_migration_lock_sha256"] = digest(migration.read_bytes())
    layout = LOCK.with_name("layout-migration.json")
    if layout.exists():
        provenance["layout_migration_sha256"] = digest(layout.read_bytes())
    publication = LOCK.with_name("publication-migration.json")
    if publication.exists():
        provenance["publication_migration_sha256"] = digest(publication.read_bytes())
    outputs["build/materialization.json"] = (json.dumps(provenance, indent=2) + "\n").encode()
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check existing materialization without writing")
    args = parser.parse_args()
    outputs = desired_outputs()
    # Validate every ancestor before any write: a symlinked jasmin/ directory
    # must never redirect an overlay into the preserved baseline.
    destinations = {name: safe_target(name) for name in outputs}
    # Unexpected source files would change wildcard dependencies; reject them explicitly.
    extra = sorted(str(p.relative_to(PROJECT)) for directory in COPY_DIRS
                   for p in (PROJECT / directory).rglob("*") if p.is_file()
                   and str(p.relative_to(PROJECT)) not in outputs)
    if extra:
        raise SystemExit("Unexpected materialized input(s): " + ", ".join(extra))
    for relative, content in outputs.items():
        path = destinations[relative]
        if path.exists() and path.read_bytes() == content:
            continue
        if args.check:
            raise SystemExit(f"Materialization drift: {relative}")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    print(f"PASS: {len(outputs)} hardened outputs {'match' if args.check else 'materialized from'} pinned baseline and overlay")


if __name__ == "__main__":
    main()
