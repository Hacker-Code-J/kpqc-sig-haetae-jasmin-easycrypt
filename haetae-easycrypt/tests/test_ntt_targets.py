"""Ensure the NTT gate cannot silently omit new composition proofs."""

import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


PROJECT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("ntt_verifier", PROJECT / "scripts/verify.py")
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


class NTTTargetTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="haetae-ntt-targets-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "manifests").mkdir()
        self.files = [self.root / name for name in (
            "theories/ntt/GFq.ec", "proofs/NTTCorrectness.ec",
            "theories/NTTAlgebra.ec", "proofs/NTTProduct.ec", "proofs/Sampler.ec",
        )]
        for path in self.files:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("")
        (self.root / "manifests/proof-targets.txt").write_text(
            "\n".join(str(path.relative_to(self.root)) for path in self.files) + "\n"
        )
        self.manifest = self.root / "manifests/ntt-composition-targets.txt"
        self.manifest.write_text("theories/NTTAlgebra.ec\nproofs/NTTProduct.ec\n")
        self.patch = patch.object(verifier, "PROJECT", self.root)
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def test_composition_is_in_ntt_group_and_not_sampler_group(self):
        composition = verifier.check_target_manifests(self.files)
        self.assertEqual(set(verifier.select_targets(self.files, "ntt", composition)),
                         set(self.files[:-1]))
        self.assertEqual(verifier.select_targets(self.files, "new", composition),
                         self.files[-1:])

    def test_new_ntt_file_requires_both_manifests(self):
        added = self.root / "proofs/NTTAdded.ec"
        added.write_text("")
        self.files.append(added)
        with self.assertRaisesRegex(ValueError, "proof-targets.txt target coverage"):
            verifier.check_target_manifests(self.files)
        with (self.root / "manifests/proof-targets.txt").open("a") as output:
            output.write("proofs/NTTAdded.ec\n")
        with self.assertRaisesRegex(ValueError, "ntt-composition-targets.txt target coverage"):
            verifier.check_target_manifests(self.files)

    def test_duplicate_or_unrelated_composition_entry_is_rejected(self):
        original = self.manifest.read_text()
        for extra in ("proofs/NTTProduct.ec\n", "proofs/Sampler.ec\n"):
            with self.subTest(extra=extra):
                self.manifest.write_text(original + extra)
                with self.assertRaises(ValueError):
                    verifier.check_target_manifests(self.files)

    def test_real_project_manifests_cover_the_selected_ntt_group(self):
        with patch.object(verifier, "PROJECT", PROJECT):
            files = verifier.proof_files()
            composition = verifier.check_target_manifests(files)
            selected = verifier.select_targets(files, "ntt", composition)
            self.assertTrue(composition)
            self.assertTrue(all(PROJECT / name in selected for name in composition))


if __name__ == "__main__":
    unittest.main()
