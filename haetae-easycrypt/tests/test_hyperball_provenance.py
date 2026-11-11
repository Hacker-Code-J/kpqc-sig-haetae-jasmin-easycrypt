#!/usr/bin/env python3
"""Reject altered constants and unreviewed changes to pinned support theories."""
import csv
import hashlib
import importlib.util
import io
from pathlib import Path
import re
import unittest
from unittest.mock import patch

PROJECT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("haetae_verify", PROJECT / "scripts/verify.py")
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)

REVIEWED_SUPPORT = {
    "theories/ntt/Fq.ec": "ntt-support-origin.tsv",
    "theories/ntt/NTT_Fq.ec": "ntt-support-origin.tsv",
    "theories/ntt/NTTFullSpec.ec": "ntt-support-origin.tsv",
    "theories/ntt/NTTFullAlgebra.ec": "ntt-support-origin.tsv",
    "proofs/SHAKEBlockCorrectness.ec": "shake-support-origin.tsv",
}


class SupportPortProvenanceTests(unittest.TestCase):
    def assert_rejected(self, relative, *, source=None, pin=None, last_origin_only=False,
                        manifest_name=None):
        target = PROJECT / relative
        manifest = PROJECT / "manifests" / (manifest_name or REVIEWED_SUPPORT[relative])
        original_read = Path.read_bytes
        original_open = Path.open
        original = original_read(target)
        original_manifest = manifest.read_text()
        text = original_manifest
        if pin is not None:
            reader = csv.DictReader(io.StringIO(text), delimiter="\t")
            fields = reader.fieldnames
            rows = list(reader)
            matching = [i for i, row in enumerate(rows) if row["destination"] == relative]
            self.assertTrue(matching)
            for index in matching[-1:] if last_origin_only else matching:
                rows[index]["ported_sha256"] = pin
            changed = io.StringIO()
            writer = csv.DictWriter(changed, fieldnames=fields, delimiter="\t", lineterminator="\n")
            writer.writeheader()
            writer.writerows(rows)
            text = changed.getvalue()

        def read_bytes(path):
            return source if path == target and source is not None else original_read(path)

        def open_file(path, *args, **kwargs):
            return io.StringIO(text) if path == manifest else original_open(path, *args, **kwargs)

        # Only this process observes mutations; concurrent proof runs and
        # on-disk sources/TSVs retain their original bytes throughout.
        with patch.object(Path, "read_bytes", read_bytes), patch.object(Path, "open", open_file):
            with self.assertRaisesRegex(ValueError, "support.*drift: " + re.escape(relative)):
                VERIFY.check_provenance()
        self.assertEqual(original_read(target), original)
        self.assertEqual(manifest.read_text(), original_manifest)

    def test_current_reviewed_ports_pass_with_historical_tsv_pins(self):
        VERIFY.check_provenance()

    def test_any_byte_change_to_a_reviewed_file_is_rejected(self):
        for relative in REVIEWED_SUPPORT:
            with self.subTest(target=relative):
                altered = (PROJECT / relative).read_bytes() + b"\n(* unreviewed edit *)\n"
                self.assert_rejected(relative, source=altered)

    def test_changed_lemma_is_rejected(self):
        for relative in REVIEWED_SUPPORT:
            with self.subTest(target=relative):
                original = (PROJECT / relative).read_bytes()
                altered, count = re.subn(rb"(?m)^lemma (\w+)", rb"lemma changed_\1", original, count=1)
                self.assertEqual(count, 1)
                self.assert_rejected(relative, source=altered)

    def test_changed_model_import_is_rejected(self):
        relative = "theories/ntt/Fq.ec"
        original = (PROJECT / relative).read_bytes()
        altered = original.replace(b"JWord JModel_x86.", b"JWord JModel_arm_m4.", 1)
        self.assertNotEqual(altered, original)
        self.assert_rejected(relative, source=altered)

    def test_tsv_pin_cannot_be_replaced_by_current_hash(self):
        for relative in REVIEWED_SUPPORT:
            with self.subTest(target=relative):
                current = hashlib.sha256((PROJECT / relative).read_bytes()).hexdigest()
                self.assert_rejected(relative, pin=current)

    def test_source_and_matching_tsv_pin_cannot_authorize_a_new_port(self):
        for relative in REVIEWED_SUPPORT:
            with self.subTest(target=relative):
                altered = (PROJECT / relative).read_bytes() + b"\n(* unauthorized port *)\n"
                self.assert_rejected(relative, source=altered, pin=hashlib.sha256(altered).hexdigest())

    def test_second_shake_origin_pin_is_also_checked(self):
        self.assert_rejected("proofs/SHAKEBlockCorrectness.ec", pin="0" * 64, last_origin_only=True)

    def test_unlisted_support_file_still_requires_its_original_hash(self):
        relative = "theories/ntt/GFq.ec"
        altered = (PROJECT / relative).read_bytes() + b"\n(* unreviewed edit *)\n"
        self.assert_rejected(relative, source=altered, manifest_name="ntt-support-origin.tsv")


class HyperballProvenanceTests(unittest.TestCase):
    def test_changed_scale_is_rejected_without_editing_the_live_theory(self):
        target = PROJECT / "theories/HyperballReferenceConstants.ec"
        original_read = Path.read_bytes
        original = original_read(target)
        needle = b"W64.of_int 2643021496320"
        self.assertIn(needle, original)
        altered = original.replace(needle, b"W64.of_int 2643021496321", 1)

        def read_bytes(path):
            return altered if path == target else original_read(path)

        # The independent C emitter runs normally. Only this process's final
        # read of the expected theory is changed; concurrent proof runs see the
        # untouched source file, and no project input needs to be restored.
        with patch.object(Path, "read_bytes", read_bytes):
            with self.assertRaisesRegex(ValueError, "Hyperball reference constants drift"):
                VERIFY.check_provenance()
        self.assertEqual(original_read(target), original)


if __name__ == "__main__":
    unittest.main()
