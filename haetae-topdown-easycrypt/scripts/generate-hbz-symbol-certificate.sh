#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
OUTPUT=${1:-"$PROJECT_DIR/easycrypt/refinement/sign/Mode2HbzSymbolWordsGenerated.ec"}
TEMP=$(mktemp)

cleanup() {
  rm -f "$TEMP"
}
trap cleanup EXIT HUP INT TERM

awk '
function symbol_for_slot(x) {
  if (x < 1) return 0
  if (x < 2) return 1
  if (x < 3) return 2
  if (x < 8) return 3
  if (x < 66) return 4
  if (x < 312) return 5
  if (x < 710) return 6
  if (x < 957) return 7
  if (x < 1016) return 8
  if (x < 1021) return 9
  if (x < 1022) return 10
  if (x < 1023) return 11
  return 12
}

BEGIN {
  print "require import AllCore IntDiv List."
  print ""
  print "from Jasmin require import JModel_x86."
  print ""
  print "import SLH64."
  print ""
  print "require SignaturePackMode2Target SignatureUnpackMode2Target."
  print "require import Mode2HbzTableCertificate."
  print ""
  print "theory Mode2HbzSymbolWordsGenerated."
  print ""
  print "import Mode2HbzCodecSpec Mode2HbzTableCertificate."
  print ""

  for (i = 0; i < 512; i++) {
    lo = symbol_for_slot(2 * i)
    hi = symbol_for_slot(2 * i + 1)
    word = lo + 65536 * hi
    printf "lemma mode2_hbz_symbol_word_%03d :\n", i
    printf "  BArray2048.get32\n"
    printf "    SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words %d =\n", i
    printf "  W32.of_int %d.\n", word
    print "proof."
    print "rewrite /SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words"
    print "        BArray2048.get32_of_list32 1:// 1:// /=."
    print "qed."
    print ""
  }

  print "lemma actual_mode2_hbz_packed_symbol_words word_index :"
  print "  0 <= word_index < 512 =>"
  print "  BArray2048.get32"
  print "    SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words word_index ="
  print "  W32.of_int (hbz_packed_symbol_word word_index)."
  print "proof."
  print "move=> hword."
  print "have hword_mem : word_index \\in range 0 512 by rewrite mem_range."
  print "move: hword_mem."
  for (i = 0; i < 512; i++) {
    print "rewrite range_ltn //=; move=> [->>|]."
    printf "+ rewrite /hbz_packed_symbol_word /hbz_symbol_for_slot /=.\n"
    printf "  exact mode2_hbz_symbol_word_%03d.\n", i
  }
  print "by rewrite range_geq."
  print "qed."
  print ""

  print "lemma actual_mode2_hbz_symbol_words slot :"
  print "  0 <= slot < Mode2HbzCodecSpec.rans_scale =>"
  print "  table_symbol_at"
  print "    SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words slot ="
  print "  hbz_symbol_for_slot slot."
  print "proof."
  print "move=> hslot."
  print "have hword : 0 <= slot %/ 2 < 512."
  print "+ rewrite /Mode2HbzCodecSpec.rans_scale in hslot."
  print "  smt(@IntDiv)."
  print "have hpack := actual_mode2_hbz_packed_symbol_words (slot %/ 2) hword."
  print "rewrite /table_symbol_at /= hpack."
  print "have hlow := hbz_symbol_for_slot_range (2 * (slot %/ 2)) _."
  print "+ smt(@IntDiv)."
  print "have hhigh := hbz_symbol_for_slot_range (2 * (slot %/ 2) + 1) _."
  print "+ smt(@IntDiv)."
  print "rewrite (hbz_packed_symbol_word_uint (slot %/ 2) hword)."
  print "case (slot %% 2 = 0) => hparity."
  print "+ rewrite (hbz_packed_symbol_word_low (slot %/ 2) hword)."
  print "  have -> : 2 * (slot %/ 2) = slot by smt(@IntDiv)."
  print "  trivial."
  print "have hrem : slot %% 2 = 1 by smt(@IntDiv)."
  print "rewrite (hbz_packed_symbol_word_high (slot %/ 2) hword)."
  print "have -> : 2 * (slot %/ 2) + 1 = slot by smt(@IntDiv)."
  print "trivial."
  print "qed."
  print ""

  print "lemma actual_mode2_hbz_tables_certified :"
  print "  mode2_hbz_table_certificate"
  print "    SignaturePackMode2Target.jmode2_hb_z1_esyms"
  print "    SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words"
  print "    SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words."
  print "proof."
  print "rewrite /mode2_hbz_table_certificate."
  print "split."
  print "+ exact actual_mode2_hbz_esym_fields."
  print "split."
  print "+ exact actual_mode2_hbz_dsym_words."
  print "exact actual_mode2_hbz_symbol_words."
  print "qed."
  print ""
  print "end Mode2HbzSymbolWordsGenerated."
}
' /dev/null > "$TEMP"

mv "$TEMP" "$OUTPUT"
trap - EXIT HUP INT TERM
