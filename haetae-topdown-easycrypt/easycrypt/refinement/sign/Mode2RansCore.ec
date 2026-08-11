require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2HbzCodecSpec Mode2HbzTableCertificate.

theory Mode2RansCore.

import Mode2HbzCodecSpec Mode2HbzTableCertificate.

op pure_rans_encode_step (x start freq : int) : int =
  (x %/ freq) * rans_scale + start + x %% freq.

op pure_rans_decode_step (y start freq : int) : int =
  (y %/ rans_scale) * freq + (y %% rans_scale) - start.

lemma pure_rans_step_quotient x start freq :
  0 <= x =>
  0 <= start =>
  0 < freq =>
  start + freq <= rans_scale =>
  pure_rans_encode_step x start freq %/ rans_scale = x %/ freq.
proof.
move=> hx hstart hfreq hcover.
have hmod : 0 <= x %% freq < freq.
+ apply modz_cmp.
  exact hfreq.
have hscale : rans_scale <> 0 by rewrite /rans_scale.
have hsmall : 0 <= start + x %% freq < rans_scale by smt().
have hsmall_abs : 0 <= start + x %% freq < `|rans_scale|.
+ rewrite /rans_scale /=.
  rewrite /rans_scale in hsmall.
  exact hsmall.
have hzero : (start + x %% freq) %/ rans_scale = 0.
+ apply divz_small.
  exact hsmall_abs.
rewrite /pure_rans_encode_step.
have -> :
    (x %/ freq) * rans_scale + start + x %% freq =
    (start + x %% freq) + (x %/ freq) * rans_scale by ring.
rewrite (divzMDr (x %/ freq) (start + x %% freq) rans_scale hscale).
rewrite hzero.
ring.
qed.

lemma pure_rans_step_slot x start freq :
  0 <= x =>
  0 <= start =>
  0 < freq =>
  start + freq <= rans_scale =>
  pure_rans_encode_step x start freq %% rans_scale =
  start + x %% freq.
proof.
move=> hx hstart hfreq hcover.
have hmod : 0 <= x %% freq < freq.
+ apply modz_cmp.
  exact hfreq.
have hsmall : 0 <= start + x %% freq < rans_scale by smt().
have hsmall_abs : 0 <= start + x %% freq < `|rans_scale|.
+ rewrite /rans_scale /=.
  rewrite /rans_scale in hsmall.
  exact hsmall.
have hsame : (start + x %% freq) %% rans_scale = start + x %% freq.
+ apply modz_small.
  exact hsmall_abs.
rewrite /pure_rans_encode_step.
have -> :
    (x %/ freq) * rans_scale + start + x %% freq =
    (start + x %% freq) + (x %/ freq) * rans_scale by ring.
rewrite (modzMDr (x %/ freq) (start + x %% freq) rans_scale).
rewrite hsame.
trivial.
qed.

lemma pure_rans_step_inverse x start freq :
  0 <= x =>
  0 <= start =>
  0 < freq =>
  start + freq <= rans_scale =>
  pure_rans_decode_step
    (pure_rans_encode_step x start freq) start freq = x.
proof.
move=> hx hstart hfreq hcover.
rewrite /pure_rans_decode_step.
rewrite (pure_rans_step_quotient x start freq hx hstart hfreq hcover)
        (pure_rans_step_slot x start freq hx hstart hfreq hcover).
smt(divz_eq).
qed.

lemma hbz_interval_bounds s :
  0 <= s < mode2_hbz_alphabet =>
  0 <= hbz_start s /\
  0 < hbz_freq s /\
  hbz_start s + hbz_freq s <= rans_scale.
proof.
rewrite /mode2_hbz_alphabet /hbz_start /hbz_freq /rans_scale.
smt().
qed.

op hbz_math_decode_step (y s : int) : int =
  pure_rans_decode_step y (hbz_start s) (hbz_freq s).

lemma hbz_math_step_inverse s x :
  0 <= s < mode2_hbz_alphabet =>
  0 <= x =>
  hbz_math_decode_step (hbz_math_encode_step x s) s = x.
proof.
move=> hs hx.
have [hstart [hfreq hcover]] := hbz_interval_bounds s hs.
rewrite /hbz_math_decode_step /hbz_math_encode_step.
exact (pure_rans_step_inverse
  x (hbz_start s) (hbz_freq s) hx hstart hfreq hcover).
qed.

lemma hbz_encoded_slot_selects_symbol s x :
  0 <= s < mode2_hbz_alphabet =>
  0 <= x =>
  hbz_symbol_for_slot (hbz_math_encode_step x s %% rans_scale) = s.
proof.
move=> hs hx.
have [hstart [hfreq hcover]] := hbz_interval_bounds s hs.
have hslot := pure_rans_step_slot
  x (hbz_start s) (hbz_freq s) hx hstart hfreq hcover.
rewrite /hbz_math_encode_step -/pure_rans_encode_step in hslot.
rewrite hslot.
apply (hbz_slot_interval s (hbz_start s + x %% hbz_freq s) hs).
smt(@IntDiv).
qed.

lemma hbz_fast_step_decode_inverse s x :
  0 <= s < mode2_hbz_alphabet =>
  1 <= x < hbz_xmax s =>
  hbz_math_decode_step (hbz_fast_encode_step x s) s = x.
proof.
move=> hs hx.
rewrite (hbz_fast_step_matches_math s x hs hx).
apply (hbz_math_step_inverse s x hs).
smt().
qed.

lemma hbz_fast_step_preconditions_satisfiable :
  0 <= 0 < mode2_hbz_alphabet /\
  1 <= 1 < hbz_xmax 0.
proof.
rewrite /mode2_hbz_alphabet /hbz_xmax /hbz_freq.
smt().
qed.

end Mode2RansCore.
