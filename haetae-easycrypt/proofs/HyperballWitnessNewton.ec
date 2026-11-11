require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import HyperballFixedPointSpec HyperballFixedPointCorrectness
  HyperballReferenceConstants HyperballWitnessSpec HyperballWordEvaluation
  HyperballSignedScale SigmaSpec.

(* All observations in this file are exact machine-word computations for
   the fixed fixtures. They assert no approximation to a real inverse square
   root, and do not assume that any Newton intermediate fits a signed type. *)
lemma hbw_normalized_low (x : hb_fp) :
  W64.to_uint (hb_norm x).`1 < 281474976710656.
proof.
  rewrite /hb_norm /=.
  have -> : 281474976710655 = 2^48-1 by trivial.
  rewrite W64.to_uint_and_mod //=.
  have h := modz_cmp (W64.to_uint x.`1) 281474976710656 _; smt().
qed.

lemma hbw_pair_value_injective (x y : hb_fp) :
  W64.to_uint x.`1 < 281474976710656 =>
  W64.to_uint y.`1 < 281474976710656 => hb_value x = hb_value y => x = y.
proof.
  case: x => x0 x1; case: y => y0 y1.
  rewrite /hb_value /=; move=> hx hy he.
  have /= hxr := W64.to_uint_cmp x0.
  have /= hyr := W64.to_uint_cmp y0.
  have [hl hh] : W64.to_uint x0 = W64.to_uint y0 /\ W64.to_uint x1 = W64.to_uint y1 by smt().
  have ex : x0 = y0 by apply W64.to_uint_eq; exact hl.
  have ey : x1 = y1 by apply W64.to_uint_eq; exact hh.
  by rewrite ex ey.
qed.

lemma hbw_half_round_exact (mode : int) : hbw_mode mode =>
  hb_half_round (hbw_sum mode) = hbw_half mode.
proof.
  move=> hm.
  have hs : W64.to_uint (hbw_sum mode).`1 < 281474976710656.
  + move: hm; rewrite /hbw_mode; move=> [-> | [-> | ->]];
      by rewrite /hbw_sum /= ?W64.of_uintK /=.
  have hh : W64.to_uint (hbw_half mode).`1 < 281474976710656.
  + move: hm; rewrite /hbw_mode; move=> [-> | [-> | ->]];
      by rewrite /hbw_half /= ?W64.of_uintK /=.
  have hv : (hb_value (hbw_sum mode)+1) %/ 2 = hb_value (hbw_half mode).
  + move: hm; rewrite /hbw_mode; move=> [-> | [-> | ->]];
      by rewrite /hbw_sum /hbw_half /hb_value /= ?W64.of_uintK /=.
  apply hbw_pair_value_injective.
  + rewrite /hb_half_round; apply hbw_normalized_low.
  + exact hh.
  by rewrite (hb_half_round_integer (hbw_sum mode) hs) hv.
qed.

lemma hbw_first_signed_high (mode : int) : hbw_mode mode =>
  W64.to_sint (hbw_first mode).`2 =
    if mode=2 then -33789970 else if mode=3 then -157935164 else -11211417.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hbw_first /= W64.of_sintK /W64.smod /=.
qed.

lemma hbw_first_negative (mode : int) : hbw_mode mode =>
  W64.to_sint (hbw_first mode).`2 < 0.
proof.
  move=> hm; rewrite (hbw_first_signed_high mode hm).
  case (mode=2); case (mode=3); trivial.
qed.

(* Concrete transition certificates. The numerals are candidate results;
   every equality below is independently checked by word-to-integer rewrite
   lemmas, preserving all64-bit modular reductions. No table entry is assumed. *)

lemma hbw_newton_initial_2 :
  hb_newton_initial (hbw_half 2) (hb_ref_cube 2) (hb_ref_three 2) = hbw_first 2.
proof.
  have hm : hb_mul (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 130843895063578, W64.of_int 4450) = (W64.of_int 65894922741212, W64.of_int 44057191).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  rewrite /hb_newton_initial /hbw_half /hb_ref_cube /hb_ref_three /hbw_first /= hm /hb_sub /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
qed.

lemma hbw_newton_initial_3 :
  hb_newton_initial (hbw_half 3) (hb_ref_cube 3) (hb_ref_three 3) = hbw_first 3.
proof.
  have hm : hb_mul (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 28764298784360, W64.of_int 2424) = (W64.of_int 174934083751211, W64.of_int 166320132).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  rewrite /hb_newton_initial /hbw_half /hb_ref_cube /hb_ref_three /hbw_first /= hm /hb_sub /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
qed.

lemma hbw_newton_initial_5 :
  hb_newton_initial (hbw_half 5) (hb_ref_cube 5) (hb_ref_three 5) = hbw_first 5.
proof.
  have hm : hb_mul (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 123213818923277, W64.of_int 1794) = (W64.of_int 43673676362222, W64.of_int 18796504).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  rewrite /hb_newton_initial /hbw_half /hb_ref_cube /hb_ref_three /hbw_first /= hm /hb_sub /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
qed.

lemma hbw_newton_initial_exact (mode : int) : hbw_mode mode =>
  hb_newton_initial (hbw_half mode) (hb_ref_cube mode) (hb_ref_three mode) = hbw_first mode.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]].
  + exact hbw_newton_initial_2.
  + exact hbw_newton_initial_3.
  exact hbw_newton_initial_5.
qed.

lemma hbw_newton_step_2_0 :
  hb_newton_step (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 331270931819935, W64.of_int 18446744073675761646) = (W64.of_int 13316356745287, W64.of_int 6846056493641674447).
proof.
  have hs : hb_square (W64.of_int 331270931819935, W64.of_int 18446744073675761646) = (W64.of_int 162848917531827, W64.of_int 13802685983377960376).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 162848917531827, W64.of_int 13802685983377960376) = (W64.of_int 117299284994387, W64.of_int 4081050362553954278).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 117299284994387, W64.of_int 4081050362553954278) = (W64.of_int 164175691716269, W64.of_int 14365693711558250521).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 14365693711558250521 `>>>` 63) `&` W64.one = W64.of_int 1.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 164175691716269, W64.of_int 14365693711558250521) (W64.of_int 1) = (W64.of_int 117299284994387, W64.of_int 4081050362151301094).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 117299284994387, W64.of_int 4081050362151301094) (W64.of_int 331270931819935, W64.of_int 18446744073675761646) = (W64.of_int 268158619965369, W64.of_int 11600687580067877168).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 268158619965369, W64.of_int 11600687580067877168) (W64.of_int 1) = (W64.of_int 13316356745287, W64.of_int 6846056493641674447).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_2_1 :
  hb_newton_step (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 13316356745287, W64.of_int 6846056493641674447) = (W64.of_int 188546408899647, W64.of_int 4584635192158448732).
proof.
  have hs : hb_square (W64.of_int 13316356745287, W64.of_int 6846056493641674447) = (W64.of_int 4431884286392, W64.of_int 9259261322291393411).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 4431884286392, W64.of_int 9259261322291393411) = (W64.of_int 13957812176051, W64.of_int 18246846909790526579).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 13957812176051, W64.of_int 18246846909790526579) = (W64.of_int 267517164534605, W64.of_int 199897164321678220).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 199897164321678220 `>>>` 63) `&` W64.one = W64.of_int 0.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 267517164534605, W64.of_int 199897164321678220) (W64.of_int 0) = (W64.of_int 267517164534605, W64.of_int 199897164321678220).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 267517164534605, W64.of_int 199897164321678220) (W64.of_int 13316356745287, W64.of_int 6846056493641674447) = (W64.of_int 188546408899647, W64.of_int 4584635192158448732).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 188546408899647, W64.of_int 4584635192158448732) (W64.of_int 0) = (W64.of_int 188546408899647, W64.of_int 4584635192158448732).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_2_2 :
  hb_newton_step (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 188546408899647, W64.of_int 4584635192158448732) = (W64.of_int 36750799524385, W64.of_int 17045911428065883665).
proof.
  have hs : hb_square (W64.of_int 188546408899647, W64.of_int 4584635192158448732) = (W64.of_int 15214967000326, W64.of_int 15459088843831386665).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 15214967000326, W64.of_int 15459088843831386665) = (W64.of_int 129475062684702, W64.of_int 2416623960815598513).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 129475062684702, W64.of_int 2416623960815598513) = (W64.of_int 151999914025954, W64.of_int 16030120113296606286).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 16030120113296606286 `>>>` 63) `&` W64.one = W64.of_int 1.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 151999914025954, W64.of_int 16030120113296606286) (W64.of_int 1) = (W64.of_int 129475062684702, W64.of_int 2416623960412945329).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 129475062684702, W64.of_int 2416623960412945329) (W64.of_int 188546408899647, W64.of_int 4584635192158448732) = (W64.of_int 244724177186271, W64.of_int 1400832645643667950).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 244724177186271, W64.of_int 1400832645643667950) (W64.of_int 1) = (W64.of_int 36750799524385, W64.of_int 17045911428065883665).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_2_3 :
  hb_newton_step (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 36750799524385, W64.of_int 17045911428065883665) = (W64.of_int 42932898497114, W64.of_int 4509971554233020529).
proof.
  have hs : hb_square (W64.of_int 36750799524385, W64.of_int 17045911428065883665) = (W64.of_int 91582207203363, W64.of_int 12916994740233820095).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 91582207203363, W64.of_int 12916994740233820095) = (W64.of_int 244396929426485, W64.of_int 16867695885013520213).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 244396929426485, W64.of_int 16867695885013520213) = (W64.of_int 37078047284171, W64.of_int 1579048189098684586).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 1579048189098684586 `>>>` 63) `&` W64.one = W64.of_int 0.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 37078047284171, W64.of_int 1579048189098684586) (W64.of_int 0) = (W64.of_int 37078047284171, W64.of_int 1579048189098684586).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 37078047284171, W64.of_int 1579048189098684586) (W64.of_int 36750799524385, W64.of_int 17045911428065883665) = (W64.of_int 42932898497114, W64.of_int 4509971554233020529).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 42932898497114, W64.of_int 4509971554233020529) (W64.of_int 0) = (W64.of_int 42932898497114, W64.of_int 4509971554233020529).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_2_4 :
  hb_newton_step (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 42932898497114, W64.of_int 4509971554233020529) = (W64.of_int 267900675430979, W64.of_int 9672405162005500899).
proof.
  have hs : hb_square (W64.of_int 42932898497114, W64.of_int 4509971554233020529) = (W64.of_int 77714056887413, W64.of_int 15514136813926456350).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 77714056887413, W64.of_int 15514136813926456350) = (W64.of_int 223210620019027, W64.of_int 12406130613577106186).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 223210620019027, W64.of_int 12406130613577106186) = (W64.of_int 58264356691629, W64.of_int 6040613460535098613).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 6040613460535098613 `>>>` 63) `&` W64.one = W64.of_int 0.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 58264356691629, W64.of_int 6040613460535098613) (W64.of_int 0) = (W64.of_int 58264356691629, W64.of_int 6040613460535098613).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 58264356691629, W64.of_int 6040613460535098613) (W64.of_int 42932898497114, W64.of_int 4509971554233020529) = (W64.of_int 267900675430979, W64.of_int 9672405162005500899).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 267900675430979, W64.of_int 9672405162005500899) (W64.of_int 0) = (W64.of_int 267900675430979, W64.of_int 9672405162005500899).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_2_5 :
  hb_newton_step (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 267900675430979, W64.of_int 9672405162005500899) = (W64.of_int 101666530011624, W64.of_int 17352118948918032670).
proof.
  have hs : hb_square (W64.of_int 267900675430979, W64.of_int 9672405162005500899) = (W64.of_int 131572698828613, W64.of_int 18276876083538504558).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 246938261909420, W64.of_int 2657365604544) (W64.of_int 131572698828613, W64.of_int 18276876083538504558) = (W64.of_int 112816496222458, W64.of_int 5506879389541553169).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 112816496222458, W64.of_int 5506879389541553169) = (W64.of_int 168658480488198, W64.of_int 12939864684570651630).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 12939864684570651630 `>>>` 63) `&` W64.one = W64.of_int 1.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 168658480488198, W64.of_int 12939864684570651630) (W64.of_int 1) = (W64.of_int 112816496222458, W64.of_int 5506879389138899985).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 112816496222458, W64.of_int 5506879389138899985) (W64.of_int 267900675430979, W64.of_int 9672405162005500899) = (W64.of_int 179808446699032, W64.of_int 1094625124791518945).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 179808446699032, W64.of_int 1094625124791518945) (W64.of_int 1) = (W64.of_int 101666530011624, W64.of_int 17352118948918032670).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_3_0 :
  hb_newton_step (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 241583609198600, W64.of_int 18446744073551616452) = (W64.of_int 98933178328723, W64.of_int 10336678811124632675).
proof.
  have hs : hb_square (W64.of_int 241583609198600, W64.of_int 18446744073551616452) = (W64.of_int 73608398480869, W64.of_int 15187044540164605604).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 73608398480869, W64.of_int 15187044540164605604) = (W64.of_int 216925457244838, W64.of_int 15885387493503806884).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 216925457244838, W64.of_int 15885387493503806884) = (W64.of_int 64549519465818, W64.of_int 2561356580608397915).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 2561356580608397915 `>>>` 63) `&` W64.one = W64.of_int 0.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 64549519465818, W64.of_int 2561356580608397915) (W64.of_int 0) = (W64.of_int 64549519465818, W64.of_int 2561356580608397915).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 64549519465818, W64.of_int 2561356580608397915) (W64.of_int 241583609198600, W64.of_int 18446744073551616452) = (W64.of_int 98933178328723, W64.of_int 10336678811124632675).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 98933178328723, W64.of_int 10336678811124632675) (W64.of_int 0) = (W64.of_int 98933178328723, W64.of_int 10336678811124632675).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_3_1 :
  hb_newton_step (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 98933178328723, W64.of_int 10336678811124632675) = (W64.of_int 113131864244766, W64.of_int 15593788615557633629).
proof.
  have hs : hb_square (W64.of_int 98933178328723, W64.of_int 10336678811124632675) = (W64.of_int 46009727141995, W64.of_int 2024972468525611936).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 46009727141995, W64.of_int 2024972468525611936) = (W64.of_int 158393614692777, W64.of_int 13004178329405078180).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 158393614692777, W64.of_int 13004178329405078180) = (W64.of_int 123081362017879, W64.of_int 5442565744707126619).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 5442565744707126619 `>>>` 63) `&` W64.one = W64.of_int 0.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 123081362017879, W64.of_int 5442565744707126619) (W64.of_int 0) = (W64.of_int 123081362017879, W64.of_int 5442565744707126619).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 123081362017879, W64.of_int 5442565744707126619) (W64.of_int 98933178328723, W64.of_int 10336678811124632675) = (W64.of_int 113131864244766, W64.of_int 15593788615557633629).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 113131864244766, W64.of_int 15593788615557633629) (W64.of_int 0) = (W64.of_int 113131864244766, W64.of_int 15593788615557633629).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_3_2 :
  hb_newton_step (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 113131864244766, W64.of_int 15593788615557633629) = (W64.of_int 80170277396342, W64.of_int 17394336002778426670).
proof.
  have hs : hb_square (W64.of_int 113131864244766, W64.of_int 15593788615557633629) = (W64.of_int 223951037177988, W64.of_int 10488294592011942920).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 223951037177988, W64.of_int 10488294592011942920) = (W64.of_int 45452090723212, W64.of_int 5141305878491036890).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 45452090723212, W64.of_int 5141305878491036890) = (W64.of_int 236022885987444, W64.of_int 13305438195621167909).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 13305438195621167909 `>>>` 63) `&` W64.one = W64.of_int 1.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 236022885987444, W64.of_int 13305438195621167909) (W64.of_int 1) = (W64.of_int 45452090723212, W64.of_int 5141305878088383706).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 45452090723212, W64.of_int 5141305878088383706) (W64.of_int 113131864244766, W64.of_int 15593788615557633629) = (W64.of_int 201304699314314, W64.of_int 1052408070931124945).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 201304699314314, W64.of_int 1052408070931124945) (W64.of_int 1) = (W64.of_int 80170277396342, W64.of_int 17394336002778426670).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_3_3 :
  hb_newton_step (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 80170277396342, W64.of_int 17394336002778426670) = (W64.of_int 68864825180320, W64.of_int 4480943190977097479).
proof.
  have hs : hb_square (W64.of_int 80170277396342, W64.of_int 17394336002778426670) = (W64.of_int 230590359157361, W64.of_int 6127994145716328047).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 230590359157361, W64.of_int 6127994145716328047) = (W64.of_int 157214585223537, W64.of_int 9759933857417390948).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 157214585223537, W64.of_int 9759933857417390948) = (W64.of_int 124260391487119, W64.of_int 8686810216694813851).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 8686810216694813851 `>>>` 63) `&` W64.one = W64.of_int 0.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 124260391487119, W64.of_int 8686810216694813851) (W64.of_int 0) = (W64.of_int 124260391487119, W64.of_int 8686810216694813851).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 124260391487119, W64.of_int 8686810216694813851) (W64.of_int 80170277396342, W64.of_int 17394336002778426670) = (W64.of_int 68864825180320, W64.of_int 4480943190977097479).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 68864825180320, W64.of_int 4480943190977097479) (W64.of_int 0) = (W64.of_int 68864825180320, W64.of_int 4480943190977097479).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_3_4 :
  hb_newton_step (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 68864825180320, W64.of_int 4480943190977097479) = (W64.of_int 211205781071443, W64.of_int 4961457989078320386).
proof.
  have hs : hb_square (W64.of_int 68864825180320, W64.of_int 4480943190977097479) = (W64.of_int 61221233266924, W64.of_int 4376993605794294712).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 61221233266924, W64.of_int 4376993605794294712) = (W64.of_int 88996237651031, W64.of_int 15464743600586630277).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 88996237651031, W64.of_int 15464743600586630277) = (W64.of_int 192478739059625, W64.of_int 2982000473525574522).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 2982000473525574522 `>>>` 63) `&` W64.one = W64.of_int 0.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 192478739059625, W64.of_int 2982000473525574522) (W64.of_int 0) = (W64.of_int 192478739059625, W64.of_int 2982000473525574522).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 192478739059625, W64.of_int 2982000473525574522) (W64.of_int 68864825180320, W64.of_int 4480943190977097479) = (W64.of_int 211205781071443, W64.of_int 4961457989078320386).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 211205781071443, W64.of_int 4961457989078320386) (W64.of_int 0) = (W64.of_int 211205781071443, W64.of_int 4961457989078320386).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_3_5 :
  hb_newton_step (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 211205781071443, W64.of_int 4961457989078320386) = (W64.of_int 101443927918593, W64.of_int 6515027660407619326).
proof.
  have hs : hb_square (W64.of_int 211205781071443, W64.of_int 4961457989078320386) = (W64.of_int 56841500350329, W64.of_int 15609856587917313555).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 233869965312719, W64.of_int 18417631402725) (W64.of_int 56841500350329, W64.of_int 15609856587917313555) = (W64.of_int 186434527646754, W64.of_int 8724340025448155756).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 186434527646754, W64.of_int 8724340025448155756) = (W64.of_int 95040449063902, W64.of_int 9722404048664049043).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 9722404048664049043 `>>>` 63) `&` W64.one = W64.of_int 1.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 95040449063902, W64.of_int 9722404048664049043) (W64.of_int 1) = (W64.of_int 186434527646754, W64.of_int 8724340025045502572).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 186434527646754, W64.of_int 8724340025045502572) (W64.of_int 211205781071443, W64.of_int 4961457989078320386) = (W64.of_int 180031048792063, W64.of_int 11931716413301932289).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 180031048792063, W64.of_int 11931716413301932289) (W64.of_int 1) = (W64.of_int 101443927918593, W64.of_int 6515027660407619326).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_5_0 :
  hb_newton_step (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 333906974325571, W64.of_int 18446744073698340199) = (W64.of_int 190770269349409, W64.of_int 3984293549753450583).
proof.
  have hs : hb_square (W64.of_int 333906974325571, W64.of_int 18446744073698340199) = (W64.of_int 258384829225034, W64.of_int 16905858679893391380).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 258384829225034, W64.of_int 16905858679893391380) = (W64.of_int 117399799316458, W64.of_int 16395046298941147181).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 117399799316458, W64.of_int 16395046298941147181) = (W64.of_int 164075177394198, W64.of_int 2051697775171057618).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 2051697775171057618 `>>>` 63) `&` W64.one = W64.of_int 0.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 164075177394198, W64.of_int 2051697775171057618) (W64.of_int 0) = (W64.of_int 164075177394198, W64.of_int 2051697775171057618).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 164075177394198, W64.of_int 2051697775171057618) (W64.of_int 333906974325571, W64.of_int 18446744073698340199) = (W64.of_int 190770269349409, W64.of_int 3984293549753450583).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 190770269349409, W64.of_int 3984293549753450583) (W64.of_int 0) = (W64.of_int 190770269349409, W64.of_int 3984293549753450583).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_5_1 :
  hb_newton_step (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 190770269349409, W64.of_int 3984293549753450583) = (W64.of_int 220285921059098, W64.of_int 7341622774493002597).
proof.
  have hs : hb_square (W64.of_int 190770269349409, W64.of_int 3984293549753450583) = (W64.of_int 241724948354119, W64.of_int 322207426211089339).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 241724948354119, W64.of_int 322207426211089339) = (W64.of_int 265064025715553, W64.of_int 17773852821609981747).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 265064025715553, W64.of_int 17773852821609981747) = (W64.of_int 16410950995103, W64.of_int 672891252502223052).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 672891252502223052 `>>>` 63) `&` W64.one = W64.of_int 0.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 16410950995103, W64.of_int 672891252502223052) (W64.of_int 0) = (W64.of_int 16410950995103, W64.of_int 672891252502223052).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 16410950995103, W64.of_int 672891252502223052) (W64.of_int 190770269349409, W64.of_int 3984293549753450583) = (W64.of_int 220285921059098, W64.of_int 7341622774493002597).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 220285921059098, W64.of_int 7341622774493002597) (W64.of_int 0) = (W64.of_int 220285921059098, W64.of_int 7341622774493002597).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_5_2 :
  hb_newton_step (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 220285921059098, W64.of_int 7341622774493002597) = (W64.of_int 175129914158558, W64.of_int 3061731672966679982).
proof.
  have hs : hb_square (W64.of_int 220285921059098, W64.of_int 7341622774493002597) = (W64.of_int 163210581629754, W64.of_int 14666046004459272775).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 163210581629754, W64.of_int 14666046004459272775) = (W64.of_int 244105013804634, W64.of_int 457581010945635139).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 244105013804634, W64.of_int 457581010945635139) = (W64.of_int 37369962906022, W64.of_int 17989163063166569660).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 17989163063166569660 `>>>` 63) `&` W64.one = W64.of_int 1.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 37369962906022, W64.of_int 17989163063166569660) (W64.of_int 1) = (W64.of_int 244105013804634, W64.of_int 457581010542981955).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 244105013804634, W64.of_int 457581010542981955) (W64.of_int 220285921059098, W64.of_int 7341622774493002597) = (W64.of_int 106345062552098, W64.of_int 15385012400742871633).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 106345062552098, W64.of_int 15385012400742871633) (W64.of_int 1) = (W64.of_int 175129914158558, W64.of_int 3061731672966679982).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_5_3 :
  hb_newton_step (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 175129914158558, W64.of_int 3061731672966679982) = (W64.of_int 6293551730198, W64.of_int 15404556116879321663).
proof.
  have hs : hb_square (W64.of_int 175129914158558, W64.of_int 3061731672966679982) = (W64.of_int 221218180493251, W64.of_int 16561373991891590210).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 221218180493251, W64.of_int 16561373991891590210) = (W64.of_int 183936756145912, W64.of_int 5077419526807466210).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 183936756145912, W64.of_int 5077419526807466210) = (W64.of_int 97538220564744, W64.of_int 13369324547304738589).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 13369324547304738589 `>>>` 63) `&` W64.one = W64.of_int 1.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 97538220564744, W64.of_int 13369324547304738589) (W64.of_int 1) = (W64.of_int 183936756145912, W64.of_int 5077419526404813026).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 183936756145912, W64.of_int 5077419526404813026) (W64.of_int 175129914158558, W64.of_int 3061731672966679982) = (W64.of_int 275181424980458, W64.of_int 3042187956830229952).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 275181424980458, W64.of_int 3042187956830229952) (W64.of_int 1) = (W64.of_int 6293551730198, W64.of_int 15404556116879321663).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_5_4 :
  hb_newton_step (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 6293551730198, W64.of_int 15404556116879321663) = (W64.of_int 62117919499292, W64.of_int 12627326120501435115).
proof.
  have hs : hb_square (W64.of_int 6293551730198, W64.of_int 15404556116879321663) = (W64.of_int 175325887120449, W64.of_int 69228531064926824).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 175325887120449, W64.of_int 69228531064926824) = (W64.of_int 179720924409805, W64.of_int 5736924171078433101).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 179720924409805, W64.of_int 5736924171078433101) = (W64.of_int 101754052300851, W64.of_int 12709819903033771698).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 12709819903033771698 `>>>` 63) `&` W64.one = W64.of_int 1.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 101754052300851, W64.of_int 12709819903033771698) (W64.of_int 1) = (W64.of_int 179720924409805, W64.of_int 5736924170675779917).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 179720924409805, W64.of_int 5736924170675779917) (W64.of_int 6293551730198, W64.of_int 15404556116879321663) = (W64.of_int 219357057211364, W64.of_int 5819417953208116500).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 219357057211364, W64.of_int 5819417953208116500) (W64.of_int 1) = (W64.of_int 62117919499292, W64.of_int 12627326120501435115).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_step_5_5 :
  hb_newton_step (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 62117919499292, W64.of_int 12627326120501435115) = (W64.of_int 51879773209874, W64.of_int 14033702225847268899).
proof.
  have hs : hb_square (W64.of_int 62117919499292, W64.of_int 12627326120501435115) = (W64.of_int 246250901409272, W64.of_int 14346635618401114992).
  + rewrite /hb_square /square_word /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hp : hb_mul (W64.of_int 271553062191832, W64.of_int 2811826814609) (W64.of_int 246250901409272, W64.of_int 14346635618401114992) = (W64.of_int 187798031740553, W64.of_int 11982363402240274345).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ht : hb_threehalves_minus (W64.of_int 187798031740553, W64.of_int 11982363402240274345) = (W64.of_int 93676944970103, W64.of_int 6464380671871930454).
  + rewrite /hb_threehalves_minus /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hsign : (W64.of_int 6464380671871930454 `>>>` 63) `&` W64.one = W64.of_int 0.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have ha : hb_cneg (W64.of_int 93676944970103, W64.of_int 6464380671871930454) (W64.of_int 0) = (W64.of_int 93676944970103, W64.of_int 6464380671871930454).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hm : hb_mul (W64.of_int 93676944970103, W64.of_int 6464380671871930454) (W64.of_int 62117919499292, W64.of_int 12627326120501435115) = (W64.of_int 51879773209874, W64.of_int 14033702225847268899).
  + rewrite /hb_mul /=.
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  have hc : hb_cneg (W64.of_int 51879773209874, W64.of_int 14033702225847268899) (W64.of_int 0) = (W64.of_int 51879773209874, W64.of_int 14033702225847268899).
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
  by rewrite /hb_newton_step hs hp ht /hb_signed_mul /= ?hsign ha hm hc.
qed.

lemma hbw_newton_exact (mode : int) : hbw_mode mode =>
  hb_newton (hbw_half mode) (hb_ref_cube mode) (hb_ref_three mode) = hbw_inverse mode.
proof.
  move=> hm; rewrite /hb_newton (hbw_newton_initial_exact mode hm).
  rewrite (hb_newton_iterS (hbw_half mode) (hbw_first mode) 5) 1://
    (hb_newton_iterS (hbw_half mode) (hbw_first mode) 4) 1://
    (hb_newton_iterS (hbw_half mode) (hbw_first mode) 3) 1://
    (hb_newton_iterS (hbw_half mode) (hbw_first mode) 2) 1://
    (hb_newton_iterS (hbw_half mode) (hbw_first mode) 1) 1://
    (hb_newton_iterS (hbw_half mode) (hbw_first mode) 0) 1://
    hb_newton_iter0.
  move: hm; rewrite /hbw_mode; move=> [-> | [-> | ->]];
    rewrite /hbw_half /hbw_first /hbw_inverse /=;
    by rewrite ?hbw_newton_step_2_0 ?hbw_newton_step_2_1 ?hbw_newton_step_2_2 ?hbw_newton_step_2_3 ?hbw_newton_step_2_4 ?hbw_newton_step_2_5 ?hbw_newton_step_3_0 ?hbw_newton_step_3_1 ?hbw_newton_step_3_2 ?hbw_newton_step_3_3 ?hbw_newton_step_3_4 ?hbw_newton_step_3_5 ?hbw_newton_step_5_0 ?hbw_newton_step_5_1 ?hbw_newton_step_5_2 ?hbw_newton_step_5_3 ?hbw_newton_step_5_4 ?hbw_newton_step_5_5.
qed.

lemma hbw_scale_exact (mode : int) : hbw_mode mode =>
  hb_mul_high (hbw_inverse mode) (hb_ref_scale mode) = hbw_scale mode.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    rewrite /hbw_inverse /hb_ref_scale /hbw_scale /hb_mul_high /=;
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
qed.

op hbw_full_magnitude (mode : int) : int =
  if mode=2 then 412929335944226
  else if mode=3 then 448613294232468
  else if mode=5 then 545876826280812
  else 0.

lemma hbw_magnitude_exact (mode : int) : hbw_mode mode =>
  hb_rnd13_magnitude (hbw_sample mode) (hbw_scale mode) = hbw_full_magnitude mode.
proof.
  rewrite /hbw_mode; move=> [-> | [-> | ->]];
    rewrite /hbw_sample /hbw_scale /hbw_full_magnitude /hb_rnd13_magnitude /hb_mul /=;
    by do 16! (rewrite ?hwe_mul48 ?hwe_mulu ?hwe_cneg0 ?hwe_cneg1 ?hwe_norm /=
      ?hwe_add ?hwe_sub ?hwe_mul ?hwe_shl ?hwe_shr
      ?hwe_mask48 ?hwe_mask32 ?hwe_mask1 ?hwe_uint //=).
qed.

lemma hbw_coefficient_exact (mode : int) : hbw_mode mode =>
  hb_mul_rnd13 (hbw_sample mode) (hbw_scale mode) W64.zero = W32.of_int (hbw_coefficient mode).
proof.
  move=> hm.
  have h := hss_mul_rnd13_word (hbw_sample mode) (hbw_scale mode) false.
  rewrite /hss_apply_sign /b2i /= (hbw_magnitude_exact mode hm) in h.
  rewrite h; move: hm; rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hbw_full_magnitude /hbw_coefficient /=.
qed.

lemma hbw_magnitude_overflow (mode : int) : hbw_mode mode =>
  2147483647 < hb_rnd13_magnitude (hbw_sample mode) (hbw_scale mode).
proof.
  move=> hm; rewrite (hbw_magnitude_exact mode hm).
  move: hm; rewrite /hbw_mode; move=> [-> | [-> | ->]];
    by rewrite /hbw_full_magnitude.
qed.

lemma hbw_newton_initial_negative (mode : int) : hbw_mode mode =>
  W64.to_sint (hb_newton_initial (hbw_half mode) (hb_ref_cube mode)
    (hb_ref_three mode)).`2 < 0.
proof.
  move=> hm; rewrite (hbw_newton_initial_exact mode hm).
  exact (hbw_first_negative mode hm).
qed.
