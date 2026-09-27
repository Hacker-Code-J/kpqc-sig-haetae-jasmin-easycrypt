require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import HardenedHyperballTarget CheckedScalarCorrectness CheckedNormCorrectness
  HyperballNormSpec HyperballScaleSpec.
import SLH64 HyperballScaleSpec.

module HCA = HardenedHyperballTarget.M.

op hca_finish (bad overflow compare : W64.t) : W64.t =
  (((bad `|` overflow) `|` compare) `^` W64.of_int (-1)) `&` W64.one.

lemma hca_sbb_mask (x : W64.t) (borrow : bool) :
  (W64.subc x x borrow).`2 = W64.of_int (-b2i borrow).
proof. rewrite W64.subcE /= W64.of_intN; ring. qed.

lemma hca_negative_boolean_bit (b : bool) :
  (W64.of_int (-b2i b)).[0] = b.
proof.
  have h := W64.b2i_get (W64.of_int (-b2i b)) 0 _; first trivial.
  move: h; rewrite W64.of_uintK /b2i /=.
  by case b => /=; smt().
qed.

lemma hca_finish_bit (bad overflow compare : W64.t) :
  hca_finish bad overflow compare =
    W64.of_int (b2i (!bad.[0] /\ !overflow.[0] /\ !compare.[0])).
proof.
  apply W64.wordP => i hi.
  rewrite /hca_finish W64.andwE W64.xorwE !W64.orwE W64.nth_one.
  have hall : W64.of_int (-1) = W64.onew by
    apply W64.to_uint_eq; rewrite W64.of_uintK W64.to_uint_onew.
  rewrite hall W64.onewE hi /=.
  case (i=0) => [->|hi0] /=.
  + rewrite /b2i; case bad.[0]; case overflow.[0]; case compare.[0] => /=;
      rewrite ?W64.nth_one ?W64.zerowE; smt().
  rewrite /b2i; case (!bad.[0] /\ !overflow.[0] /\ !compare.[0]) => /=;
    rewrite ?W64.nth_one ?W64.zerowE; smt().
qed.

lemma hca_finish_boolean (bad overflow compare : W64.t) :
  hca_finish bad overflow compare = W64.zero \/
  hca_finish bad overflow compare = W64.one.
proof.
  rewrite hca_finish_bit /b2i.
  by case (!bad.[0] /\ !overflow.[0] /\ !compare.[0]) => /=; smt().
qed.

lemma hca_finish_safe (bad bound : W64.t) (norm : int) :
  0 <= norm =>
  hca_finish bad (W64.of_int (-b2i (W64.modulus<=norm)))
    (W64.of_int (-b2i (W64.to_uint bound<W64.to_uint (W64.of_int norm)))) = W64.one =>
  norm <= W64.to_uint bound.
proof.
  move=> hn; rewrite hca_finish_bit !hca_negative_boolean_bit /b2i.
  case (W64.modulus<=norm) => hover /=.
  + by rewrite W64.to_uint_eq /=.
  rewrite W64.to_uint_small 1:/#.
  case (W64.to_uint bound<norm) => hcmp /=.
  + by rewrite W64.to_uint_eq /=.
  smt().
qed.

lemma hca_final_word (bad overflow norm bound : W64.t) :
  let sub = W64.subc bound norm false in
  (((bad `|` overflow) `|` (W64.subc sub.`2 sub.`2 sub.`1).`2)
    `^` W64.of_int 18446744073709551615) `&` W64.one =
  hca_finish bad overflow (W64.of_int (-b2i (W64.to_uint bound<W64.to_uint norm))).
proof.
  by rewrite /= hca_sbb_mask W64.subcE /W64.borrow_sub /hca_finish /=.
qed.

lemma hca_bit_at_ll : islossless HCA.__bit_at_u8.
proof. proc; islossless. qed.

lemma hca_scale_samples_ll : islossless HCA._hb_checked_scale_samples.
proof.
  proc.
  while (true) (W64.to_uint total-W64.to_uint i).
  + move=> z; wp; call hcs_pointer_ll.
    wp; call hca_bit_at_ll.
    auto => /> &hr hguard.
    rewrite /protect_64 /protect_ptr.
    have /= ht := W64.to_uint_cmp total{hr}.
    rewrite W64.ultE in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
  wp.
  while (true) (W64.to_uint lcount-W64.to_uint i).
  + move=> z; wp; call hcs_pointer_ll.
    wp; call hca_bit_at_ll.
    auto => /> &hr hguard.
    rewrite /protect_64 /protect_ptr.
    have /= hl := W64.to_uint_cmp lcount{hr}.
    rewrite W64.ultE in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
  auto => />; smt(W64.ultE W64.to_uint_cmp).
qed.

lemma hca_scale_and_check_boolean :
  hoare [HCA._hb_checked_scale_and_check_values : true ==>
    res.`3=W64.zero \/ res.`3=W64.one].
proof.
  proc; wp; call (_ : true ==> true); first by conseq.
  wp; call (_ : true ==> true); first by conseq.
  auto => />; rewrite /protect_64; smt(hca_final_word hca_finish_boolean).
qed.

lemma hca_scale_and_check_safe_bit (l t : int) (bound0 : W64.t) :
  hoare [HCA._hb_checked_scale_and_check_values :
    lcount=W64.of_int l /\ total=W64.of_int t /\ bound=bound0 /\ hb_scale_bounds l t ==>
    (res.`3=W64.zero \/ res.`3=W64.one) /\
    (res.`3=W64.one => hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0)].
proof.
  proc; wp; ecall (checked_sqnorm2_correct y1p l y2p (t-l)).
  wp; call (_ : true ==> true); first by conseq.
  auto => />; rewrite /protect_64 /protect_ptr -W64.of_intS.
  move=> hl0 hlmax hk0 hkmax ht result; split; first trivial.
  move=> _ _ result0 -> ->.
  rewrite hca_final_word /cn_overflow_mask.
  split; first apply hca_finish_boolean.
  apply hca_finish_safe.
  exact (hyperball_sqnorm_nonnegative result.`1 l result.`2 (t-l) hl0 hk0).
qed.

lemma hca_scale_and_check_safe (l t : int) (bound0 : W64.t) :
  hoare [HCA._hb_checked_scale_and_check_values :
    lcount=W64.of_int l /\ total=W64.of_int t /\ bound=bound0 /\ hb_scale_bounds l t ==>
    res.`3=W64.one => hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0].
proof. conseq (hca_scale_and_check_safe_bit l t bound0) => />; smt(). qed.

lemma hca_scale_and_check_ll : islossless HCA._hb_checked_scale_and_check_values.
proof.
  proc; wp; call checked_sqnorm2_ll.
  wp; call hca_scale_samples_ll.
  auto => />; smt().
qed.

lemma hca_scale_and_check_total (l t : int) (bound0 : W64.t) :
  phoare [HCA._hb_checked_scale_and_check_values :
    lcount=W64.of_int l /\ total=W64.of_int t /\ bound=bound0 /\ hb_scale_bounds l t ==>
    (res.`3=W64.zero \/ res.`3=W64.one) /\
    (res.`3=W64.one => hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0)] = 1%r.
proof.
  by conseq hca_scale_and_check_ll (hca_scale_and_check_safe_bit l t bound0).
qed.
