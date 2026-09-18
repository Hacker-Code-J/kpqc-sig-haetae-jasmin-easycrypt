require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import HyperballSpec HyperballHistoryCorrectness HyperballScaleSpec HyperballNormSpec.
import HyperballScaleSpec.

lemma hb_history_modular_norm seed base l k cube three scale bound initial1 initial2 history
    current1 current2 :
  hb_history seed base l k cube three scale bound initial1 initial2 history
    current1 current2 W64.one =>
  hyperball_sqnorm current1 (256 * l) current2 (256 * k) %% W64.modulus <= W64.to_uint bound.
proof.
  move=> [hc [hr hlast]].
  have h10 : W64.one <> W64.zero by rewrite W64.to_uint_eq W64.to_uint1 W64.to_uint0.
  have hne : history <> [] by smt().
  have hout : (current1, current2) = hb_attempt_outputs initial1 initial2
      (last witness history) l k cube three scale by smt().
  have hp := hb_boolean_word_one (hb_attempt_accept initial1 initial2
    (last witness history) l k cube three scale bound).
  have ha : hb_attempt_accept initial1 initial2 (last witness history)
      l k cube three scale bound by smt().
  move: ha; rewrite /hb_attempt_accept -hout; trivial.
qed.

lemma hb_result_modular_norm seed base l k cube three scale bound initial1 initial2
    current1 current2 byte_result counter_result :
  hb_result seed base l k cube three scale bound initial1 initial2 current1 current2
    byte_result counter_result =>
  hyperball_sqnorm current1 (256 * l) current2 (256 * k) %% W64.modulus <= W64.to_uint bound.
proof.
  move=> [history [hn [hh _]]].
  exact (hb_history_modular_norm seed base l k cube three scale bound initial1 initial2
    history current1 current2 hh).
qed.

lemma hb_result_output_frames seed base l k cube three scale bound initial1 initial2
    current1 current2 byte_result counter_result :
  hb_shape l k =>
  hb_result seed base l k cube three scale bound initial1 initial2 current1 current2
    byte_result counter_result =>
  hb_output_frame initial1 current1 (256 * l) /\ hb_output_frame initial2 current2 (256 * k).
proof.
  move=> hshape [history [hn [hh _]]].
  exact (hb_history_frames seed base l k cube three scale bound initial1 initial2
    history current1 current2 W64.one hshape hh).
qed.

lemma hb_result_integer_norm seed base l k cube three scale bound initial1 initial2
    current1 current2 byte_result counter_result :
  hb_shape l k =>
  hb_result seed base l k cube three scale bound initial1 initial2 current1 current2
    byte_result counter_result =>
  hyperball_sqnorm current1 (256 * l) current2 (256 * k) < W64.modulus =>
  hyperball_sqnorm current1 (256 * l) current2 (256 * k) <= W64.to_uint bound.
proof.
  move=> hs hr hfit.
  have ha := hb_result_modular_norm seed base l k cube three scale bound initial1 initial2
    current1 current2 byte_result counter_result hr.
  have hn := hyperball_sqnorm_nonnegative current1 (256 * l) current2 (256 * k) _ _;
    first 2 by move: hs; rewrite /hb_shape; smt().
  move: ha; rewrite modz_small 1:/#; trivial.
qed.

lemma hb_result_26bit_integer_norm seed base l k cube three scale bound initial1 initial2
    current1 current2 byte_result counter_result :
  hb_shape l k =>
  hb_result seed base l k cube three scale bound initial1 initial2 current1 current2
    byte_result counter_result =>
  hyperball_coeff_bound current1 (256 * l) 67108864 =>
  hyperball_coeff_bound current2 (256 * k) 67108864 =>
  hyperball_sqnorm current1 (256 * l) current2 (256 * k) <= W64.to_uint bound.
proof.
  move=> hs hr h1 h2.
  have [_ hfit] := hyperball_sqnorm_26bit_no_overflow current1 (256 * l)
    current2 (256 * k) _ _ _ h1 h2; first 3 by move: hs; rewrite /hb_shape; smt().
  exact (hb_result_integer_norm seed base l k cube three scale bound initial1 initial2
    current1 current2 byte_result counter_result hs hr hfit).
qed.

lemma hb_signed32_norm_range l k (current1 current2 : BArray8192.t) :
  hb_shape l k =>
  0 <= hyperball_sqnorm current1 (256 * l) current2 (256 * k) <= 704 * W64.modulus.
proof.
  move=> hs.
  have h1 : hyperball_coeff_bound current1 (256 * l) 2147483648.
  + move=> i hi; have := W32.to_sint_cmp (BArray8192.get32 current1 i); smt().
  have h2 : hyperball_coeff_bound current2 (256 * k) 2147483648.
  + move=> i hi; have := W32.to_sint_cmp (BArray8192.get32 current2 i); smt().
  have hn := hyperball_sqnorm_nonnegative current1 (256 * l) current2 (256 * k) _ _;
    first 2 by move: hs; rewrite /hb_shape; smt().
  have hb := hyperball_sqnorm_bound current1 (256 * l) current2 (256 * k)
    2147483648 _ _ _ h1 h2; first 3 by move: hs; rewrite /hb_shape; smt().
  move: hs; rewrite /hb_shape /=; smt().
qed.

(* The extra disjunct cannot be removed from the modular norm condition alone:
   HyperballNormBoundary supplies an arithmetic witness, without asserting
   that any actual SHAKE seed reaches that witness. *)
lemma hb_result_integer_or_wrap seed base l k cube three scale bound initial1 initial2
    current1 current2 byte_result counter_result :
  hb_shape l k =>
  hb_result seed base l k cube three scale bound initial1 initial2 current1 current2
    byte_result counter_result =>
  hyperball_sqnorm current1 (256 * l) current2 (256 * k) <= W64.to_uint bound \/
  W64.modulus <= hyperball_sqnorm current1 (256 * l) current2 (256 * k).
proof.
  move=> hs hr.
  case (hyperball_sqnorm current1 (256 * l) current2 (256 * k) < W64.modulus) => hfit.
  + have h := hb_result_integer_norm seed base l k cube three scale bound initial1 initial2
      current1 current2 byte_result counter_result hs hr hfit; smt().
  smt().
qed.
