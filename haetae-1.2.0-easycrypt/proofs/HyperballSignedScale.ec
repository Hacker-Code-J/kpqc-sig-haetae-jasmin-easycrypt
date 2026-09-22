require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import HyperballFixedPointSpec HyperballFixedPointCorrectness
  HyperballScaleSpec HyperballScaleCorrectness GaussianIidBufferSpec GaussianSignBits.
import HyperballScaleSpec HyperballScaleCorrectness.

(* Magnitudes below are decoded AFTER the implemented word multiplication,
   addition and rounding. The scale may be any two-word value; no ideal real
   multiplication or absence of intermediate wrap is asserted. *)
op hss_apply_sign (negative : bool) (magnitude : int) : int =
  if negative then -magnitude else magnitude.

op hss_coeff_magnitude (samples : BArray32768.t) (scale : BArray16.t) (i : int) : int =
  hb_rnd13_magnitude (BArray32768.get64 samples i) (hb_load scale).

op hss_negative (signs : BArray512.t) (i : int) : bool =
  hb_sign_bit signs i <> W8.zero.

op hss_coeff_integer (samples : BArray32768.t) (signs : BArray512.t)
    (scale : BArray16.t) (i : int) : int =
  hss_apply_sign (hss_negative signs i) (hss_coeff_magnitude samples scale i).

op hss_vector (samples : BArray32768.t) (signs : BArray512.t)
    (scale : BArray16.t) (count : int) : int list =
  map (hss_coeff_integer samples signs scale) (iota_ 0 count).

op hss_observe (out1 out2 : BArray8192.t) (left_count count : int) : int list =
  map (fun i => W32.to_sint (if i < left_count then BArray8192.get32 out1 i
    else BArray8192.get32 out2 (i-left_count))) (iota_ 0 count).

lemma hss_magnitude_range (sample : W64.t) (scale : hb_fp) :
  0 <= hb_rnd13_magnitude sample scale < 562949953421312.
proof.
  rewrite /hb_rnd13_magnitude /= W64.to_uint_shr //=.
  apply divz_cmp; first trivial.
  exact W64.to_uint_cmp.
qed.

lemma hss_sign_extend_bool (negative : bool) :
  zeroextu64 (W8.of_int (b2i negative)) = W64.of_int (b2i negative).
proof.
  apply W64.to_uint_eq.
  rewrite W8u8.to_uint_zeroextu64 W8.of_uintK W64.of_uintK /b2i.
  by case negative => /=.
qed.

lemma hss_sign_truncate_word (rounded : W64.t) (negative : bool) :
  truncateu32 ((rounded `^` (W64.zero - W64.of_int (b2i negative))) +
    W64.of_int (b2i negative)) =
  W32.of_int (hss_apply_sign negative (W64.to_uint rounded)).
proof.
  have hmask : W64.of_int 18446744073709551615 = W64.onew by rewrite W64.oneE.
  rewrite /hss_apply_sign /b2i; case negative => hn /=.
  + rewrite hmask W64.xorw1 -W64.twos_compl.
    by rewrite -{1}(W64.to_uintK rounded) -W64.of_intN hb_truncate_of_int.
  by rewrite -{1}(W64.to_uintK rounded) hb_truncate_of_int.
qed.

lemma hss_mul_rnd13_word (sample : W64.t) (scale : hb_fp) (negative : bool) :
  hb_mul_rnd13 sample scale (W64.of_int (b2i negative)) =
    W32.of_int (hss_apply_sign negative (hb_rnd13_magnitude sample scale)).
proof.
  pose rounded := ((hb_mul
    ((sample `&` W64.of_int 4294967295) `<<<` 16, sample `>>>` 32) scale).`2 +
    W64.of_int 16384) `>>>` 15.
  have h := hss_sign_truncate_word rounded negative.
  by move: h; rewrite /rounded /hb_mul_rnd13 /hb_rnd13_magnitude /=.
qed.

lemma hss_mul_rnd13_signed_fit (sample : W64.t) (scale : hb_fp) (negative : bool) :
  hb_rnd13_magnitude sample scale <= 2147483647 =>
  W32.to_sint (hb_mul_rnd13 sample scale (W64.of_int (b2i negative))) =
    hss_apply_sign negative (hb_rnd13_magnitude sample scale).
proof.
  move=> hf; rewrite /hss_apply_sign /b2i; case negative => hn /=.
  + have h := hb_mul_rnd13_signed_fit sample scale W64.one _ hf; first by right.
    by move: h; rewrite W64.to_uint_eq W64.to_uint1 W64.to_uint0 /=.
  have h := hb_mul_rnd13_signed_fit sample scale W64.zero _ hf; first by left.
  by move: h; rewrite /=.
qed.

lemma hss_regs_word_total (sample : W64.t) (scale : hb_fp) (negative : bool) :
  phoare [HB.__fixpoint_mul_rnd13_regs :
    x = sample /\ y0 = scale.`1 /\ y1 = scale.`2 /\
    sign = W64.of_int (b2i negative) ==>
    res = W32.of_int (hss_apply_sign negative (hb_rnd13_magnitude sample scale))] = 1%r.
proof.
  conseq (hb_mul_rnd13_regs_total sample scale.`1 scale.`2
    (W64.of_int (b2i negative))) => />.
  rewrite -pairS.
  move=> &hr hy0 hy1 hs.
  by rewrite hss_mul_rnd13_word.
qed.

lemma hss_regs_signed_total (sample : W64.t) (scale : hb_fp) (negative : bool) :
  phoare [HB.__fixpoint_mul_rnd13_regs :
    x = sample /\ y0 = scale.`1 /\ y1 = scale.`2 /\
    sign = W64.of_int (b2i negative) /\
    hb_rnd13_magnitude sample scale <= 2147483647 ==>
    W32.to_sint res = hss_apply_sign negative (hb_rnd13_magnitude sample scale)] = 1%r.
proof.
  conseq hb_mul_rnd13_regs_ll
    (hb_mul_rnd13_regs_correct sample scale.`1 scale.`2 (W64.of_int (b2i negative))) => //.
  move=> &m hpre result.
  have hf : hb_rnd13_magnitude sample scale <= 2147483647 by smt().
  have h := hss_mul_rnd13_signed_fit sample scale negative hf.
  rewrite -pairS; smt().
qed.

lemma hss_scalar_word_total (sample : W64.t) (scale : BArray16.t) (negative : bool) :
  phoare [HB._fixpoint_mul_rnd13 :
    x = sample /\ yp = scale /\ sign = W8.of_int (b2i negative) ==>
    res = W32.of_int (hss_apply_sign negative (hb_rnd13_magnitude sample (hb_load scale)))] = 1%r.
proof.
  conseq hb_mul_rnd13_ll
    (hb_mul_rnd13_correct sample scale (W8.of_int (b2i negative))) => //.
  move=> &m hpre result.
  have h : hb_scale_sample sample scale (W8.of_int (b2i negative)) =
      W32.of_int (hss_apply_sign negative (hb_rnd13_magnitude sample (hb_load scale))).
  + by rewrite /hb_scale_sample hss_sign_extend_bool hss_mul_rnd13_word.
  smt().
qed.

lemma hss_scalar_signed_total (sample : W64.t) (scale : BArray16.t) (negative : bool) :
  phoare [HB._fixpoint_mul_rnd13 :
    x = sample /\ yp = scale /\ sign = W8.of_int (b2i negative) /\
    hb_rnd13_magnitude sample (hb_load scale) <= 2147483647 ==>
    W32.to_sint res =
      hss_apply_sign negative (hb_rnd13_magnitude sample (hb_load scale))] = 1%r.
proof.
  conseq hb_mul_rnd13_ll
    (hb_mul_rnd13_correct sample scale (W8.of_int (b2i negative))) => //.
  move=> &m hpre result.
  have hf : hb_rnd13_magnitude sample (hb_load scale) <= 2147483647 by smt().
  have h : W32.to_sint (hb_scale_sample sample scale (W8.of_int (b2i negative))) =
      hss_apply_sign negative (hb_rnd13_magnitude sample (hb_load scale)).
  + rewrite /hb_scale_sample hss_sign_extend_bool.
    exact (hss_mul_rnd13_signed_fit sample (hb_load scale) negative hf).
  smt().
qed.

lemma hss_negative_bit (signs : BArray512.t) (i : int) :
  hss_negative signs i = (BArray512.get8 signs (i %/ 8)).[i %% 8].
proof.
  rewrite /hss_negative /hb_sign_bit /b2i.
  case (BArray512.get8 signs (i %/ 8)).[i %% 8] => hs /=.
  + by rewrite W8.to_uint_eq W8.to_uint1 W8.to_uint0.
  trivial.
qed.

lemma hss_coeff_word samples signs scale i :
  hb_scaled_coeff samples signs scale i = W32.of_int (hss_coeff_integer samples signs scale i).
proof.
  rewrite /hb_scaled_coeff /hb_scale_sample hb_sign_extend hss_mul_rnd13_word.
  by rewrite /hss_coeff_integer /hss_coeff_magnitude hss_negative_bit.
qed.

lemma hss_coeff_signed_fit samples signs scale i :
  hss_coeff_magnitude samples scale i <= 2147483647 =>
  W32.to_sint (hb_scaled_coeff samples signs scale i) = hss_coeff_integer samples signs scale i.
proof.
  move=> hf; rewrite /hss_coeff_integer /hss_coeff_magnitude hss_negative_bit /hss_apply_sign.
  exact (hb_scaled_coeff_signed_fit samples signs scale i hf).
qed.

lemma hss_indexed_scalar_total samples signs scale i :
  phoare [HB._fixpoint_mul_rnd13 :
    x = BArray32768.get64 samples i /\ yp = scale /\ sign = hb_sign_bit signs i /\
    hss_coeff_magnitude samples scale i <= 2147483647 ==>
    W32.to_sint res = hss_coeff_integer samples signs scale i] = 1%r.
proof.
  conseq hb_mul_rnd13_ll
    (hb_mul_rnd13_correct (BArray32768.get64 samples i) scale (hb_sign_bit signs i)) => //.
  move=> &m hpre result.
  have hf : hss_coeff_magnitude samples scale i <= 2147483647 by smt().
  have h := hss_coeff_signed_fit samples signs scale i hf.
  rewrite /hb_scaled_coeff in h; smt().
qed.

lemma hss_scale_result_observation before1 before2 samples signs scale left_count count :
  hb_scale_bounds left_count count =>
  (forall i, 0 <= i < count => hss_coeff_magnitude samples scale i <= 2147483647) =>
  hss_observe (hb_scale_result before1 before2 samples signs scale left_count count).`1
    (hb_scale_result before1 before2 samples signs scale left_count count).`2 left_count count =
    hss_vector samples signs scale count.
proof.
  move=> hb hf; have [hfirst [hsecond hframe]] :=
    hb_scale_result_layout before1 before2 samples signs scale left_count count hb.
  have [hl [hr ht]] : 0 <= left_count <= 2048 /\ 0 <= count-left_count <= 2048 /\ count <= 4096
    by exact hb.
  rewrite /hss_observe /hss_vector; apply eq_in_map => i; rewrite mem_iota /= => hi.
  have hir : 0 <= i < count by smt().
  case (i < left_count) => his /=.
  + rewrite (hfirst i _) 1:/# his /=.
    exact (hss_coeff_signed_fit samples signs scale i (hf i hir)).
  have hidx : 0 <= i-left_count < 2048 by smt().
  have hactive : i-left_count < count-left_count by smt().
  rewrite (hsecond (i-left_count) hidx) hactive /=.
  have -> : left_count+(i-left_count) = i by ring.
  exact (hss_coeff_signed_fit samples signs scale i (hf i hir)).
qed.

lemma hss_scale_samples_signed_total
    (before1 before2 : BArray8192.t) (samples : BArray32768.t)
    (signs : BArray512.t) (scale : BArray16.t) (left_count count : int) :
  phoare [HS._polyfixveclk_scale_samples :
    y1p = before1 /\ y2p = before2 /\ samplesp = samples /\ signsp = signs /\ scalep = scale /\
    counts = W64.of_int (count*4294967296+left_count) /\ hb_scale_bounds left_count count /\
    (forall i, 0 <= i < count => hss_coeff_magnitude samples scale i <= 2147483647) ==>
    hss_observe res.`1 res.`2 left_count count = hss_vector samples signs scale count] = 1%r.
proof.
  conseq hb_scale_samples_ll
    (hb_scale_samples_correct before1 before2 samples signs scale left_count count) => //.
  move=> &m hpre result.
  have hb : hb_scale_bounds left_count count by smt().
  have hf : forall i, 0 <= i < count => hss_coeff_magnitude samples scale i <= 2147483647 by smt().
  have h := hss_scale_result_observation before1 before2 samples signs scale left_count count hb hf.
  smt().
qed.

lemma hss_local_negative (result : gib_result) (signoff i : int) :
  0 <= i < 256 =>
  hss_negative result.`2 (8*signoff+i) = nth false (gsb_result_bits result signoff) i.
proof.
  move=> hi; rewrite /hss_negative (gsb_hb_sign_bit result signoff i hi) /b2i.
  case (nth false (gsb_result_bits result signoff) i) => hs /=.
  + by rewrite W8.to_uint_eq W8.to_uint1 W8.to_uint0.
  trivial.
qed.

(* A local sign window addresses global coefficient8*signoff+i. The
   sampler's sample and sign offsets are separate inputs, so the alignment
   is an explicit premise in these local observations. *)
lemma hss_local_coeff_word (result : gib_result) (scale : BArray16.t)
    (sample_offset signoff i : int) :
  sample_offset = 8*signoff => 0 <= i < 256 =>
  hb_scaled_coeff result.`1 result.`2 scale (sample_offset+i) =
    W32.of_int (hss_apply_sign (nth false (gsb_result_bits result signoff) i)
      (hss_coeff_magnitude result.`1 scale (sample_offset+i))).
proof.
  move=> -> hi.
  by rewrite hss_coeff_word /hss_coeff_integer (hss_local_negative result signoff i hi).
qed.

lemma hss_local_coeff_signed_fit (result : gib_result) (scale : BArray16.t)
    (sample_offset signoff i : int) :
  sample_offset = 8*signoff => 0 <= i < 256 =>
  hss_coeff_magnitude result.`1 scale (sample_offset+i) <= 2147483647 =>
  W32.to_sint (hb_scaled_coeff result.`1 result.`2 scale (sample_offset+i)) =
    hss_apply_sign (nth false (gsb_result_bits result signoff) i)
      (hss_coeff_magnitude result.`1 scale (sample_offset+i)).
proof.
  move=> -> hi hf.
  by rewrite (hss_coeff_signed_fit result.`1 result.`2 scale (8*signoff+i) hf)
    /hss_coeff_integer (hss_local_negative result signoff i hi).
qed.
