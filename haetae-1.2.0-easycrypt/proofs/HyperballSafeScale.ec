require import AllCore IntDiv StdOrder.
from Jasmin require import JModel_x86.
require import HyperballFixedPointSpec HyperballFixedPointCorrectness
  HyperballSafeSpec HyperballSafeConstants HyperballReferenceConstants
  HyperballWordEvaluation SigmaSpec SigmaSquareExact HyperballMulBounds
  HyperballScaleSpec HyperballScaleCorrectness HyperballNormSpec.

import HyperballScaleSpec HyperballScaleCorrectness.

(* The masked shift is allowed to wrap. Its retained radix slice, every
   addition, and the final normalization are accounted for separately. *)
lemma hsa_high_join (a hi bh : W64.t) :
  W64.to_uint a < 281474976710656 =>
  W64.to_uint hi < 562949953421312 => W64.to_uint bh <= 262144 =>
  hbs_canonical (hb_norm
    (((a+(W64.one `<<<` 27)) `>>>` 28)+
      ((hi `<<<` 20) `&` W64.of_int 281474976710655),
     (hi `>>>` 28)+(bh `<<<` 20))) /\
  hb_value (hb_norm
    (((a+(W64.one `<<<` 27)) `>>>` 28)+
      ((hi `<<<` 20) `&` W64.of_int 281474976710655),
     (hi `>>>` 28)+(bh `<<<` 20))) =
    (W64.to_uint a+134217728) %/ 268435456 +
      1048576*W64.to_uint hi + 295147905179352825856*W64.to_uint bh.
proof.
  move=> ha hhi hbh.
  have hau := W64.to_uint_cmp a; have hhu := W64.to_uint_cmp hi.
  have hbu := W64.to_uint_cmp bh.
  have hadd : W64.to_uint (a+(W64.one `<<<` 27)) = W64.to_uint a+134217728.
  + rewrite W64.to_uintD W64.to_uint_shl //= modz_small; smt().
  have har : W64.to_uint ((a+(W64.one `<<<` 27)) `>>>` 28) =
      (W64.to_uint a+134217728) %/ 268435456
    by rewrite W64.to_uint_shr //= hadd.
  have harb : 0 <= (W64.to_uint a+134217728) %/ 268435456 < 1048577
    by apply divz_cmp; smt().
  have hhir : W64.to_uint (hi `>>>` 28) = W64.to_uint hi %/ 268435456
    by rewrite W64.to_uint_shr.
  have hhirb : 0 <= W64.to_uint hi %/ 268435456 < 2097152
    by apply divz_cmp; smt().
  have hbs : W64.to_uint (bh `<<<` 20) = W64.to_uint bh*1048576.
  + rewrite W64.to_uint_shl //= modz_small; smt().
  have hm := modz_cmp (W64.to_uint hi) 268435456 _; first trivial.
  pose s0 := ((a+(W64.one `<<<` 27)) `>>>` 28)+
    ((hi `<<<` 20) `&` W64.of_int 281474976710655).
  pose s1 := (hi `>>>` 28)+(bh `<<<` 20).
  have hs0 : W64.to_uint s0 = (W64.to_uint a+134217728) %/ 268435456 +
      (W64.to_uint hi %% 268435456)*1048576.
  + rewrite /s0 W64.to_uintD har ss_shift20_mask_exact modz_small; smt().
  have hs1 : W64.to_uint s1 = W64.to_uint hi %/ 268435456 +
      W64.to_uint bh*1048576.
  + rewrite /s1 W64.to_uintD hhir hbs modz_small; smt().
  have hs0b : 0 <= W64.to_uint s0 <= 281474976710656 by smt().
  have hc : 0 <= W64.to_uint s0 %/ 281474976710656 < 2
    by apply divz_cmp; smt().
  have hn := hb_norm_value_exact (s0,s1) _; first rewrite /=; smt().
  rewrite -/s0 -/s1; split.
  + rewrite /hbs_canonical /hbs_radix.
    have [_ h] := hb_norm_low_bound (s0,s1); exact h.
  rewrite hn /hb_value /= hs0 hs1.
  have hd := divz_eq (W64.to_uint hi) 268435456; smt().
qed.

lemma hsa_mul_high_exact (x : hb_fp) (y : W64.t) :
  hbs_canonical x => W64.to_uint x.`2 <= 8388608 =>
  W64.to_uint y < 8796093022208 =>
  hbs_canonical (hb_mul_high x y) /\
  hb_value (hb_mul_high x y) =
    (hb_value x*W64.to_uint y+134217728) %/ 268435456.
proof.
  rewrite /hbs_canonical /hbs_radix => hx hh hy.
  have hx0 := W64.to_uint_cmp x.`1; have hx1 := W64.to_uint_cmp x.`2.
  have hy0 := W64.to_uint_cmp y.
  pose a := mul48_word x.`1 y; pose b := mul48_word x.`2 y.
  have hp0 : 0 <= W64.to_uint x.`1*W64.to_uint y <
      2475880078570760549798248448 by smt(IntOrder.mulr_ge0 IntOrder.ler_pmul).
  have hp1 : 0 <= W64.to_uint x.`2*W64.to_uint y <
      73786976294838206464 by smt(IntOrder.mulr_ge0 IntOrder.ler_pmul).
  have hqa : 0 <= (W64.to_uint x.`1*W64.to_uint y) %/ 281474976710656 <
      8796093022208 by apply divz_cmp; smt().
  have hqb : 0 <= (W64.to_uint x.`2*W64.to_uint y) %/ 281474976710656 <
      262144 by apply divz_cmp; smt().
  have hra := modz_cmp (W64.to_uint x.`1*W64.to_uint y) 281474976710656 _;
    first trivial.
  have hrb := modz_cmp (W64.to_uint x.`2*W64.to_uint y) 281474976710656 _;
    first trivial.
  have ha0 : W64.to_uint a.`1 =
      (W64.to_uint x.`1*W64.to_uint y) %% 281474976710656.
  + rewrite /a hwe_mul48_word /= W64.of_uintK modz_small; smt().
  have ha1 : W64.to_uint a.`2 =
      (W64.to_uint x.`1*W64.to_uint y) %/ 281474976710656.
  + rewrite /a hwe_mul48_word /= W64.of_uintK modz_small; smt().
  have hb0 : W64.to_uint b.`1 =
      (W64.to_uint x.`2*W64.to_uint y) %% 281474976710656.
  + rewrite /b hwe_mul48_word /= W64.of_uintK modz_small; smt().
  have hb1 : W64.to_uint b.`2 =
      (W64.to_uint x.`2*W64.to_uint y) %/ 281474976710656.
  + rewrite /b hwe_mul48_word /= W64.of_uintK modz_small; smt().
  have hhi : W64.to_uint (a.`2+b.`1) = W64.to_uint a.`2+W64.to_uint b.`1.
  + rewrite W64.to_uintD modz_small; smt().
  have [hcan hv] := hsa_high_join a.`1 (a.`2+b.`1) b.`2 _ _ _;
    first 3 smt().
  rewrite /hb_mul_high -/a -/b; split; first exact hcan.
  rewrite hv ha0 hhi ha1 hb0 hb1.
  have hda := divz_eq (W64.to_uint x.`1*W64.to_uint y) 281474976710656.
  have hdb := divz_eq (W64.to_uint x.`2*W64.to_uint y) 281474976710656.
  have he : hb_value x*W64.to_uint y+134217728 =
    (1048576*((W64.to_uint x.`1*W64.to_uint y) %/ 281474976710656+
      (W64.to_uint x.`2*W64.to_uint y) %% 281474976710656)+
      295147905179352825856*((W64.to_uint x.`2*W64.to_uint y) %/ 281474976710656))*
        268435456 + ((W64.to_uint x.`1*W64.to_uint y) %% 281474976710656+134217728).
  + rewrite /hb_value; smt().
  rewrite he divzMDl 1://; ring.
qed.

lemma hsa_mul_high_floor (x : hb_fp) (y : W64.t) :
  hbs_canonical x => W64.to_uint x.`2 <= 8388608 =>
  W64.to_uint y < 8796093022208 =>
  (hb_value x*W64.to_uint y) %/ 268435456 <= hb_value (hb_mul_high x y) <=
    (hb_value x*W64.to_uint y) %/ 268435456+1.
proof.
  move=> hx hh hy.
  have [_ hv] := hsa_mul_high_exact x y hx hh hy; rewrite hv.
  have hd := divz_eq (hb_value x*W64.to_uint y) 268435456.
  have hr := modz_cmp (hb_value x*W64.to_uint y) 268435456 _; first trivial.
  have he : hb_value x*W64.to_uint y+134217728 =
    ((hb_value x*W64.to_uint y) %/ 268435456)*268435456 +
    ((hb_value x*W64.to_uint y) %% 268435456+134217728) by smt().
  rewrite he divzMDl 1://.
  have hb : 0 <= ((hb_value x*W64.to_uint y) %% 268435456+134217728) %/ 268435456 < 2
    by apply divz_cmp; smt().
  smt().
qed.

lemma hsa_mul_high_error (x : hb_fp) (y : W64.t) :
  hbs_canonical x => W64.to_uint x.`2 <= 8388608 =>
  W64.to_uint y < 8796093022208 =>
  `|268435456*hb_value (hb_mul_high x y)-hb_value x*W64.to_uint y| <= 268435456.
proof.
  move=> hx hh hy; have h := hsa_mul_high_floor x y hx hh hy.
  have hd := divz_eq (hb_value x*W64.to_uint y) 268435456.
  have hr := modz_cmp (hb_value x*W64.to_uint y) 268435456 _; first trivial.
  smt(IntOrder.ler_norml).
qed.

lemma hsa_mode_scale_bound (mode : int) (inv : hb_fp) :
  hbs_mode mode => hbs_canonical inv => hb_value inv <= hbs_inverse_cap mode =>
  hbs_canonical (hb_mul_high inv (hb_ref_scale mode)) /\
  hb_value (hb_mul_high inv (hb_ref_scale mode)) <= hbs_scale_cap.
proof.
  move=> hm hc hv.
  have hcert := hbs_mode_certificate mode hm.
  have hiu := W64.to_uint_cmp inv.`1.
  have [hy0 hymax] := W64.to_uint_cmp (hb_ref_scale mode).
  have hh : W64.to_uint inv.`2 <= 8388608.
  + move: hv; rewrite /hb_value; smt().
  have hy : W64.to_uint (hb_ref_scale mode) < 8796093022208 by smt().
  have [hc2 _] := hsa_mul_high_exact inv (hb_ref_scale mode) hc hh hy.
  have hf := hsa_mul_high_floor inv (hb_ref_scale mode) hc hh hy.
  have hp := IntOrder.ler_wpmul2r (W64.to_uint (hb_ref_scale mode)) hy0
    (hb_value inv) (hbs_inverse_cap mode) hv.
  have hd := leq_div2r 268435456 _ _ hp _; first trivial.
  split; first exact hc2.
  smt().
qed.

op hsa_sample_input (sample : W64.t) : hb_fp =
  ((sample `&` W64.of_int 4294967295) `<<<` 16,sample `>>>` 32).

lemma hsa_sample_pair (sample : W64.t) :
  hbs_canonical (hsa_sample_input sample) /\
  hb_value (hsa_sample_input sample) = W64.to_uint sample*65536 /\
  0 <= hb_value (hsa_sample_input sample) < 1208925819614629174706176.
proof.
  have hu := W64.to_uint_cmp sample.
  have hm := modz_cmp (W64.to_uint sample) 4294967296 _; first trivial.
  have hlo : W64.to_uint ((sample `&` W64.of_int 4294967295) `<<<` 16) =
      (W64.to_uint sample %% 4294967296)*65536.
  + have -> : 4294967295=2^32-1 by trivial.
    rewrite W64.to_uint_shl // W64.to_uint_and_mod //= modz_small; smt().
  have hhi : W64.to_uint (sample `>>>` 32) = W64.to_uint sample %/ 4294967296
    by rewrite W64.to_uint_shr.
  have hd := divz_eq (W64.to_uint sample) 4294967296.
  rewrite /hbs_canonical /hbs_radix /hsa_sample_input /hb_value /= hlo hhi.
  smt().
qed.

lemma hsa_sample_product_bound (sample : W64.t) (scale : hb_fp) :
  hbs_canonical scale => hb_value scale <= hbs_scale_cap =>
  hb_value (hb_mul (hsa_sample_input sample) scale) <= 618970019642690137449562113 /\
  W64.to_uint (hb_mul (hsa_sample_input sample) scale).`2 <= 2199023255552.
proof.
  move=> hc hs.
  have [hxcan [hxval hxbound]] := hsa_sample_pair sample.
  have hxop : hbs_operand (hsa_sample_input sample).
  + move: hxcan hxbound; rewrite /hbs_operand /hbs_canonical /hbs_radix /hbs_operand_cap;
      smt().
  have hsop : hbs_operand scale.
  + move: hc hs; rewrite /hbs_operand /hbs_canonical /hbs_radix
      /hbs_operand_cap /hbs_scale_cap; smt().
  have [_ hf] := hmb_mul_floor_bounds (hsa_sample_input sample) scale hxop hsop.
  have hs0 := hmb_value_nonnegative scale.
  have hp : hb_value (hsa_sample_input sample)*hb_value scale <=
      46768052394588893382517914646921056628989841375232.
  + move: hs; rewrite /hbs_scale_cap; smt(IntOrder.ler_pmul).
  have hd := leq_div2r 75557863725914323419136 _ _ hp _; first trivial.
  have hv : hb_value (hb_mul (hsa_sample_input sample) scale) <=
      618970019642690137449562113.
  + move: hf hd; rewrite /hbs_q /=; smt().
  split; first exact hv.
  have hl := W64.to_uint_cmp (hb_mul (hsa_sample_input sample) scale).`1.
  move: hv; rewrite /hb_value; smt().
qed.

lemma hsa_rnd13_bound (sample : W64.t) (scale : hb_fp) :
  hbs_canonical scale => hb_value scale <= hbs_scale_cap =>
  0 <= hb_rnd13_magnitude sample scale <= hbs_coefficient_cap.
proof.
  move=> hc hs; have [_ hh] := hsa_sample_product_bound sample scale hc hs.
  pose p := hb_mul (hsa_sample_input sample) scale.
  have hu := W64.to_uint_cmp p.`2.
  have ha : W64.to_uint (p.`2+W64.of_int 16384) = W64.to_uint p.`2+16384.
  + rewrite W64.to_uintD W64.of_uintK /= modz_small; smt().
  have hdiv : 0 <= (W64.to_uint p.`2+16384) %/ 32768 < 67108865
    by apply divz_cmp; smt().
  rewrite /hb_rnd13_magnitude /= -/hsa_sample_input -/p W64.to_uint_shr //= ha
    /hbs_coefficient_cap; smt().
qed.

lemma hsa_scaled_coeff_bound samples signs scale i :
  hbs_canonical (hb_load scale) => hb_value (hb_load scale) <= hbs_scale_cap =>
  -hbs_coefficient_cap <= W32.to_sint (hb_scaled_coeff samples signs scale i) <=
    hbs_coefficient_cap.
proof.
  move=> hc hs.
  have hm := hsa_rnd13_bound (BArray32768.get64 samples i) (hb_load scale) hc hs.
  have hfit : hb_rnd13_magnitude (BArray32768.get64 samples i) (hb_load scale) <= 2147483647
    by move: hm; rewrite /hbs_coefficient_cap; smt().
  rewrite (hb_scaled_coeff_signed_fit samples signs scale i hfit).
  case (BArray512.get8 signs (i %/ 8)).[i %% 8]; smt().
qed.

(* No sample, sign, or initial output-array restriction is used here. *)
lemma hsa_scale_result_safe before1 before2 samples signs scale l t bound :
  hb_scale_bounds l t => t <= 2816 =>
  hbs_canonical (hb_load scale) => hb_value (hb_load scale) <= hbs_scale_cap =>
  hyperball_coeff_bound (hb_scale_result before1 before2 samples signs scale l t).`1
    l hbs_coefficient_cap /\
  hyperball_coeff_bound (hb_scale_result before1 before2 samples signs scale l t).`2
    (t-l) hbs_coefficient_cap /\
  0 <= hb_scale_norm before1 before2 samples signs scale l t < W64.modulus /\
  (hb_scale_check_result before1 before2 samples signs scale l t bound).`3 =
    W64.of_int (b2i (hb_scale_norm before1 before2 samples signs scale l t <=
      W64.to_uint bound)).
proof.
  move=> hb ht hc hs.
  have [hl [hk [hframe1 hframe2]]] :=
    hb_scale_result_layout before1 before2 samples signs scale l t hb.
  have hbl : hyperball_coeff_bound
      (hb_scale_result before1 before2 samples signs scale l t).`1 l hbs_coefficient_cap.
  + rewrite /hyperball_coeff_bound => i hi.
    have hir : 0 <= i < 2048 by move: hb; rewrite /hb_scale_bounds; smt().
    rewrite (hl i hir) ifT 1:/#.
    exact (hsa_scaled_coeff_bound samples signs scale i hc hs).
  have hbk : hyperball_coeff_bound
      (hb_scale_result before1 before2 samples signs scale l t).`2 (t-l) hbs_coefficient_cap.
  + rewrite /hyperball_coeff_bound => i hi.
    have hir : 0 <= i < 2048 by move: hb; rewrite /hb_scale_bounds; smt().
    rewrite (hk i hir) ifT 1:/#.
    exact (hsa_scaled_coeff_bound samples signs scale (l+i) hc hs).
  have hna : 0 <= l by move: hb; rewrite /hb_scale_bounds; smt().
  have hnb : 0 <= t-l by move: hb; rewrite /hb_scale_bounds; smt().
  have hcount : l+(t-l)<=2816 by smt().
  have hn := hyperball_sqnorm_26bit_no_overflow
    (hb_scale_result before1 before2 samples signs scale l t).`1 l
    (hb_scale_result before1 before2 samples signs scale l t).`2 (t-l)
    hna hnb hcount hbl hbk.
  have hnorm : 0 <= hb_scale_norm before1 before2 samples signs scale l t < W64.modulus
    by rewrite /hb_scale_norm; exact hn.
  have [hn0 hnfit] := hnorm.
  have hacc := hb_scale_accept_integer before1 before2 samples signs scale l t bound hb hnfit.
  split; first exact hbl.
  split; first exact hbk.
  split; first exact hnorm.
  exact hacc.
qed.

lemma hsa_mode_scale_total mode (input : BArray16.t) :
  hbs_mode mode => hbs_canonical (hb_load input) =>
  hb_value (hb_load input) <= hbs_inverse_cap mode =>
  phoare [HB._fixpoint_mul_high : xp=input /\ y=hb_ref_scale mode ==>
    res=hb_pack (hb_mul_high (hb_load input) (hb_ref_scale mode)) /\
    hbs_canonical (hb_load res) /\ hb_value (hb_load res)<=hbs_scale_cap] = 1%r.
proof.
  move=> hm hc hv; have hs := hsa_mode_scale_bound mode (hb_load input) hm hc hv.
  conseq hb_mul_high_ll (hb_mul_high_correct input (hb_ref_scale mode)) => //.
  move=> &m hpre result; split; first smt().
  move=> [_ ->]; rewrite hb_load_pack; smt().
qed.

(* The integer-norm precondition of the old word contract is discharged
   by the scale bound, independently of all samples and sign bytes. *)
lemma hsa_scale_and_check_safe_total
    (before1 before2 : BArray8192.t) (samples : BArray32768.t)
    (signs : BArray512.t) (scale : BArray16.t) (l t : int) (bound0 : W64.t) :
  hb_scale_bounds l t => t <= 2816 =>
  hbs_canonical (hb_load scale) => hb_value (hb_load scale) <= hbs_scale_cap =>
  phoare [HS._sf_scale_and_check :
    y1p=before1 /\ y2p=before2 /\ samplesp=samples /\ signsp=signs /\
    scalep=scale /\ lcount=W64.of_int l /\ total=W64.of_int t /\ bound=bound0 ==>
    res.`1=(hb_scale_result before1 before2 samples signs scale l t).`1 /\
    res.`2=(hb_scale_result before1 before2 samples signs scale l t).`2 /\
    res.`3=W64.of_int (b2i (hb_scale_norm before1 before2 samples signs scale l t <=
      W64.to_uint bound0))] = 1%r.
proof.
  move=> hb ht hc hs.
  have [_ [_ [hn _]]] := hsa_scale_result_safe before1 before2 samples signs scale l t bound0
    hb ht hc hs.
  conseq (hb_scale_and_check_integer_total before1 before2 samples signs scale l t bound0) => //.
  smt().
qed.
