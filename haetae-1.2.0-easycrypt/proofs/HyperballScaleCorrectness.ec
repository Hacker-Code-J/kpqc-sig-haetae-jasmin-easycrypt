require import AllCore IntDiv List StdOrder.
from Jasmin require import JModel_x86.
require import ApiTarget BArray16 BArray512 BArray8192 BArray32768
               HyperballFixedPointSpec HyperballFixedPointCorrectness
               HyperballNormSpec HyperballNormCorrectness HyperballScaleSpec
               GaussianStreamCorrectness.
import SLH64.

theory HyperballScaleCorrectness.
module HS = ApiTarget.M(ApiTarget.Syscall).
import HyperballScaleSpec HyperballNormCorrectness GaussianStreamCorrectness.

lemma hb_byte_extract (b : W8.t) k : 0 <= k =>
  truncateu8 ((zeroextu32 b `>>>` k) `&` W32.one) = W8.of_int (b2i b.[k]).
proof.
  move=> hk; apply W8.to_uint_eq.
  rewrite W4u8.to_uint_truncateu8.
  have -> : W32.one = W32.of_int (2^1 - 1) by trivial.
  rewrite W32.to_uint_and_mod 1:// /= W32.to_uint_shr 1:hk
    W4u8.to_uint_zeroextu32 W8.b2i_get 1:hk.
  trivial.
qed.

lemma hb_shr0 (w : W32.t) : w `>>>` 0 = w.
proof. by apply W32.wordP => i hi; rewrite W32.shrwE hi /=. qed.

lemma hb_bit_at_0_correct (b : W8.t) :
  hoare [HS.__bit_at_u8 : x = zeroextu32 b /\ shift = W8.of_int 0 ==>
    res = W8.of_int (b2i b.[0])].
proof.
  proc; auto => />.
  rewrite !W8.to_uint_eq /(`>>`) ?W8.to_uint0 ?W8.to_uint1 ?W8.of_uintK /=.
  have h := hb_byte_extract b 0 _; first trivial.
  by move: h; rewrite W8.to_uint_eq W4u8.to_uint_truncateu8 /(`>>`) /= ?hb_shr0.
qed.

lemma hb_bit_at_1_correct (b : W8.t) :
  hoare [HS.__bit_at_u8 : x = zeroextu32 b /\ shift = W8.of_int 1 ==>
    res = W8.of_int (b2i b.[1])].
proof.
  proc; auto => />.
  rewrite !W8.to_uint_eq /(`>>`) ?W8.to_uint0 ?W8.to_uint1 ?W8.of_uintK /=.
  have h := hb_byte_extract b 1 _; first trivial.
  by move: h; rewrite W8.to_uint_eq W4u8.to_uint_truncateu8 /(`>>`) /= ?hb_shr0.
qed.

lemma hb_bit_at_2_correct (b : W8.t) :
  hoare [HS.__bit_at_u8 : x = zeroextu32 b /\ shift = W8.of_int 2 ==>
    res = W8.of_int (b2i b.[2])].
proof.
  proc; auto => />.
  rewrite !W8.to_uint_eq /(`>>`) ?W8.to_uint0 ?W8.to_uint1 ?W8.of_uintK /=.
  have h := hb_byte_extract b 2 _; first trivial.
  by move: h; rewrite W8.to_uint_eq W4u8.to_uint_truncateu8 /(`>>`) /= ?hb_shr0.
qed.

lemma hb_bit_at_3_correct (b : W8.t) :
  hoare [HS.__bit_at_u8 : x = zeroextu32 b /\ shift = W8.of_int 3 ==>
    res = W8.of_int (b2i b.[3])].
proof.
  proc; auto => />.
  rewrite !W8.to_uint_eq /(`>>`) ?W8.to_uint0 ?W8.to_uint1 ?W8.of_uintK /=.
  have h := hb_byte_extract b 3 _; first trivial.
  by move: h; rewrite W8.to_uint_eq W4u8.to_uint_truncateu8 /(`>>`) /= ?hb_shr0.
qed.

lemma hb_bit_at_4_correct (b : W8.t) :
  hoare [HS.__bit_at_u8 : x = zeroextu32 b /\ shift = W8.of_int 4 ==>
    res = W8.of_int (b2i b.[4])].
proof.
  proc; auto => />.
  rewrite !W8.to_uint_eq /(`>>`) ?W8.to_uint0 ?W8.to_uint1 ?W8.of_uintK /=.
  have h := hb_byte_extract b 4 _; first trivial.
  by move: h; rewrite W8.to_uint_eq W4u8.to_uint_truncateu8 /(`>>`) /= ?hb_shr0.
qed.

lemma hb_bit_at_5_correct (b : W8.t) :
  hoare [HS.__bit_at_u8 : x = zeroextu32 b /\ shift = W8.of_int 5 ==>
    res = W8.of_int (b2i b.[5])].
proof.
  proc; auto => />.
  rewrite !W8.to_uint_eq /(`>>`) ?W8.to_uint0 ?W8.to_uint1 ?W8.of_uintK /=.
  have h := hb_byte_extract b 5 _; first trivial.
  by move: h; rewrite W8.to_uint_eq W4u8.to_uint_truncateu8 /(`>>`) /= ?hb_shr0.
qed.

lemma hb_bit_at_6_correct (b : W8.t) :
  hoare [HS.__bit_at_u8 : x = zeroextu32 b /\ shift = W8.of_int 6 ==>
    res = W8.of_int (b2i b.[6])].
proof.
  proc; auto => />.
  rewrite !W8.to_uint_eq /(`>>`) ?W8.to_uint0 ?W8.to_uint1 ?W8.of_uintK /=.
  have h := hb_byte_extract b 6 _; first trivial.
  by move: h; rewrite W8.to_uint_eq W4u8.to_uint_truncateu8 /(`>>`) /= ?hb_shr0.
qed.

lemma hb_bit_at_7_correct (b : W8.t) :
  hoare [HS.__bit_at_u8 : x = zeroextu32 b /\ shift = W8.of_int 7 ==>
    res = W8.of_int (b2i b.[7])].
proof.
  proc; auto => />.
  rewrite !W8.to_uint_eq /(`>>`) ?W8.to_uint0 ?W8.to_uint1 ?W8.of_uintK /=.
  have h := hb_byte_extract b 7 _; first trivial.
  by move: h; rewrite W8.to_uint_eq W4u8.to_uint_truncateu8 /(`>>`) /= ?hb_shr0.
qed.

lemma hb_bit_at_correct (b : W8.t) (k : int) : 0 <= k < 8 =>
  hoare [HS.__bit_at_u8 : x = zeroextu32 b /\ shift = W8.of_int k ==>
    res = W8.of_int (b2i b.[k])].
proof.
  move=> hk.
  case (k = 0) => hk0; first by subst k; apply hb_bit_at_0_correct.
  case (k = 1) => hk1; first by subst k; apply hb_bit_at_1_correct.
  case (k = 2) => hk2; first by subst k; apply hb_bit_at_2_correct.
  case (k = 3) => hk3; first by subst k; apply hb_bit_at_3_correct.
  case (k = 4) => hk4; first by subst k; apply hb_bit_at_4_correct.
  case (k = 5) => hk5; first by subst k; apply hb_bit_at_5_correct.
  case (k = 6) => hk6; first by subst k; apply hb_bit_at_6_correct.
  have -> : k = 7 by smt().
  apply hb_bit_at_7_correct.
qed.

lemma hb_bit_at_ll : islossless HS.__bit_at_u8.
proof. proc; islossless. qed.

lemma hb_low3_shift (i : W64.t) :
  truncateu8 i `&` W8.of_int 7 = W8.of_int (W64.to_uint i %% 8).
proof.
  have -> : W8.of_int 7 = W8.of_int (2^3 - 1) by trivial.
  by rewrite W8.and_mod 1:// W8u8.to_uint_truncateu8 /= modz_dvd 1:/#.
qed.

lemma hb_sign_at_correct (signs0 : BArray512.t) (i0 : W64.t) :
  hoare [HS.__bit_at_u8 :
    x = zeroextu32 (BArray512.get8 signs0 (W64.to_uint i0 %/ 8)) /\
    shift = truncateu8 i0 `&` W8.of_int 7 ==>
    res = hb_sign_bit signs0 (W64.to_uint i0)].
proof.
  have hk : 0 <= W64.to_uint i0 %% 8 < 8 by smt(modz_cmp).
  conseq (hb_bit_at_correct (BArray512.get8 signs0 (W64.to_uint i0 %/ 8))
    (W64.to_uint i0 %% 8) hk) => />.
  by rewrite hb_low3_shift.
qed.

lemma hb_scale_counter_next (i : W64.t) : W64.to_uint i < 4096 =>
  W64.to_uint (i + W64.one) = W64.to_uint i + 1.
proof.
  move=> hi; have /= hr := W64.to_uint_cmp i.
  by rewrite W64.to_uintD_small 1:/# W64.to_uint1.
qed.

lemma hb_scale_samples_correct
    (before1 before2 : BArray8192.t) (samples0 : BArray32768.t)
    (signs0 : BArray512.t) (scale0 : BArray16.t) (l t : int) :
  hoare [HS._polyfixveclk_scale_samples :
    y1p = before1 /\ y2p = before2 /\ samplesp = samples0 /\
    signsp = signs0 /\ scalep = scale0 /\
    counts = W64.of_int (t * 4294967296 + l) /\ hb_scale_bounds l t ==>
    res = hb_scale_result before1 before2 samples0 signs0 scale0 l t].
proof.
  proc.
  while (samplesp = samples0 /\ signsp = signs0 /\ scalep = scale0 /\
    total = W64.of_int t /\ hb_scale_bounds l t /\
    W64.to_uint i = l + W64.to_uint j /\ 0 <= W64.to_uint j <= t-l /\
    y1p = hb_scaled_output before1 (hb_scaled_coeff samples0 signs0 scale0) 0 l /\
    y2p = hb_scaled_output before2 (hb_scaled_coeff samples0 signs0 scale0) l (W64.to_uint j)).
  + wp; ecall (hb_mul_rnd13_correct sample scalep sign8).
    wp; ecall (hb_sign_at_correct signs0 i).
    auto => /> &hr hl0 hlmax hk0 hkmax ht hij hj0 hjt hguard.
    rewrite /protect_64 /protect_ptr.
    rewrite W64.ultE W64.to_uint_small 1:/# in hguard.
    rewrite W64.shr_div W8.of_uintK /=.
    rewrite !hb_scale_counter_next 1..2:/#.
    have hstep := hb_scaled_output_step before2 (hb_scaled_coeff samples0 signs0 scale0)
      l (W64.to_uint j{hr}) _; first smt().
    have hv : hb_scale_sample (BArray32768.get64 samples0 (W64.to_uint i{hr}))
      scale0 (hb_sign_bit signs0 (W64.to_uint i{hr})) =
      hb_scaled_coeff samples0 signs0 scale0 (l + W64.to_uint j{hr}) by
      rewrite /hb_scaled_coeff -hij.
    rewrite hv.
    smt().
  wp.
  while (samplesp = samples0 /\ signsp = signs0 /\ scalep = scale0 /\
    lcount = W64.of_int l /\ total = W64.of_int t /\ hb_scale_bounds l t /\
    0 <= W64.to_uint i <= l /\
    y1p = hb_scaled_output before1 (hb_scaled_coeff samples0 signs0 scale0) 0 (W64.to_uint i) /\
    y2p = before2).
  + wp; ecall (hb_mul_rnd13_correct sample scalep sign8).
    wp; ecall (hb_sign_at_correct signs0 i).
    auto => /> &hr hl0 hlmax hk0 hkmax ht hi0 hil hguard.
    rewrite /protect_64 /protect_ptr.
    rewrite W64.ultE W64.to_uint_small 1:/# in hguard.
    rewrite W64.shr_div W8.of_uintK /= hb_scale_counter_next 1:/#.
    have hstep := hb_scaled_output_step before1 (hb_scaled_coeff samples0 signs0 scale0)
      0 (W64.to_uint i{hr}) _; first smt().
    rewrite /= in hstep.
    have hv : hb_scale_sample (BArray32768.get64 samples0 (W64.to_uint i{hr}))
      scale0 (hb_sign_bit signs0 (W64.to_uint i{hr})) =
      hb_scaled_coeff samples0 signs0 scale0 (W64.to_uint i{hr}) by
      rewrite /hb_scaled_coeff.
    rewrite hv.
    smt().
  auto => /> hl0 hlmax hk0 hkmax ht.
  have hd : hb_scale_bounds l t by rewrite /hb_scale_bounds; smt().
  rewrite /protect_ptr /protect_64 /(`>>`) W8.of_uintK /=.
  rewrite (hb_counts_low l t hd) (hb_counts_high l t hd) !hb_scaled_output0.
  split; first smt().
  move=> i hdone hi0 hil.
  have hi : W64.to_uint i = l by
    move: hdone; rewrite W64.ultE W64.to_uint_small 1:/#; smt().
  rewrite hi.
  split; first smt().
  move=> i0 j0 hdone0 hij hj0 hjt.
  have hj : W64.to_uint j0 = t-l by
    move: hdone0; rewrite W64.ultE W64.to_uint_small 1:/#; smt().
  by rewrite /hb_scale_result hj.
qed.

lemma hb_scale_samples_ll : islossless HS._polyfixveclk_scale_samples.
proof.
  proc.
  while (true) (W64.to_uint total - W64.to_uint i).
  + move=> z; wp; call hb_mul_rnd13_ll.
    wp; call hb_bit_at_ll.
    auto => /> &hr hguard.
    rewrite /protect_64 /protect_ptr.
    have /= ht := W64.to_uint_cmp total{hr}.
    rewrite W64.ultE in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
  wp.
  while (true) (W64.to_uint lcount - W64.to_uint i).
  + move=> z; wp; call hb_mul_rnd13_ll.
    wp; call hb_bit_at_ll.
    auto => /> &hr hguard.
    rewrite /protect_64 /protect_ptr.
    have /= hl := W64.to_uint_cmp lcount{hr}.
    rewrite W64.ultE in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
  auto => />; smt(W64.ultE W64.to_uint_cmp).
qed.

lemma hb_scale_samples_total
    (before1 before2 : BArray8192.t) (samples0 : BArray32768.t)
    (signs0 : BArray512.t) (scale0 : BArray16.t) (l t : int) :
  phoare [HS._polyfixveclk_scale_samples :
    y1p = before1 /\ y2p = before2 /\ samplesp = samples0 /\
    signsp = signs0 /\ scalep = scale0 /\
    counts = W64.of_int (t * 4294967296 + l) /\ hb_scale_bounds l t ==>
    res = hb_scale_result before1 before2 samples0 signs0 scale0 l t] = 1%r.
proof.
  by conseq hb_scale_samples_ll
    (hb_scale_samples_correct before1 before2 samples0 signs0 scale0 l t).
qed.

lemma hb_scale_and_check_correct
    (before1 before2 : BArray8192.t) (samples0 : BArray32768.t)
    (signs0 : BArray512.t) (scale0 : BArray16.t) (l t : int) (bound0 : W64.t) :
  hoare [HS._sf_scale_and_check :
    y1p = before1 /\ y2p = before2 /\ samplesp = samples0 /\
    signsp = signs0 /\ scalep = scale0 /\ lcount = W64.of_int l /\
    total = W64.of_int t /\ bound = bound0 /\ hb_scale_bounds l t ==>
    res = hb_scale_check_result before1 before2 samples0 signs0 scale0 l t bound0].
proof.
  proc; wp.
  ecall (polyfixveclk_sqnorm2_correct y1p l y2p (t-l)).
  wp; call (hb_scale_samples_correct before1 before2 samples0 signs0 scale0 l t).
  auto => /> hl0 hlmax hk0 hkmax ht.
  rewrite /protect_64 /protect_ptr /(`<<`) W8.of_uintK /=.
  rewrite gs_pack_counts_word 1:/#.
  try rewrite -W64.of_intS.
  rewrite /hb_scale_check_result /hb_scale_norm /=.
  rewrite W64.uleE W64.of_uintK.
  smt().
qed.

lemma hb_scale_and_check_ll : islossless HS._sf_scale_and_check.
proof.
  proc; wp; call polyfixveclk_sqnorm2_ll.
  wp; call hb_scale_samples_ll.
  auto => />; smt().
qed.

lemma hb_scale_and_check_total
    (before1 before2 : BArray8192.t) (samples0 : BArray32768.t)
    (signs0 : BArray512.t) (scale0 : BArray16.t) (l t : int) (bound0 : W64.t) :
  phoare [HS._sf_scale_and_check :
    y1p = before1 /\ y2p = before2 /\ samplesp = samples0 /\
    signsp = signs0 /\ scalep = scale0 /\ lcount = W64.of_int l /\
    total = W64.of_int t /\ bound = bound0 /\ hb_scale_bounds l t ==>
    res = hb_scale_check_result before1 before2 samples0 signs0 scale0 l t bound0] = 1%r.
proof.
  by conseq hb_scale_and_check_ll
    (hb_scale_and_check_correct before1 before2 samples0 signs0 scale0 l t bound0).
qed.

lemma hb_scale_and_check_integer_total
    (before1 before2 : BArray8192.t) (samples0 : BArray32768.t)
    (signs0 : BArray512.t) (scale0 : BArray16.t) (l t : int) (bound0 : W64.t) :
  phoare [HS._sf_scale_and_check :
    y1p = before1 /\ y2p = before2 /\ samplesp = samples0 /\
    signsp = signs0 /\ scalep = scale0 /\ lcount = W64.of_int l /\
    total = W64.of_int t /\ bound = bound0 /\ hb_scale_bounds l t /\
    hb_scale_norm before1 before2 samples0 signs0 scale0 l t < W64.modulus ==>
    res.`1 = (hb_scale_result before1 before2 samples0 signs0 scale0 l t).`1 /\
    res.`2 = (hb_scale_result before1 before2 samples0 signs0 scale0 l t).`2 /\
    res.`3 = W64.of_int (b2i (hb_scale_norm before1 before2 samples0 signs0 scale0 l t
      <= W64.to_uint bound0))] = 1%r.
proof.
  conseq (hb_scale_and_check_total before1 before2 samples0 signs0 scale0 l t bound0) => />.
  move=> &hr hl ht hl0 hlmax hk0 hkmax htmax hfit result.
  have hd : hb_scale_bounds l t by rewrite /hb_scale_bounds; smt().
  have hacc := hb_scale_accept_integer y1p{hr} y2p{hr} samplesp{hr}
    signsp{hr} scalep{hr} l t bound{hr} hd hfit.
  split; last exact hacc.
  rewrite /hb_scale_check_result /= in hacc.
  rewrite /hb_scale_check_result /=.
  smt().
qed.

lemma hb_sign_extend signs i :
  zeroextu64 (hb_sign_bit signs i) =
    W64.of_int (b2i (BArray512.get8 signs (i %/ 8)).[i %% 8]).
proof.
  apply W64.to_uint_eq.
  rewrite /hb_sign_bit W8u8.to_uint_zeroextu64 !W8.of_uintK W64.of_uintK /b2i.
  by case (BArray512.get8 signs (i %/ 8)).[i %% 8] => /=.
qed.

lemma hb_scaled_coeff_signed_fit samples signs scale i :
  hb_rnd13_magnitude (BArray32768.get64 samples i) (hb_load scale) <= 2147483647 =>
  W32.to_sint (hb_scaled_coeff samples signs scale i) =
    if (BArray512.get8 signs (i %/ 8)).[i %% 8]
    then -hb_rnd13_magnitude (BArray32768.get64 samples i) (hb_load scale)
    else hb_rnd13_magnitude (BArray32768.get64 samples i) (hb_load scale).
proof.
  move=> hf.
  rewrite /hb_scaled_coeff /hb_scale_sample hb_sign_extend /b2i.
  case (BArray512.get8 signs (i %/ 8)).[i %% 8] => hs /=.
  + have h := hb_mul_rnd13_signed_fit (BArray32768.get64 samples i) (hb_load scale)
      W64.one _ hf; first by right.
    by move: h; rewrite W64.to_uint_eq W64.to_uint1 W64.to_uint0 /=.
  have h := hb_mul_rnd13_signed_fit (BArray32768.get64 samples i) (hb_load scale)
    W64.zero _ hf; first by left.
  by move: h; rewrite /=.
qed.

end HyperballScaleCorrectness.
