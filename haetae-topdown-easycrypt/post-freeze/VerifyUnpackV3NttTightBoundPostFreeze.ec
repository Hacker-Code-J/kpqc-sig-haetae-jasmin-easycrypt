require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import Array256 BArray1024 BArray8192 Fq GFq Rq.
require import Hpoly_loop VerifyUnpackMode2Target.
require import NTT_Fq RefJasminNTTLoop TargetNTTRefinement
               TargetKeygenM23WideNTT TargetKeygenM23WideSupport
               KeygenM23MatrixSpec VerifyUnpackV3NttPostFreeze
               KeygenM23SingularBoundary
               KeygenM23SingularIntegerSemantics.

theory VerifyUnpackV3NttTightBoundPostFreeze.

module Verify = VerifyUnpackMode2Target.M.
module Parent = TargetKeygenM23WideSupport.Parent.
module Wide = TargetKeygenM23WideNTT.WideSpec.
module Target = TargetNTTRefinement.Target.

import RefJasminNTT.

op verify_unpack_ntt_polys : int = 2.
op verify_unpack_ntt_words : int =
  verify_unpack_ntt_polys * KeygenM23MatrixSpec.poly_words_i.

op signed_bound32 (w : W32.t) (m : int) : bool =
  -m <= W32.to_sint w < m.

op signed_array256_bound_by
    (rp : BArray1024.t) (bd : int -> int) : bool =
  forall i, i \in range 0 256 =>
    signed_bound32 (BArray1024.get32 rp i) (bd i).

op poly_signed_bound131068 (rp : BArray1024.t) : bool =
  signed_array256_bound_by rp (const_bound 131068).

op verify_unpack_ntt_input_signed131068 (xp : BArray8192.t) : bool =
  forall i, 0 <= i < verify_unpack_ntt_words =>
    signed_bound32 (BArray8192.get32 xp i) 131068.

op verify_unpack_ntt_output_bound20 (xp : BArray8192.t) : bool =
  forall i, 0 <= i < verify_unpack_ntt_words =>
    Fq.bw32 (BArray8192.get32 xp i) 20.

op tight_stage_mag (len : int) : int =
  if len = 128 then 131068 else
  if len = 64 then 196604 else
  if len = 32 then 262140 else
  if len = 16 then 327676 else
  if len = 8 then 393212 else
  if len = 4 then 458748 else
  if len = 2 then 524284 else
  if len = 1 then 589820 else 655356.

op tight_middle_bound (m start i : int) : int =
  if 0 <= i < start then m + 65536 else m.

op tight_inner_bound (m len start j i : int) : int =
  if (0 <= i < start) \/ (start <= i < j) \/
     (start + len <= i < j + len)
  then m + 65536 else m.

lemma tight_fwd_len_ok_128 : fwd_len_ok 128.
proof. by rewrite /fwd_len_ok. qed.

lemma tight_fwd_zbase_128 : fwd_zbase 128 = 0.
proof. by rewrite /fwd_zbase. qed.

lemma tight_stage_mag_range len :
  fwd_len_ok len =>
  0 <= tight_stage_mag len <= 655356.
proof.
rewrite /fwd_len_ok /tight_stage_mag.
smt().
qed.

lemma tight_stage_mag_le_pow20 len :
  fwd_len_ok len =>
  tight_stage_mag len < 2^20.
proof.
move=> hlen.
have hrange := tight_stage_mag_range len hlen.
rewrite /tight_stage_mag /fwd_len_ok in hlen.
smt().
qed.

lemma tight_stage_mag_next len :
  fwd_len_ok len =>
  0 < len =>
  tight_stage_mag (len %/ 2) = tight_stage_mag len + 65536.
proof.
rewrite /fwd_len_ok /tight_stage_mag.
smt().
qed.

lemma tight_middle_start_const m i :
  tight_middle_bound m 0 i = m.
proof. by rewrite /tight_middle_bound; smt(). qed.

lemma tight_middle_to_inner m len start i :
  tight_middle_bound m start i =
  tight_inner_bound m len start start i.
proof. by rewrite /tight_middle_bound /tight_inner_bound; smt(). qed.

lemma tight_inner_current m len start j :
  0 < len =>
  start <= j < start + len =>
  tight_inner_bound m len start j j = m /\
  tight_inner_bound m len start j (j + len) = m /\
  tight_inner_bound m len start (j + 1) j = m + 65536 /\
  tight_inner_bound m len start (j + 1) (j + len) = m + 65536.
proof. by rewrite /tight_inner_bound; smt(). qed.

lemma tight_inner_weaken_unchanged m len start j k :
  0 <= m =>
  0 < len =>
  start <= j < start + len =>
  k \in range 0 256 =>
  k <> j =>
  k <> j + len =>
  0 <= tight_inner_bound m len start j k <=
       tight_inner_bound m len start (j + 1) k.
proof.
move=> hm hlen hjrange hk hkj hkjl.
have hbase :=
  fwd_inner_weaken_unchanged 0 len start j k
    _ hlen hjrange hk hkj hkjl.
+ smt().
rewrite /tight_inner_bound /fwd_inner_bound in hbase.
move: hbase.
smt().
qed.

lemma tight_inner_exit_to_middle m len start i :
  0 <= start =>
  0 < len =>
  tight_inner_bound m len start (start + len) i =
  tight_middle_bound m (start + 2 * len) i.
proof.
move=> hstart hlen.
have hbase := fwd_inner_exit_to_middle 0 len start i hstart hlen.
rewrite /tight_inner_bound /tight_middle_bound.
rewrite /fwd_inner_bound /fwd_middle_bound in hbase.
move: hbase.
smt().
qed.

lemma tight_middle_exit_const m start i :
  0 <= i < 256 =>
  256 <= start =>
  tight_middle_bound m start i = m + 65536.
proof.
move=> hi hstart.
rewrite /tight_middle_bound.
have hcur : 0 <= i < start by smt().
rewrite hcur.
by smt().
qed.

lemma signed_bound32_of_bw16 (w : W32.t) :
  Fq.bw32 w 16 =>
  signed_bound32 w 65536.
proof.
rewrite /Fq.bw32 /signed_bound32.
smt().
qed.

lemma signed_bound32_to_bw (w : W32.t) m sz :
  signed_bound32 w m =>
  0 <= m <= 2^sz =>
  Fq.bw32 w sz.
proof.
rewrite /signed_bound32 /Fq.bw32.
smt().
qed.

lemma signed_array256_const_to_barray20 rp m :
  signed_array256_bound_by rp (const_bound m) =>
  0 <= m <= 2^20 =>
  NTT_Fq.barray256_bound rp 20.
proof.
move=> hbd hm i hi.
apply
  (signed_bound32_to_bw
    (BArray1024.get32 rp i) m 20 (hbd i hi) hm).
qed.

lemma fqmul_product_bound_16_20 a b :
  Fq.bw32 a 16 =>
  Fq.bw32 b 20 =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <=
    W32.to_sint a * W32.to_sint b <
    Fq.SignedReductions.R %/ 2 * Fq.q.
proof.
rewrite /Fq.bw32 /Fq.SignedReductions.R /Fq.q /=.
smt().
qed.

lemma signed_array256_bound_by_set32
    rp bd i w :
  signed_array256_bound_by rp bd =>
  0 <= i < 256 =>
  signed_bound32 w (bd i) =>
  signed_array256_bound_by (BArray1024.set32 rp i w) bd.
proof.
move=> hbd hi hbw j hj.
have hget :
  BArray1024.get32 (BArray1024.set32 rp i w) j =
  if i = j then w else BArray1024.get32 rp j.
+ change (BArray1024.get32d (BArray1024.set32d rp (4 * i) w) (4 * j) =
          if i = j then w else BArray1024.get32d rp (4 * j)).
  by rewrite BArray1024.get_set32E 1:/# 1:/#.
rewrite hget.
case: (i = j) => hij.
+ by smt().
exact (hbd j hj).
qed.

lemma signed_array256_bound_by_set32_change
    rp bd bd' i w :
  signed_array256_bound_by rp bd =>
  0 <= i < 256 =>
  signed_bound32 w (bd' i) =>
  (forall k, k \in range 0 256 => k <> i =>
     0 <= bd k <= bd' k) =>
  signed_array256_bound_by (BArray1024.set32 rp i w) bd'.
proof.
move=> hbd hi hbw hle j hj.
have hget :
  BArray1024.get32 (BArray1024.set32 rp i w) j =
  if i = j then w else BArray1024.get32 rp j.
+ change (BArray1024.get32d (BArray1024.set32d rp (4 * i) w) (4 * j) =
          if i = j then w else BArray1024.get32d rp (4 * j)).
  by rewrite BArray1024.get_set32E 1:/# 1:/#.
rewrite hget.
case: (i = j) => hij.
+ by smt().
have hneq : j <> i by smt().
have := hbd j hj.
rewrite /signed_bound32.
move=> hcur.
have hlims := hle j hj hneq.
smt().
qed.

lemma forward_butterfly_signed_bounds s t m :
  0 <= m /\
  m + 65536 < 2147483648 =>
  signed_bound32 s m =>
  Fq.bw32 t 16 =>
  signed_bound32 (s + t) (m + 65536) /\
  signed_bound32 (s - t) (m + 65536).
proof.
move=> hm hs hbwt.
have ht := signed_bound32_of_bw16 t hbwt.
move: hs ht => [hslo hshi] [htlo hthi].
have hadd :
  W32.to_sint (s + t) = W32.to_sint s + W32.to_sint t.
+ rewrite W32.to_sintD_small 1:/#.
  smt().
have hsub :
  W32.to_sint (s - t) = W32.to_sint s - W32.to_sint t.
+ rewrite W32.to_sintB_small 1:/#.
  smt().
split.
+ rewrite /signed_bound32 hadd.
  smt().
rewrite /signed_bound32 hsub.
smt().
qed.

lemma forward_butterfly_signed_step_bound_by
    rp j len start s t m :
  signed_array256_bound_by rp
    (tight_inner_bound m len start j) =>
  0 <= start =>
  0 < len =>
  start <= j < start + len =>
  0 <= j < 256 =>
  0 <= j + len < 256 =>
  s = BArray1024.get32 rp j =>
  0 <= m /\
  m + 65536 < 2147483648 =>
  Fq.bw32 t 16 =>
  signed_array256_bound_by
    (BArray1024.set32 (BArray1024.set32 rp (j + len) (s - t)) j (s + t))
    (tight_inner_bound m len start (j + 1)).
proof.
  move=> hbd hstart hlen hjrange hj hjlen hs hm hbwt.
have [hcurj [hcurjl [hnextj hnextjl]]] :=
  tight_inner_current m len start j hlen hjrange.
have hbound_s : signed_bound32 s m.
+ rewrite hs -hcurj.
  have hjmem : j \in range 0 256 by rewrite mem_range; smt().
  exact (hbd j hjmem).
have [hsum hsub] :=
  forward_butterfly_signed_bounds s t m hm hbound_s hbwt.
have hbound1 :
  signed_array256_bound_by
    (BArray1024.set32 rp (j + len) (s - t))
    (tight_inner_bound m len start (j + 1)).
+ apply
    (signed_array256_bound_by_set32_change
      rp (tight_inner_bound m len start j)
      (tight_inner_bound m len start (j + 1))
      (j + len) (s - t)).
  + exact hbd.
  + by smt().
  + by rewrite hnextjl; exact hsub.
  move=> k hk hkneq.
  case: (k = j) => hkj.
  + rewrite hkj hcurj hnextj.
    smt().
  apply (tight_inner_weaken_unchanged m len start j k).
  + by smt().
  + exact hlen.
  + exact hjrange.
  + exact hk.
  + exact hkj.
  + exact hkneq.
apply
  (signed_array256_bound_by_set32
    (BArray1024.set32 rp (j + len) (s - t))
    (tight_inner_bound m len start (j + 1))
    j (s + t)).
+ exact hbound1.
+ by smt().
by rewrite hnextj; exact hsum.
qed.

lemma tight_twiddle_product_bound_from_inner
    rp len start j zc :
  signed_array256_bound_by rp
    (tight_inner_bound (tight_stage_mag len) len start j) =>
  fwd_len_ok len =>
  0 < len =>
  start <= j < start + len =>
  0 <= j + len < 256 =>
  1 <= zc < 256 =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <=
    W32.to_sint (BArray1024.get32 Hpoly_loop.jzetas zc) *
    W32.to_sint (BArray1024.get32 rp (j + len)) <
    Fq.SignedReductions.R %/ 2 * Fq.q.
proof.
move=> hbd hlenok hlen hjrange hjlen hzc.
have hzbw := jzetas_bound16 zc hzc.
have [_ [hcurjl _]] :=
  tight_inner_current (tight_stage_mag len) len start j hlen hjrange.
have hsigned :
  signed_bound32
    (BArray1024.get32 rp (j + len))
    (tight_stage_mag len).
+ have hjlmem : j + len \in range 0 256 by rewrite mem_range; smt().
  have := hbd (j + len) hjlmem.
  by rewrite hcurjl.
have hbw20 :
  Fq.bw32 (BArray1024.get32 rp (j + len)) 20.
+ apply
    (signed_bound32_to_bw
      (BArray1024.get32 rp (j + len))
      (tight_stage_mag len) 20 hsigned).
  have hmag := tight_stage_mag_le_pow20 len hlenok.
  smt().
exact
  (fqmul_product_bound_16_20
    (BArray1024.get32 Hpoly_loop.jzetas zc)
    (BArray1024.get32 rp (j + len)) hzbw hbw20).
qed.

lemma fqmul_bw16_call_h ai bi :
  hoare [Hpoly_loop.M.__fqmul :
    W32.to_sint a = ai /\ W32.to_sint b = bi /\
    - Fq.SignedReductions.R %/ 2 * Fq.q <= ai * bi <
      Fq.SignedReductions.R %/ 2 * Fq.q
    ==> Fq.bw32 res 16].
proof.
conseq (fqmul_word_to_coeff_mul_bound_h ai bi).
+ by smt().
qed.

lemma loop_poly_ntt_signed_bound20 :
  hoare [Hpoly_loop.M._poly_ntt :
    poly_signed_bound131068 rp
    ==>
    signed_array256_bound_by res (const_bound 655356) /\
    NTT_Fq.barray256_bound res 20].
proof.
proc.
wp.
while (
  signed_array256_bound_by rp (const_bound (tight_stage_mag len)) /\
  NTT_Fq.barray256_bound rp 20 /\
  zetasp = Hpoly_loop.jzetas /\
  fwd_len_ok len /\
  zetasctr = fwd_zbase len
).
+ wp.
  while (
    signed_array256_bound_by rp
      (tight_middle_bound (tight_stage_mag len) start) /\
    zetasp = Hpoly_loop.jzetas /\
    fwd_len_ok len /\
    0 < len /\
    0 <= start <= 256 /\
    start = 2 * len * (zetasctr - fwd_zbase len)
  ).
  + wp.
    while (
      signed_array256_bound_by rp
        (tight_inner_bound (tight_stage_mag len) len start j) /\
      zetasp = Hpoly_loop.jzetas /\
      fwd_len_ok len /\
      0 < len /\
      0 <= start < 256 /\
      start + 2 * len <= 256 /\
      start =
        2 * len *
        (zetasctr - 1 - fwd_zbase len) /\
      1 <= zetasctr < 256 /\
      zeta_0 = BArray1024.get32 Hpoly_loop.jzetas zetasctr /\
      cmp = start + len /\
      start <= j <= start + len
    ).
    + wp.
      sp.
      exlim zeta_0 => ai.
      exlim coeff => bi.
      call (fqmul_bw16_call_h
        (W32.to_sint ai) (W32.to_sint bi)).
      wp.
      skip.
      move=> &m /=.
      move=>
        [hbi [hai [hs [hoff [hcoeff [hinv hguards]]]]]].
      move: hinv => [hbd hinv].
      move: hinv => [hzetasp hinv].
      move: hinv => [hlenok hinv].
      move: hinv => [hlen hinv].
      move: hinv => [hstart_rng hinv].
      move: hinv => [hblock hinv].
      move: hinv => [hzctr hinv].
      move: hinv => [hzcrng hinv].
      move: hinv => [hzeta0 [hcmp hjrng]].
      move: hstart_rng => [hstart0 hstartlt].
      move: hjrng => [hj_ge hj_le].
      have hprod :=
        tight_twiddle_product_bound_from_inner
          rp{m} len{m} start{m} j{m} zetasctr{m}
          hbd hlenok hlen _ _ hzcrng.
      + by smt().
      + by smt().
      split.
      + rewrite hzeta0 hcoeff hoff.
        split; first by smt().
        split; first by smt().
        move: hprod.
        smt().
      move=> _ result hbwt.
      have hm :
        0 <= tight_stage_mag len{m} /\
        tight_stage_mag len{m} + 65536 < 2147483648.
      + have hmag := tight_stage_mag_range len{m} hlenok.
        smt().
      have hstep :=
        forward_butterfly_signed_step_bound_by
          rp{m} j{m} len{m} start{m} s{m} result
          (tight_stage_mag len{m})
          hbd hstart0 hlen _ _ _ hs hm hbwt.
      + by smt().
      + by smt().
      + by smt().
      split.
      + by smt().
      split.
      + by smt().
      split.
      + by smt().
      split.
      + by smt().
      split.
      + by smt().
      split.
      + by smt().
      split.
      + by smt().
      split.
      + by smt().
      split.
      + by smt().
      split.
      + by smt().
      split.
      + by smt().
      by smt().
    wp.
    skip.
    move=> &m /= [hm hstart_guard].
    move: hm => [hbd hm].
    move: hm => [hzetasp hm].
    move: hm => [hlenok hm].
    move: hm => [hlen [hstart_rng hzctr]].
    move: hstart_rng => [hstart_ge hstart_le].
    have hstart_lt : 0 <= start{m} < 256 by smt().
    have hblock :=
      fwd_block_end_bound len{m} start{m} zetasctr{m}
        hlenok hlen hstart_lt _.
    + exact hzctr.
    have hzcr :=
      fwd_read_range len{m} start{m} zetasctr{m}
        hlenok hlen hstart_lt hzctr.
    split.
    + split.
      + move=> i hi.
        rewrite -tight_middle_to_inner.
        exact (hbd i hi).
      split; first exact hzetasp.
      split; first exact hlenok.
      split; first exact hlen.
      split; first exact hstart_lt.
      split; first exact hblock.
      split; first exact hzctr.
      split; first by smt().
      split; first by rewrite hzetasp.
      by smt().
    move=> jL rpL hnotL hinv.
    move: hinv => [hbdL hinv].
    move: hinv => [hzetaspL hinv].
    move: hinv => [hlenL_ok hinv].
    move: hinv => [hlenL hinv].
    move: hinv => [hstartL_rng hinv].
    move: hinv => [hblockL hinv].
    move: hinv => [hzctrL hinv].
    move: hinv => [hzcrL hinv].
    move: hinv => [hzeta0L hinv].
    move: hinv => [hcmpL hjrngL].
    move: hstartL_rng => [hstartL_ge hstartL_lt].
    have hj_end : jL = start{m} + len{m} by smt().
    have hstart_new : jL + len{m} = start{m} + 2 * len{m} by smt().
    have hbdmid :
      signed_array256_bound_by rpL
        (tight_middle_bound (tight_stage_mag len{m}) (jL + len{m})).
    + move=> i hi.
      have htmp := hbdL i hi.
      have heq :=
        tight_inner_exit_to_middle
          (tight_stage_mag len{m}) len{m} start{m} i
          hstartL_ge hlenL.
      rewrite hstart_new.
      move: htmp.
      by rewrite hj_end heq.
    split; first exact hbdmid.
    by smt().
  wp.
  skip.
  move=> &m /= [hm hlen_pos].
  move: hm => [hbd [hbw20 [hzetasp [hlenok hzbase]]]].
  split.
  + split.
    + move=> i hi.
      rewrite tight_middle_start_const.
      exact (hbd i hi).
    split; first exact hzetasp.
    split; first exact hlenok.
    split; first exact hlen_pos.
    by smt().
  move=> rpL startL zcL hnotL hm.
  move: hm => [hbdL hm].
  move: hm => [hzetaspL hm].
  move: hm => [hlenL_ok hm].
  move: hm => [hlenL_pos [hstart_eqL hstart_rngL]].
  have hstart_end : startL = 256 by smt().
  have hshift : len{m} `|>>` 1 = len{m} %/ 2.
  + by apply int_shr1_div2; smt().
  have hlen_next :=
    fwd_len_next_ok len{m} hlenL_ok hlenL_pos.
  have hzbase_next :=
    fwd_stage_zbase_exit len{m} zcL
      hlenL_ok hlenL_pos _.
  + by smt().
  have hbdconst :
    signed_array256_bound_by rpL
      (const_bound (tight_stage_mag (len{m} `|>>` 1))).
  + move=> i hi.
    have htmp := hbdL i hi.
    move: htmp.
    rewrite hstart_end.
    rewrite (tight_middle_exit_const (tight_stage_mag len{m}) 256 i _ _).
    + by move: hi; rewrite mem_range.
    + trivial.
    rewrite /const_bound hshift.
    have hnext := tight_stage_mag_next len{m} hlenL_ok hlenL_pos.
    smt().
  have hbwconst : NTT_Fq.barray256_bound rpL 20.
  + apply
      (signed_array256_const_to_barray20
        rpL (tight_stage_mag (len{m} `|>>` 1)) hbdconst).
    rewrite hshift.
    have hmag := tight_stage_mag_range (len{m} %/ 2) hlen_next.
    smt().
  split; first exact hbdconst.
  split; first exact hbwconst.
  split; first exact hzetaspL.
  split; first by rewrite hshift; exact hlen_next.
  by rewrite hshift; exact hzbase_next.
wp.
skip.
move=> &m /= hpre.
have hbd :
  signed_array256_bound_by rp{m} (const_bound (tight_stage_mag 128)).
+ rewrite /poly_signed_bound131068 /const_bound /tight_stage_mag in hpre.
  exact hpre.
have hbw20 : NTT_Fq.barray256_bound rp{m} 20.
+ apply
    (signed_array256_const_to_barray20
      rp{m} (tight_stage_mag 128) hbd).
  rewrite /tight_stage_mag.
  smt().
split.
+ split.
  + exact hbd.
  split.
  + exact hbw20.
  split.
  + by [].
  by rewrite /fwd_len_ok /fwd_zbase.
by rewrite /tight_stage_mag; smt().
qed.

lemma target_poly_ntt_signed_bound20 :
  hoare [Target._poly_ntt :
    poly_signed_bound131068 rp
    ==>
    signed_array256_bound_by res (const_bound 655356) /\
    NTT_Fq.barray256_bound res 20].
proof.
have hloop := loop_poly_ntt_signed_bound20.
by conseq TargetNTTRefinement.poly_ntt_loop_equiv hloop => /#.
qed.

lemma wide_polyvec_ntt_verify_unpack_count2_tight_bound20
    (xp0 : BArray8192.t) :
  hoare [Wide._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_signed131068 xp0
    ==>
    verify_unpack_ntt_output_bound20 res /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
proc.
rcondt 3; first by auto.
rcondt 8; first by auto; call (_ : true); auto.
rcondf 13; first by
  auto; call (_ : true); auto; call (_ : true); auto.
wp.
call target_poly_ntt_signed_bound20.
wp.
call target_poly_ntt_signed_bound20.
wp.
skip.
move=> &hr [-> [hcount hin]].
have hbound0 :
    0 <= 0 /\
    0 + KeygenM23MatrixSpec.poly_words_i <=
      KeygenM23MatrixSpec.array_words_i by
  rewrite /KeygenM23MatrixSpec.poly_words_i
          /KeygenM23MatrixSpec.array_words_i
          /BArray8192.size /=.
have hbound1 :
    0 <= KeygenM23MatrixSpec.poly_words_i /\
    KeygenM23MatrixSpec.poly_words_i +
      KeygenM23MatrixSpec.poly_words_i <=
      KeygenM23MatrixSpec.array_words_i by
  rewrite /KeygenM23MatrixSpec.poly_words_i
          /KeygenM23MatrixSpec.array_words_i
          /BArray8192.size /=.
have hin0 :
    poly_signed_bound131068
      (TargetKeygenM23WideSupport.poly_slice xp0 0).
+ rewrite /poly_signed_bound131068 /signed_array256_bound_by.
  move=> i hi.
  have hi' :
      0 <= i < KeygenM23MatrixSpec.poly_words_i.
  + move: hi.
    by rewrite mem_range /KeygenM23MatrixSpec.poly_words_i.
  rewrite TargetKeygenM23WideSupport.poly_slice_get32
    1:hbound0 1:hi'.
  apply hin.
  move: hi.
  rewrite mem_range /verify_unpack_ntt_words
          /verify_unpack_ntt_polys
          /KeygenM23MatrixSpec.poly_words_i /=.
  smt().
have hin1 :
    poly_signed_bound131068
      (TargetKeygenM23WideSupport.poly_slice
        xp0 KeygenM23MatrixSpec.poly_words_i).
+ rewrite /poly_signed_bound131068 /signed_array256_bound_by.
  move=> i hi.
  have hi' :
      0 <= i < KeygenM23MatrixSpec.poly_words_i.
  + move: hi.
    by rewrite mem_range /KeygenM23MatrixSpec.poly_words_i.
  rewrite TargetKeygenM23WideSupport.poly_slice_get32
    1:hbound1 1:hi'.
  apply hin.
  move: hi.
  rewrite mem_range /verify_unpack_ntt_words
          /verify_unpack_ntt_polys
          /KeygenM23MatrixSpec.poly_words_i /=.
  smt().
split; first exact hin0.
move=> _ r0 hr0.
have hslice1 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
      KeygenM23MatrixSpec.poly_words_i =
    TargetKeygenM23WideSupport.poly_slice
      xp0 KeygenM23MatrixSpec.poly_words_i.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound0.
  + exact hbound1.
  + right.
    smt().
split.
+ rewrite hslice1.
  exact hin1.
move=> _ r1 hr1.
move: hr0 => [_ hbw0].
move: hr1 => [_ hbw1].
have htail0 :
    KeygenM23MatrixSpec.word_tail_frame
      xp0 xp0 verify_unpack_ntt_words by
  rewrite /KeygenM23MatrixSpec.word_tail_frame.
have htail1 :
    KeygenM23MatrixSpec.word_tail_frame
      xp0
      (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
      verify_unpack_ntt_words by
  apply
    (TargetKeygenM23WideSupport.word_tail_frame_put_before
      xp0 xp0 0 verify_unpack_ntt_words r0);
    [ rewrite /verify_unpack_ntt_words
              /verify_unpack_ntt_polys
              /KeygenM23MatrixSpec.poly_words_i /=
    | rewrite /verify_unpack_ntt_words
              /verify_unpack_ntt_polys
              /KeygenM23MatrixSpec.poly_words_i
              /KeygenM23MatrixSpec.array_words_i
              /BArray8192.size /=
    | exact htail0 ].
have htail2 :
    KeygenM23MatrixSpec.word_tail_frame
      xp0
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      verify_unpack_ntt_words by
  apply
    (TargetKeygenM23WideSupport.word_tail_frame_put_before
      xp0 (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
      KeygenM23MatrixSpec.poly_words_i verify_unpack_ntt_words r1);
    [ rewrite /verify_unpack_ntt_words
              /verify_unpack_ntt_polys
              /KeygenM23MatrixSpec.poly_words_i /=
    | rewrite /verify_unpack_ntt_words
              /verify_unpack_ntt_polys
              /KeygenM23MatrixSpec.poly_words_i
              /KeygenM23MatrixSpec.array_words_i
              /BArray8192.size /=
    | exact htail1 ].
split.
+ rewrite /verify_unpack_ntt_output_bound20.
  move=> i hi.
  case (i < KeygenM23MatrixSpec.poly_words_i) => hfirst.
  + rewrite TargetKeygenM23WideSupport.put_poly_slice_get32_out
      1:hbound1 1:/# 1:/#.
    have hi0 : 0 <= i < KeygenM23MatrixSpec.poly_words_i by smt().
    have hget :=
      TargetKeygenM23WideSupport.put_poly_slice_get32_in
        xp0 0 r0 i hbound0 hi0.
    rewrite hget.
    apply hbw0.
    rewrite mem_range /KeygenM23MatrixSpec.poly_words_i.
    smt().
  have hi512 : 0 <= i < 512.
  + move: hi.
    by rewrite /verify_unpack_ntt_words /verify_unpack_ntt_polys
               /KeygenM23MatrixSpec.poly_words_i /=.
  have hge256 : 256 <= i.
  + move: hfirst.
    rewrite /KeygenM23MatrixSpec.poly_words_i.
    smt().
  have hlocal :
      0 <= i - KeygenM23MatrixSpec.poly_words_i <
        KeygenM23MatrixSpec.poly_words_i.
  + rewrite /KeygenM23MatrixSpec.poly_words_i.
    smt().
  have hget :=
    TargetKeygenM23WideSupport.put_poly_slice_get32_in
      (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
      KeygenM23MatrixSpec.poly_words_i r1
      (i - KeygenM23MatrixSpec.poly_words_i)
      hbound1 hlocal.
  have hgeti :
      BArray8192.get32
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1) i =
      BArray1024.get32 r1
        (i - KeygenM23MatrixSpec.poly_words_i).
  + move: hget.
    rewrite /KeygenM23MatrixSpec.poly_words_i.
    smt().
  rewrite hgeti.
  apply hbw1.
  by rewrite mem_range.
+ move: htail2.
  by rewrite /verify_unpack_ntt_words
             /verify_unpack_ntt_polys
             /KeygenM23MatrixSpec.poly_words_i /=.
qed.

lemma parent_polyvec_ntt_verify_unpack_count2_tight_bound20
    (xp0 : BArray8192.t) :
  hoare [Parent._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_signed131068 xp0
    ==>
    verify_unpack_ntt_output_bound20 res /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
have hwide :=
  wide_polyvec_ntt_verify_unpack_count2_tight_bound20 xp0.
by conseq VerifyUnpackV3NttPostFreeze.parent_polyvec_ntt_equiv_wide_count2
  hwide => /#.
qed.

lemma verify_unpack_polyvec_ntt_count2_tight_bound20
    (xp0 : BArray8192.t) :
  hoare [Verify._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_signed131068 xp0
    ==>
    verify_unpack_ntt_output_bound20 res /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
by conseq VerifyUnpackV3NttPostFreeze.verify_unpack_polyvec_ntt_equiv_parent
  (parent_polyvec_ntt_verify_unpack_count2_tight_bound20 xp0) => /#.
qed.

end VerifyUnpackV3NttTightBoundPostFreeze.
