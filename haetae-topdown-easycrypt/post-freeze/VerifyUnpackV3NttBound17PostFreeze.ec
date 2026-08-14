require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8192 Array256 Fq GFq Rq.
require import Hpoly_loop VerifyUnpackMode2Target.
require import NTT_Fq NTTFullSpec NTTFullAlgebra NTTRowProductSpec.
require import RefJasminNTTLoop TargetNTTRefinement
               TargetKeygenM23WideNTT TargetKeygenM23WideSupport
               KeygenM23ArithmeticSpec KeygenM23MatrixSpec
               VerifyUnpackV3NttPostFreeze.

theory VerifyUnpackV3NttBound17PostFreeze.

module Verify = VerifyUnpackMode2Target.M.
module Parent = TargetKeygenM23WideSupport.Parent.
module Wide = TargetKeygenM23WideNTT.WideSpec.
module Target = TargetNTTRefinement.Target.

import TargetKeygenM23WideSupport.
import RefJasminNTT.

op verify_unpack_ntt_polys : int = 2.
op verify_unpack_ntt_words : int =
  verify_unpack_ntt_polys * KeygenM23MatrixSpec.poly_words_i.

op verify_unpack_ntt_input_repr_bound17
    (s : BArray8192.t) (p0 p1 : Rq.poly) : bool =
  KeygenM23ArithmeticSpec.wide_slice_repr_bound s 0 p0 17 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s KeygenM23MatrixSpec.poly_words_i p1 17.

op verify_unpack_ntt_repr_bound25
    (s : BArray8192.t) (p0 p1 : Rq.poly) : bool =
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s 0 (NTTFullSpec.full_ntt p0) 25 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s KeygenM23MatrixSpec.poly_words_i
    (NTTFullSpec.full_ntt p1) 25.

op fwd_stage_bound17 (len : int) : int =
  RefJasminNTT.fwd_stage_bound len + 1.

lemma fwd_stage_bound17_range len :
  RefJasminNTT.fwd_len_ok len =>
  0 <= fwd_stage_bound17 len <= 25.
proof.
move=> hlen.
have hrange := RefJasminNTT.fwd_stage_bound_range len hlen.
rewrite /fwd_stage_bound17.
smt().
qed.

lemma fwd_stage_bound17_ge16 len :
  RefJasminNTT.fwd_len_ok len =>
  16 <= fwd_stage_bound17 len.
proof.
move=> hlen.
have hrange := fwd_stage_bound17_range len hlen.
smt().
qed.

lemma fwd_stage_bound17_lt31 len :
  RefJasminNTT.fwd_len_ok len =>
  fwd_stage_bound17 len < 31.
proof.
move=> hlen.
have hrange := fwd_stage_bound17_range len hlen.
smt().
qed.

lemma fqmul_product_bound_16_25 a b :
  Fq.bw32 a 16 =>
  Fq.bw32 b 25 =>
  - Fq.SignedReductions.R %/ 2 * Fq.q <=
    W32.to_sint a * W32.to_sint b <
    Fq.SignedReductions.R %/ 2 * Fq.q.
proof.
rewrite /Fq.bw32 /Fq.SignedReductions.R /Fq.q /=.
smt().
qed.

lemma fwd_stage_bound17_next len :
  RefJasminNTT.fwd_len_ok len =>
  0 < len =>
  fwd_stage_bound17 (len %/ 2) = fwd_stage_bound17 len + 1.
proof.
move=> hlen hpos.
rewrite /fwd_stage_bound17.
have hnext := RefJasminNTT.fwd_stage_next len hlen hpos.
smt().
qed.

lemma forward_twiddle_product_bound_from_inner17
  rp len start j zc :
  barray256_bound_by rp
    (fwd_inner_bound (fwd_stage_bound17 len) len start j) =>
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
  fwd_inner_current (fwd_stage_bound17 len) len start j _ hlen hjrange.
+ have hrange := fwd_stage_bound17_range len hlenok.
  smt().
have hraw :
  Fq.bw32 (BArray1024.get32 rp (j + len)) (fwd_stage_bound17 len).
+ have hjlmem : j + len \in range 0 256 by rewrite mem_range; smt().
  have := hbd (j + len) hjlmem.
  by rewrite hcurjl.
have hstage := fwd_stage_bound17_range len hlenok.
have hbw25 :
  Fq.bw32 (BArray1024.get32 rp (j + len)) 25.
+ exact (NTT_Fq.bw32_weaken (BArray1024.get32 rp (j + len))
           (fwd_stage_bound17 len) 25 hstage hraw).
exact (fqmul_product_bound_16_25
  (BArray1024.get32 Hpoly_loop.jzetas zc)
  (BArray1024.get32 rp (j + len)) hzbw hbw25).
qed.

equiv poly_ntt_core_ref17 :
  Hpoly_loop.M._poly_ntt ~ NTT_Fq.NTT.ntt :
  NTT_Fq.poly_repr_bound rp{1} r{2} 17 /\
  zetas{2} = NTT_Fq.zetas
  ==> NTT_Fq.poly_repr_bound res{1} res{2} 25.
proof.
proc.
wp.
while (
  NTT_Fq.poly_repr rp{1} r{2} /\
  barray256_bound_by rp{1}
    (const_bound (fwd_stage_bound17 len{1})) /\
  zetasp{1} = Hpoly_loop.jzetas /\
  zetas{2} = NTT_Fq.zetas /\
  zetasctr{1} = zetasctr{2} /\
  len{1} = len{2} /\
  fwd_len_ok len{1} /\
  zetasctr{1} = fwd_zbase len{1}
).
+ wp.
  while (
    NTT_Fq.poly_repr rp{1} r{2} /\
    barray256_bound_by rp{1}
      (fwd_middle_bound
        (fwd_stage_bound17 len{1}) start{1}) /\
    zetasp{1} = Hpoly_loop.jzetas /\
    zetas{2} = NTT_Fq.zetas /\
    zetasctr{1} = zetasctr{2} /\
    len{1} = len{2} /\
    fwd_len_ok len{1} /\
    0 < len{1} /\
    start{1} = start{2} /\
    0 <= start{1} <= 256 /\
    start{1} =
      2 * len{1} *
        (zetasctr{1} - fwd_zbase len{1})
  ).
  + wp.
    while (
      NTT_Fq.poly_repr rp{1} r{2} /\
      barray256_bound_by rp{1}
        (fwd_inner_bound
          (fwd_stage_bound17 len{1})
          len{1} start{1} j{1}) /\
      zetasp{1} = Hpoly_loop.jzetas /\
      zetas{2} = NTT_Fq.zetas /\
      zetasctr{1} = zetasctr{2} /\
      len{1} = len{2} /\
      fwd_len_ok len{1} /\
      0 < len{1} /\
      start{1} = start{2} /\
      0 <= start{1} < 256 /\
      start{1} + 2 * len{1} <= 256 /\
      start{1} =
        2 * len{1} *
        (zetasctr{1} - 1 - fwd_zbase len{1}) /\
      1 <= zetasctr{1} < 256 /\
      zeta_0{1} = BArray1024.get32 Hpoly_loop.jzetas zetasctr{1} /\
      zeta_{2} = NTT_Fq.zetas.[zetasctr{2}] /\
      j{1} = j{2} /\
      cmp{1} = start{1} + len{1} /\
      start{1} <= j{1} <= start{1} + len{1}
    ).
    + wp.
      sp.
      ecall{1} (forward_twiddle_product_bound_call_ph
        rp{1} r{2} zetasctr{2} j{2} len{2} zeta_0{1} coeff{1}).
      wp.
      skip.
      move=> &1 &2 /=.
      move=> [hs [hoff [hcoeff [hinv hguards]]]].
      move: hinv => [hrepr hinv].
      move: hinv => [hbd hinv].
      move: hinv => [hzetasp hinv].
      move: hinv => [hzetas hinv].
      move: hinv => [hzc_eq hinv].
      move: hinv => [hlen_eq hinv].
      move: hinv => [hlenok hinv].
      move: hinv => [hlen hinv].
      move: hinv => [hstart_eq hinv].
      move: hinv => [hstart_rng hinv].
      move: hinv => [hblock hinv].
      move: hinv => [hzctr hinv].
      move: hinv => [hzcrng hinv].
      move: hinv => [hzeta0 hinv].
      move: hinv => [hzeta hinv].
      move: hinv => [hj_eq [hcmp hjrng]].
      move: hstart_rng => [hstart0 hstartlt].
      move: hzcrng => [hzc_lo hzc_hi].
      move: hjrng => [hj_ge hj_le].
      move: hguards => [hj_guard1 hj_guard2].
      split.
      + split; first exact hrepr.
        split; first by smt().
        split; first by smt().
        split.
        + by rewrite hzeta0 hzc_eq.
        split.
        + by rewrite hcoeff hoff hj_eq hlen_eq.
        split.
        + rewrite hzeta0 hcoeff hoff.
          have hprod :=
            forward_twiddle_product_bound_from_inner17
              rp{1} len{1} start{1} j{1} zetasctr{1}
              hbd hlenok hlen _ _ _.
          + by smt().
          + by smt().
          + by smt().
          move: hprod.
          by rewrite /Hpoly_loop.jzetas.
        move=> _.
        rewrite hzeta0 hcoeff hoff.
        have hprod :=
          forward_twiddle_product_bound_from_inner17
            rp{1} len{1} start{1} j{1} zetasctr{1}
            hbd hlenok hlen _ _ _.
        + by smt().
        + by smt().
        + by smt().
        move: hprod.
        by rewrite /Hpoly_loop.jzetas.
      move=> _ result [ht hbwt].
      have hstep :=
        forward_butterfly_step_bound_by
          rp{1} r{2} j{1} len{1} start{1} s{1} result
          (fwd_stage_bound17 len{1})
          hrepr hbd _ hlen _ _ _ hs _ _ hbwt.
      + by smt().
      + by smt().
      + by smt().
      + by smt().
      + exact (fwd_stage_bound17_ge16 len{1} hlenok).
      + have hrange := fwd_stage_bound17_range len{1} hlenok.
        smt().
      move: hstep.
      rewrite ht -hzeta hj_eq hlen_eq.
      move=> [hpoly hbound].
      rewrite hoff hj_eq hlen_eq.
      split.
      + split; first exact hpoly.
        split; first exact hbound.
        by smt().
      by smt().
    wp.
    skip.
    move=> &1 &2 /=.
    move=> [hm hguards].
    move: hm => [hrepr hm].
    move: hm => [hbd hm].
    move: hm => [hzetasp hm].
    move: hm => [hzetas hm].
    move: hm => [hzc_eq hm].
    move: hm => [hlen_eq hm].
    move: hm => [hlenok hm].
    move: hm => [hlen hm].
    move: hm => [hstart_eq hm].
    move: hm => [hstart_rng hzctr].
    move: hguards => [hstart_guard1 hstart_guard2].
    move: hstart_rng => [hstart_ge hstart_le].
    have hstart_lt : 0 <= start{1} < 256 by smt().
    have hblock :=
      fwd_block_end_bound len{1} start{1} zetasctr{1}
        hlenok hlen hstart_lt hzctr.
    have hzcr :=
      fwd_read_range len{1} start{1} zetasctr{1}
        hlenok hlen hstart_lt hzctr.
    split.
    + split.
      + split; first exact hrepr.
        split.
        + move=> i hi.
          rewrite -fwd_middle_to_inner.
          exact (hbd i hi).
        split; first exact hzetasp.
        split; first exact hzetas.
        split; first by smt().
        split; first exact hlen_eq.
        split; first exact hlenok.
        split; first exact hlen.
        split; first exact hstart_eq.
        split; first exact hstart_lt.
        split; first exact hblock.
        split; first by smt().
        split; first exact hzcr.
        split; first by rewrite hzetasp.
        split; first by rewrite hzetas.
        split; first exact hstart_eq.
        by smt().
      by smt().
    move=> jL rpL jR rR hnotL hnotR hinv.
    move: hinv => [hreprL hinv].
    move: hinv => [hbdL hinv].
    move: hinv => [hzetaspL hinv].
    move: hinv => [hzetasL hinv].
    move: hinv => [hzcL hinv].
    move: hinv => [hlenL_eq hinv].
    move: hinv => [hlenL_ok hinv].
    move: hinv => [hlenL hinv].
    move: hinv => [hstartL_eq0 hinv].
    move: hinv => [hstartL_rng hinv].
    move: hinv => [hblockL hinv].
    move: hinv => [hzctrL hinv].
    move: hinv => [hzcrL hinv].
    move: hinv => [hzeta0L hinv].
    move: hinv => [hzetaL hinv].
    move: hinv => [hj_eqL [hcmpL hjrngL]].
    move: hstartL_rng => [hstartL_ge hstartL_lt].
    have hjL_ge : start{1} <= jL by smt().
    have hjL_le : jL <= start{1} + len{1} by smt().
    have hj_end : jL = start{1} + len{1} by smt().
    have hstart_new : jL + len{1} = start{1} + 2 * len{1} by smt().
    have hbdmid :
      barray256_bound_by rpL
        (fwd_middle_bound
          (fwd_stage_bound17 len{1}) (jL + len{1})).
    + move=> i hi.
      have htmp := hbdL i hi.
      have heq :=
        fwd_inner_exit_to_middle
          (fwd_stage_bound17 len{1}) len{1} start{1} i
          hstartL_ge hlenL.
      rewrite hstart_new.
      move: htmp.
      by rewrite hj_end heq.
    split.
    + split; first exact hreprL.
      split; first exact hbdmid.
      split; first exact hzetaspL.
      split; first exact hzetasL.
      split; first exact hzcL.
      split; first exact hlenL_eq.
      split; first exact hlenL_ok.
      split; first exact hlenL.
      split; first by smt().
      split; first by smt().
      by smt().
    by smt().
  wp.
  skip.
  move=> &1 &2 /=.
  move=> [ho hguards].
  move: ho => [hrepr ho].
  move: ho => [hbd ho].
  move: ho => [hzetasp ho].
  move: ho => [hzetas ho].
  move: ho => [hzc_eq ho].
  move: ho => [hlen_eq ho].
  move: ho => [hlenok hzbase].
  move: hguards => [hlen_pos hlen_guard].
  split.
  + split; first exact hrepr.
    split.
    + move=> i hi.
      rewrite fwd_middle_start_const /const_bound.
      exact (hbd i hi).
    split; first exact hzetasp.
    split; first exact hzetas.
    split; first exact hzc_eq.
    split; first exact hlen_eq.
    split; first exact hlenok.
    split; first exact hlen_pos.
    by smt().
  move=> rpL startL zcL rR startR zcR hnotL hnotR hm.
  move: hm => [hreprL hm].
  move: hm => [hbdL hm].
  move: hm => [hzetaspL hm].
  move: hm => [hzetasL hm].
  move: hm => [hzcL hm].
  move: hm => [hlenL_eq hm].
  move: hm => [hlenL_ok hm].
  move: hm => [hlenL_pos hm].
  move: hm => [hstart_eqL hm].
  move: hm => [hstart_rngL hstart_zcL].
  have hstart_end : startL = 256 by smt().
  have hshift : len{1} `|>>` 1 = len{1} %/ 2.
  + by apply int_shr1_div2; smt().
  have hlen_next :=
    fwd_len_next_ok len{1} hlenL_ok hlenL_pos.
  have hzbase_next :=
    fwd_stage_zbase_exit len{1} zcL
      hlenL_ok hlenL_pos _.
  + by smt().
  have hbdconst :
    barray256_bound_by rpL
      (const_bound
        (fwd_stage_bound17 (len{1} `|>>` 1))).
  + move=> i hi.
    have htmp := hbdL i hi.
    move: htmp.
    rewrite hstart_end.
    rewrite (fwd_middle_exit_const
               (fwd_stage_bound17 len{1}) 256 i _ _).
    + by move: hi; rewrite mem_range.
    + trivial.
    rewrite /const_bound /fwd_stage_bound17.
    have hstage_next :=
      fwd_stage_bound17_next len{1} hlenL_ok hlenL_pos.
    smt().
  split.
  + split; first exact hreprL.
    split; first exact hbdconst.
    split; first exact hzetaspL.
    split; first exact hzetasL.
    split; first exact hzcL.
    split; first by smt().
    split; first by rewrite hshift; exact hlen_next.
    by rewrite hshift; exact hzbase_next.
  by rewrite hshift; smt().
wp.
skip.
move=> &1 &2 /=.
move=> [hpre hzetas2].
split.
+ split.
  + exact (NTT_Fq.poly_repr_bound_repr rp{1} r{2} 17 hpre).
  split.
  + rewrite /fwd_stage_bound17 /fwd_stage_bound.
    exact (barray256_bound_by_const rp{1} 17
             (NTT_Fq.poly_repr_bound_bound rp{1} r{2} 17 hpre)).
  split; first by [].
  split; first by rewrite /fwd_len_ok.
  by rewrite /fwd_zbase.
by smt().
qed.

lemma loop_poly_ntt_correct17 p :
  hoare [Hpoly_loop.M._poly_ntt :
    NTT_Fq.poly_repr_bound rp p 17 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 25].
proof.
by conseq poly_ntt_core_ref17
  (NTTFullAlgebra.ntt_full_ntt p) => /#.
qed.

lemma target_poly_ntt_correct17 p :
  hoare [Target._poly_ntt :
    NTT_Fq.poly_repr_bound rp p 17 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 25].
proof.
have hloop_core :
  hoare [Hpoly_loop.M._poly_ntt :
    NTT_Fq.poly_repr_bound rp p 17 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 25].
+ exact (loop_poly_ntt_correct17 p).
by conseq TargetNTTRefinement.poly_ntt_loop_equiv hloop_core => /#.
qed.

lemma wide_polyvec_ntt_verify_unpack_count2_bound25
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Wide._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound17 xp0 p0 p1
    ==>
    verify_unpack_ntt_repr_bound25 res p0 p1 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
proc.
rcondt 3; first by auto.
rcondt 8; first by auto; call (_ : true); auto.
rcondf 13; first by
  auto; call (_ : true); auto; call (_ : true); auto.
wp.
call (target_poly_ntt_correct17 p1).
wp.
call (target_poly_ntt_correct17 p0).
wp.
skip.
move=> &hr [-> [hcount hin]].
move: hin.
rewrite /verify_unpack_ntt_input_repr_bound17.
move=> [hin0 hin1].
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
have hrepr0 :
    NTT_Fq.poly_repr_bound
      (TargetKeygenM23WideSupport.poly_slice xp0 0) p0 17.
+ have hbridge :
      (KeygenM23ArithmeticSpec.wide_slice_repr_bound xp0 0 p0 17 <=>
       NTT_Fq.poly_repr_bound
         (TargetKeygenM23WideSupport.poly_slice xp0 0) p0 17).
  + apply TargetKeygenM23WideSupport.wide_slice_poly_repr_bound.
    exact hbound0.
  move: hin0.
  by rewrite hbridge.
have hrepr1 :
    NTT_Fq.poly_repr_bound
      (TargetKeygenM23WideSupport.poly_slice
         xp0 KeygenM23MatrixSpec.poly_words_i) p1 17.
+ have hbridge :
      (KeygenM23ArithmeticSpec.wide_slice_repr_bound
         xp0 KeygenM23MatrixSpec.poly_words_i p1 17 <=>
       NTT_Fq.poly_repr_bound
         (TargetKeygenM23WideSupport.poly_slice
            xp0 KeygenM23MatrixSpec.poly_words_i) p1 17).
  + apply TargetKeygenM23WideSupport.wide_slice_poly_repr_bound.
    exact hbound1.
  move: hin1.
  by rewrite hbridge.
split.
+ exact hrepr0.
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
  exact hrepr1.
move=> _ r1 hr1.
have hsame0 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0) 0 = r0.
+ apply TargetKeygenM23WideSupport.poly_slice_put_same.
  exact hbound0.
have hother10 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1) 0 =
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0) 0.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound1.
  + exact hbound0.
  + left.
    smt().
have hsame1 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      KeygenM23MatrixSpec.poly_words_i = r1.
+ apply TargetKeygenM23WideSupport.poly_slice_put_same.
  exact hbound1.
have hpost0 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      0 (NTTFullSpec.full_ntt p0) 25.
+ rewrite TargetKeygenM23WideSupport.wide_slice_poly_repr_bound 1:hbound0.
  by rewrite hother10 hsame0.
have hpost1 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      KeygenM23MatrixSpec.poly_words_i
      (NTTFullSpec.full_ntt p1) 25.
+ rewrite TargetKeygenM23WideSupport.wide_slice_poly_repr_bound 1:hbound1.
  by rewrite hsame1.
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
simplify.
rewrite /verify_unpack_ntt_repr_bound25.
split.
+ split.
  + exact hpost0.
  + move: hpost1.
    by rewrite /KeygenM23MatrixSpec.poly_words_i /=.
+ move: htail2.
  by rewrite /verify_unpack_ntt_words
             /verify_unpack_ntt_polys
             /KeygenM23MatrixSpec.poly_words_i /=.
qed.

lemma verify_unpack_ntt_repr_bound25_forward_repr
    (before after : BArray8192.t) (p0 p1 : Rq.poly) :
  verify_unpack_ntt_input_repr_bound17 before p0 p1 =>
  verify_unpack_ntt_repr_bound25 after p0 p1 =>
  NTTRowProductSpec.vector_forward_repr
    verify_unpack_ntt_polys
    (fun col =>
      KeygenM23ArithmeticSpec.wide_poly
        after (col * KeygenM23MatrixSpec.poly_words_i))
    (fun col =>
      KeygenM23ArithmeticSpec.wide_poly
        before (col * KeygenM23MatrixSpec.poly_words_i)).
proof.
rewrite /verify_unpack_ntt_input_repr_bound17
        /verify_unpack_ntt_repr_bound25
        /NTTRowProductSpec.vector_forward_repr.
move=> [hin0 hin1] [hout0 hout1] col hcol.
case (col = 0) => h0.
+ subst col.
  move: hin0 hout0.
  rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  by move=> [-> _] [-> _].
have h1 : col = 1 by smt().
subst col.
move: hin1 hout1.
rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound
        /KeygenM23MatrixSpec.poly_words_i /=.
by move=> [-> _] [-> _].
qed.

lemma parent_polyvec_ntt_verify_unpack_count2_bound25
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Parent._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound17 xp0 p0 p1
    ==>
    verify_unpack_ntt_repr_bound25 res p0 p1 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
have hwide := wide_polyvec_ntt_verify_unpack_count2_bound25 xp0 p0 p1.
by conseq VerifyUnpackV3NttPostFreeze.parent_polyvec_ntt_equiv_wide_count2
  hwide => /#.
qed.

lemma parent_polyvec_ntt_verify_unpack_count2_correct
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Parent._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound17 xp0 p0 p1
    ==>
    NTTRowProductSpec.vector_forward_repr
      verify_unpack_ntt_polys
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          res (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          xp0 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
have hparent := parent_polyvec_ntt_verify_unpack_count2_bound25 xp0 p0 p1.
conseq hparent => //=.
move=> &m [_ [_ hin]] result [hout htail].
split.
+ exact
    (verify_unpack_ntt_repr_bound25_forward_repr
      xp0 result p0 p1 hin hout).
+ exact htail.
qed.

lemma verify_unpack_polyvec_ntt_count2_bound25
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Verify._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound17 xp0 p0 p1
    ==>
    verify_unpack_ntt_repr_bound25 res p0 p1 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
by conseq VerifyUnpackV3NttPostFreeze.verify_unpack_polyvec_ntt_equiv_parent
  (parent_polyvec_ntt_verify_unpack_count2_bound25 xp0 p0 p1) => /#.
qed.

lemma verify_unpack_polyvec_ntt_count2_correct
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Verify._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound17 xp0 p0 p1
    ==>
    NTTRowProductSpec.vector_forward_repr
      verify_unpack_ntt_polys
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          res (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          xp0 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
by conseq VerifyUnpackV3NttPostFreeze.verify_unpack_polyvec_ntt_equiv_parent
  (parent_polyvec_ntt_verify_unpack_count2_correct xp0 p0 p1) => /#.
qed.

lemma verify_unpack_polyvec_ntt_count2_full_correct
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Verify._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound17 xp0 p0 p1
    ==>
    verify_unpack_ntt_repr_bound25 res p0 p1 /\
    NTTRowProductSpec.vector_forward_repr
      verify_unpack_ntt_polys
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          res (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          xp0 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
conseq
  (verify_unpack_polyvec_ntt_count2_bound25 xp0 p0 p1)
  (verify_unpack_polyvec_ntt_count2_correct xp0 p0 p1) => />.
qed.

lemma verify_unpack_polyvec_ntt_count2_full_correct17
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Verify._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound17 xp0 p0 p1
    ==>
    verify_unpack_ntt_repr_bound25 res p0 p1 /\
    NTTRowProductSpec.vector_forward_repr
      verify_unpack_ntt_polys
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          res (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          xp0 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
exact (verify_unpack_polyvec_ntt_count2_full_correct xp0 p0 p1).
qed.

end VerifyUnpackV3NttBound17PostFreeze.
