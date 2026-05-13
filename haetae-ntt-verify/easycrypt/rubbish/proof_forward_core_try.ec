require import RefJasminNTT.
require import AllCore IntDiv CoreMap List Distr Ring StdOrder BitEncoding.
from Jasmin require import JWord JModel_x86.
import SLH64.
require import Array256 BArray1024.
require import Fq GFq NTT_Fq Hpoly_extract.
import Zq IntOrder.

theory ProofForwardCoreTry.

equiv poly_ntt_core_ref_try :
  Hpoly_extract.M._poly_ntt ~ NTT_Fq.NTT.ntt :
  NTT_Fq.poly_repr_bound rp{1} r{2} 16 /\
  zetas{2} = NTT_Fq.zetas
  ==> NTT_Fq.poly_repr_bound res{1} res{2} 24.
proof.
proc.
wp.
while (
  NTT_Fq.poly_repr rp{1} r{2} /\
  RefJasminNTT.barray256_bound_by rp{1}
    (RefJasminNTT.const_bound (RefJasminNTT.fwd_stage_bound len{1})) /\
  zetasp{1} = Hpoly_extract.jzetas /\
  zetas{2} = NTT_Fq.zetas /\
  zetasctr{1} = zetasctr{2} /\
  len{1} = len{2} /\
  RefJasminNTT.fwd_len_ok len{1} /\
  zetasctr{1} = RefJasminNTT.fwd_zbase len{1}
).
+ wp.
  while (
    NTT_Fq.poly_repr rp{1} r{2} /\
    RefJasminNTT.barray256_bound_by rp{1}
      (RefJasminNTT.fwd_middle_bound
        (RefJasminNTT.fwd_stage_bound len{1}) start{1}) /\
    zetasp{1} = Hpoly_extract.jzetas /\
    zetas{2} = NTT_Fq.zetas /\
    zetasctr{1} = zetasctr{2} /\
    len{1} = len{2} /\
    RefJasminNTT.fwd_len_ok len{1} /\
    0 < len{1} /\
    start{1} = start{2} /\
    0 <= start{1} <= 256 /\
    start{1} =
      2 * len{1} *
        (zetasctr{1} - RefJasminNTT.fwd_zbase len{1})
  ).
  + wp.
    while (
      NTT_Fq.poly_repr rp{1} r{2} /\
      RefJasminNTT.barray256_bound_by rp{1}
        (RefJasminNTT.fwd_inner_bound
          (RefJasminNTT.fwd_stage_bound len{1})
          len{1} start{1} j{1}) /\
      zetasp{1} = Hpoly_extract.jzetas /\
      zetas{2} = NTT_Fq.zetas /\
      zetasctr{1} = zetasctr{2} /\
      len{1} = len{2} /\
      RefJasminNTT.fwd_len_ok len{1} /\
      0 < len{1} /\
      start{1} = start{2} /\
      0 <= start{1} < 256 /\
      start{1} + 2 * len{1} <= 256 /\
      start{1} =
        2 * len{1} *
        (zetasctr{1} - 1 - RefJasminNTT.fwd_zbase len{1}) /\
      1 <= zetasctr{1} < 256 /\
      zeta_0{1} = BArray1024.get32 Hpoly_extract.jzetas zetasctr{1} /\
      zeta_{2} = NTT_Fq.zetas.[zetasctr{2}] /\
      j{1} = j{2} /\
      cmp{1} = start{1} + len{1} /\
      start{1} <= j{1} <= start{1} + len{1}
    ).
    + wp.
      sp.
      ecall{1} (RefJasminNTT.forward_twiddle_product_bound_call_ph
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
            RefJasminNTT.forward_twiddle_product_bound_from_inner
              rp{1} len{1} start{1} j{1} zetasctr{1}
              hbd hlenok hlen _ _ _.
          + by smt().
          + by smt().
          + by smt().
          move: hprod.
          by rewrite /Hpoly_extract.jzetas.
        move=> _.
        rewrite hzeta0 hcoeff hoff.
        have hprod :=
          RefJasminNTT.forward_twiddle_product_bound_from_inner
            rp{1} len{1} start{1} j{1} zetasctr{1}
            hbd hlenok hlen _ _ _.
        + by smt().
        + by smt().
        + by smt().
        move: hprod.
        by rewrite /Hpoly_extract.jzetas.
      move=> _ result [ht hbwt].
      have hstep :=
        RefJasminNTT.forward_butterfly_step_bound_by
          rp{1} r{2} j{1} len{1} start{1} s{1} result
          (RefJasminNTT.fwd_stage_bound len{1})
          hrepr hbd _ hlen _ _ _ hs _ _ hbwt.
      + by smt().
      + by smt().
      + by smt().
      + by smt().
      + exact (RefJasminNTT.fwd_stage_bound_ge16 len{1} hlenok).
      + by have := RefJasminNTT.fwd_stage_bound_range len{1} hlenok; smt().
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
      RefJasminNTT.fwd_block_end_bound len{1} start{1} zetasctr{1}
        hlenok hlen hstart_lt hzctr.
    have hzcr :=
      RefJasminNTT.fwd_read_range len{1} start{1} zetasctr{1}
        hlenok hlen hstart_lt hzctr.
    split.
    + split.
      + split; first exact hrepr.
        split.
        + move=> i hi.
          rewrite -RefJasminNTT.fwd_middle_to_inner.
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
      RefJasminNTT.barray256_bound_by rpL
        (RefJasminNTT.fwd_middle_bound
          (RefJasminNTT.fwd_stage_bound len{1}) (jL + len{1})).
    + move=> i hi.
      have htmp := hbdL i hi.
      have heq :=
        RefJasminNTT.fwd_inner_exit_to_middle
          (RefJasminNTT.fwd_stage_bound len{1}) len{1} start{1} i
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
      rewrite RefJasminNTT.fwd_middle_start_const /RefJasminNTT.const_bound.
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
  + by apply RefJasminNTT.int_shr1_div2; smt().
  have hstage_next :=
    RefJasminNTT.fwd_stage_next len{1} hlenL_ok hlenL_pos.
  have hstage_shift :
    RefJasminNTT.fwd_stage_bound (len{1} `|>>` 1) =
    RefJasminNTT.fwd_stage_bound len{1} + 1.
  + by rewrite hshift hstage_next.
  have hlen_next :=
    RefJasminNTT.fwd_len_next_ok len{1} hlenL_ok hlenL_pos.
  have hzbase_next :=
    RefJasminNTT.fwd_stage_zbase_exit len{1} zcL
      hlenL_ok hlenL_pos _.
  + by smt().
  have hbdconst :
    RefJasminNTT.barray256_bound_by rpL
      (RefJasminNTT.const_bound
        (RefJasminNTT.fwd_stage_bound (len{1} `|>>` 1))).
  + move=> i hi.
    have htmp := hbdL i hi.
    move: htmp.
    rewrite hstart_end.
    rewrite (RefJasminNTT.fwd_middle_exit_const
               (RefJasminNTT.fwd_stage_bound len{1}) 256 i _ _).
    + by move: hi; rewrite mem_range.
    + trivial.
    rewrite /RefJasminNTT.const_bound.
    by smt().
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
  + exact (NTT_Fq.poly_repr_bound_repr rp{1} r{2} 16 hpre).
  split.
  + rewrite /RefJasminNTT.fwd_stage_bound.
    exact (RefJasminNTT.barray256_bound_by_const rp{1} 16
             (NTT_Fq.poly_repr_bound_bound rp{1} r{2} 16 hpre)).
  split; first by [].
  split; first by rewrite /RefJasminNTT.fwd_len_ok.
  by rewrite /RefJasminNTT.fwd_zbase.
  by smt().
qed.

end ProofForwardCoreTry.
