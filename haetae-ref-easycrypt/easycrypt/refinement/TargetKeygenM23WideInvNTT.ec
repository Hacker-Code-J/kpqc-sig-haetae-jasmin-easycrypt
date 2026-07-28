require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import TargetKeygenM23WideSupport
               TargetKeygenM23Matrix
               KeygenM23MatrixSpec KeygenM23ArithmeticSpec
               NTT_Fq NTTFullSpec TargetNTTRefinement.

theory TargetKeygenM23WideInvNTT.

module Parent = TargetKeygenM23WideSupport.Parent.
module Single = TargetKeygenM23WideSupport.Single.
import TargetKeygenM23WideSupport.

lemma int_shl1_mul2 x :
  x `<<` 1 = x * 2.
proof.
by rewrite /(`<<`) /=.
qed.

module WideInvSpec = {
  proc _polyvec_invntt
      (xp : BArray8192.t, count : W64.t) : BArray8192.t = {
    var poly : W64.t;
    var base : W64.t;
    var rp : BArray1024.t;

    poly <- W64.zero;
    base <- W64.zero;
    while (poly \ult count) {
      rp <- poly_slice xp (W64.to_uint base);
      rp <@ Single._poly_invntt(rp);
      xp <- put_poly_slice xp (W64.to_uint base) rp;
      base <- base + W64.of_int 256;
      poly <- poly + W64.one;
    }
    return xp;
  }
}.

lemma polyvec_invntt_mode2_equiv :
  equiv [Parent._polyvec_invntt ~ WideInvSpec._polyvec_invntt :
    ={xp, count} /\
    count{1} =
      W64.of_int KeygenM23MatrixSpec.mode2_rows_i
    ==> ={res}].
proof.
proc.
while
  (={xp, poly, base, count} /\
   count{1} =
     W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
   W64.to_uint poly{1} <=
     KeygenM23MatrixSpec.mode2_rows_i /\
   W64.to_uint base{1} =
     KeygenM23MatrixSpec.poly_words_i *
       W64.to_uint poly{1} /\
   0 <= W64.to_uint base{1} /\
   W64.to_uint base{1} +
     KeygenM23MatrixSpec.poly_words_i <=
       KeygenM23MatrixSpec.array_words_i /\
   zetasp{1} = HpolyTarget.jzetas_inv).
+ inline Single._poly_invntt.
  seq 2 6 :
    (={poly, base, count, zetasp} /\
     zetasp{1} = HpolyTarget.jzetas_inv /\
     count{1} =
       W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint poly{1} <
       KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint base{1} =
       KeygenM23MatrixSpec.poly_words_i *
         W64.to_uint poly{1} /\
     0 <= W64.to_uint base{1} /\
     W64.to_uint base{1} +
       KeygenM23MatrixSpec.poly_words_i <=
         KeygenM23MatrixSpec.array_words_i /\
     W64.to_uint zetasctr{1} = zetasctr{2} /\
     W64.to_uint len{1} = len{2} /\
     KeygenM23MatrixSpec.ntt_stage_len
       (W64.to_uint len{1}) /\
     1 <= W64.to_uint len{1} <= 256 /\
     0 <= W64.to_uint zetasctr{1} <= 255 /\
     W64.to_uint zetasctr{1} * W64.to_uint len{1} =
       256 * (W64.to_uint len{1} - 1) /\
     poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
     poly_slice_frame xp{2} xp{1} (W64.to_uint base{1})).
  + wp.
    skip => /> &2 hpolyle hbaseeq hbase0 hbasecap hguard.
    move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.mode2_rows_i /=.
    trivial.
  seq 1 1 :
    (={poly, base, count, zetasp} /\
     zetasp{1} = HpolyTarget.jzetas_inv /\
     count{1} =
       W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint poly{1} <
       KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint base{1} =
       KeygenM23MatrixSpec.poly_words_i *
         W64.to_uint poly{1} /\
     0 <= W64.to_uint base{1} /\
     W64.to_uint base{1} +
       KeygenM23MatrixSpec.poly_words_i <=
         KeygenM23MatrixSpec.array_words_i /\
     W64.to_uint zetasctr{1} = zetasctr{2} /\
     W64.to_uint len{1} = len{2} /\
     KeygenM23MatrixSpec.ntt_stage_len
       (W64.to_uint len{1}) /\
     1 <= W64.to_uint len{1} <= 256 /\
     0 <= W64.to_uint zetasctr{1} <= 255 /\
     W64.to_uint zetasctr{1} * W64.to_uint len{1} =
       256 * (W64.to_uint len{1} - 1) /\
     poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
     poly_slice_frame xp{2} xp{1} (W64.to_uint base{1})).
  + while
      (={poly, base, count, zetasp} /\
       zetasp{1} = HpolyTarget.jzetas_inv /\
       count{1} =
         W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
       W64.to_uint poly{1} <
         KeygenM23MatrixSpec.mode2_rows_i /\
       W64.to_uint base{1} =
         KeygenM23MatrixSpec.poly_words_i *
           W64.to_uint poly{1} /\
       0 <= W64.to_uint base{1} /\
       W64.to_uint base{1} +
         KeygenM23MatrixSpec.poly_words_i <=
           KeygenM23MatrixSpec.array_words_i /\
       W64.to_uint zetasctr{1} = zetasctr{2} /\
       W64.to_uint len{1} = len{2} /\
       KeygenM23MatrixSpec.ntt_stage_len
         (W64.to_uint len{1}) /\
       1 <= W64.to_uint len{1} <= 256 /\
       0 <= W64.to_uint zetasctr{1} <= 255 /\
       W64.to_uint zetasctr{1} * W64.to_uint len{1} =
         256 * (W64.to_uint len{1} - 1) /\
       poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
       poly_slice_frame xp{2} xp{1} (W64.to_uint base{1})).
    + wp.
      while
        (={poly, base, count, zetasp} /\
         zetasp{1} = HpolyTarget.jzetas_inv /\
         count{1} =
           W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
         W64.to_uint poly{1} <
           KeygenM23MatrixSpec.mode2_rows_i /\
         W64.to_uint base{1} =
           KeygenM23MatrixSpec.poly_words_i *
             W64.to_uint poly{1} /\
         0 <= W64.to_uint base{1} /\
         W64.to_uint base{1} +
           KeygenM23MatrixSpec.poly_words_i <=
             KeygenM23MatrixSpec.array_words_i /\
         W64.to_uint zetasctr{1} = zetasctr{2} /\
         W64.to_uint len{1} = len{2} /\
         W64.to_uint start{1} = start{2} /\
         KeygenM23MatrixSpec.ntt_stage_len
           (W64.to_uint len{1}) /\
         1 <= W64.to_uint len{1} <= 128 /\
         poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
         poly_slice_frame xp{2} xp{1}
           (W64.to_uint base{1}) /\
         exists z0,
           0 <= z0 <= 255 /\
           z0 * W64.to_uint len{1} =
             256 * (W64.to_uint len{1} - 1) /\
           z0 <= W64.to_uint zetasctr{1} <= 255 /\
           0 <= W64.to_uint start{1} <= 256 /\
           W64.to_uint start{1} =
             2 * (W64.to_uint zetasctr{1} - z0) *
               W64.to_uint len{1} /\
           2 * (W64.to_uint zetasctr{1} - z0) *
             W64.to_uint len{1} <= 256).
      + wp.
        while
          (={poly, base, count, zetasp, zeta_0} /\
           zetasp{1} = HpolyTarget.jzetas_inv /\
           count{1} =
             W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
           W64.to_uint poly{1} <
             KeygenM23MatrixSpec.mode2_rows_i /\
           W64.to_uint base{1} =
             KeygenM23MatrixSpec.poly_words_i *
               W64.to_uint poly{1} /\
           0 <= W64.to_uint base{1} /\
           W64.to_uint base{1} +
             KeygenM23MatrixSpec.poly_words_i <=
               KeygenM23MatrixSpec.array_words_i /\
           W64.to_uint zetasctr{1} = zetasctr{2} /\
           W64.to_uint len{1} = len{2} /\
           W64.to_uint start{1} = start{2} /\
           W64.to_uint j{1} = j{2} /\
           W64.to_uint cmp{1} = cmp{2} /\
           KeygenM23MatrixSpec.ntt_stage_len
             (W64.to_uint len{1}) /\
           1 <= W64.to_uint len{1} <= 128 /\
           0 <= W64.to_uint start{1} < 256 /\
           W64.to_uint start{1} <= W64.to_uint j{1} <=
             W64.to_uint cmp{1} /\
           W64.to_uint cmp{1} =
             W64.to_uint start{1} + W64.to_uint len{1} /\
           W64.to_uint start{1} +
             2 * W64.to_uint len{1} <= 256 /\
           poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
           poly_slice_frame xp{2} xp{1}
             (W64.to_uint base{1}) /\
           exists z0,
             0 <= z0 <= 255 /\
             z0 * W64.to_uint len{1} =
               256 * (W64.to_uint len{1} - 1) /\
             z0 + 1 <= W64.to_uint zetasctr{1} <= 255 /\
             W64.to_uint start{1} =
               2 * (W64.to_uint zetasctr{1} - 1 - z0) *
                 W64.to_uint len{1} /\
             W64.to_uint start{1} +
               2 * W64.to_uint len{1} =
                 2 * (W64.to_uint zetasctr{1} - z0) *
                   W64.to_uint len{1}).
        + wp.
          call parent_single_fqmul_equiv.
          wp.
          skip => /> &1 &2 hpoly hbase hbase0 hbasecap
                      hsched hlen1 hlen128 hstart0 hstartlt
                      hjlow hjhigh hcmp hblock hframe
                      z0 hz00 hz0255 hzrel hzlow hzup
                      hstartrel hnextrel hguardL hguardR.
          have hjlt : W64.to_uint j{1} < W64.to_uint cmp{1}.
          + exact hguardR.
          have hj256 : W64.to_uint j{1} < 256 by smt().
          have hjlen256 :
              W64.to_uint j{1} + W64.to_uint len{1} < 256 by
            smt().
          have hjlen :
              W64.to_uint (j{1} + len{1}) =
                W64.to_uint j{1} + W64.to_uint len{1}.
          + rewrite W64.to_uintD_small 1:/#.
            trivial.
          have hj1 :
              W64.to_uint (j{1} + W64.one) =
                W64.to_uint j{1} + 1.
          + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
            trivial.
          have hbasecap' := hbasecap.
          rewrite /KeygenM23MatrixSpec.array_words_i
                  /KeygenM23MatrixSpec.poly_words_i
                  /BArray8192.size /= in hbasecap'.
          have hbasej_small :
              W64.to_uint base{2} + W64.to_uint j{1} < 2048
            by smt().
          have hbasej :
              W64.to_uint (base{2} + j{1}) =
                W64.to_uint base{2} + W64.to_uint j{1}.
          + rewrite W64.to_uintD_small.
            + smt(W64.to_uint_cmp).
            trivial.
          have hbasejlen_small :
              W64.to_uint base{2} + W64.to_uint j{1} +
                W64.to_uint len{1} < 2048
            by smt().
          have hbasejlen :
              W64.to_uint (base{2} + (j{1} + len{1})) =
                W64.to_uint base{2} +
                  (W64.to_uint j{1} + W64.to_uint len{1}).
          + rewrite W64.to_uintD_small.
            + rewrite hjlen.
              smt(W64.to_uint_cmp).
            rewrite hjlen.
            ring.
          have hread1 :
              BArray8192.get32 xp{1}
                (W64.to_uint (base{2} + j{1})) =
              BArray1024.get32
                (poly_slice xp{1} (W64.to_uint base{2}))
                (W64.to_uint j{1}).
          + rewrite hbasej.
            rewrite poly_slice_get32 1:/# 1:/#.
            trivial.
          have hread2 :
              BArray8192.get32 xp{1}
                (W64.to_uint
                  (base{2} + (j{1} + len{1}))) =
              BArray1024.get32
                (poly_slice xp{1} (W64.to_uint base{2}))
                (W64.to_uint j{1} + W64.to_uint len{1}).
          + rewrite hbasejlen.
            rewrite poly_slice_get32 1:/# 1:/#.
            congr; ring.
          rewrite hread1 hread2.
          split; first trivial.
          move=> _ result_R.
          have hbaseok :
              0 <= W64.to_uint base{2} /\
              W64.to_uint base{2} +
                KeygenM23MatrixSpec.poly_words_i <=
                  KeygenM23MatrixSpec.array_words_i by smt().
          have hjok :
              0 <= W64.to_uint j{1} <
                KeygenM23MatrixSpec.poly_words_i by smt().
          have hjlenok :
              0 <= W64.to_uint j{1} + W64.to_uint len{1} <
                KeygenM23MatrixSpec.poly_words_i by smt().
          have hinner :=
            poly_slice_set32 xp{1} (W64.to_uint base{2})
              (W64.to_uint j{1})
              (BArray1024.get32
                 (poly_slice xp{1} (W64.to_uint base{2}))
                 (W64.to_uint j{1}) +
               BArray1024.get32
                 (poly_slice xp{1} (W64.to_uint base{2}))
                 (W64.to_uint j{1} + W64.to_uint len{1}))
              hbaseok hjok.
          have houter :=
            poly_slice_set32
              (BArray8192.set32 xp{1}
                (W64.to_uint base{2} + W64.to_uint j{1})
                (BArray1024.get32
                   (poly_slice xp{1} (W64.to_uint base{2}))
                   (W64.to_uint j{1}) +
                 BArray1024.get32
                   (poly_slice xp{1} (W64.to_uint base{2}))
                   (W64.to_uint j{1} + W64.to_uint len{1})))
              (W64.to_uint base{2})
              (W64.to_uint j{1} + W64.to_uint len{1})
              result_R hbaseok hjlenok.
          rewrite hinner in houter.
          have hframe1 :=
            poly_slice_frame_set32
              xp{2} xp{1} (W64.to_uint base{2})
              (W64.to_uint j{1})
              (BArray1024.get32
                 (poly_slice xp{1} (W64.to_uint base{2}))
                 (W64.to_uint j{1}) +
               BArray1024.get32
                 (poly_slice xp{1} (W64.to_uint base{2}))
                 (W64.to_uint j{1} +
                   W64.to_uint len{1}))
              hbaseok hjok hframe.
          have hframe2 :=
            poly_slice_frame_set32
              xp{2}
              (BArray8192.set32 xp{1}
                (W64.to_uint base{2} + W64.to_uint j{1})
                (BArray1024.get32
                   (poly_slice xp{1} (W64.to_uint base{2}))
                   (W64.to_uint j{1}) +
                 BArray1024.get32
                   (poly_slice xp{1} (W64.to_uint base{2}))
                   (W64.to_uint j{1} +
                     W64.to_uint len{1})))
              (W64.to_uint base{2})
              (W64.to_uint j{1} + W64.to_uint len{1})
              result_R hbaseok hjlenok hframe1.
          rewrite hbasej hbasejlen hj1 houter.
          rewrite !W64.ultE.
          smt().
        wp.
        skip => /> &1 &2 hpoly hbase hbase0 hbasecap
                    hsched hlen1 hlen128 hframe
                    z0 hz00 hz0255 hzrel hzlow hzup
                    hstart0 hstart256 hstartrel hcap
                    hguardL hguardR.
        have hstartlt : W64.to_uint start{1} < 256.
        + exact hguardR.
        split.
        + have hentry :=
            TargetKeygenM23Matrix.invntt_inner_entry
              start{1} len{1} zetasctr{1} z0
              hsched hlen1 hlen128 hz00 hz0255 hzrel hzlow hzup
              hstartrel hstartlt.
          have hzsucc :
              W64.to_uint (zetasctr{1} + W64.one) =
                W64.to_uint zetasctr{1} + 1.
          + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
            trivial.
          move: hentry.
          rewrite !W64.ultE /=.
          smt().
        move=> jL xpL hnword hnint hzsucc hsum
                hjlowx hjhighx hblockx hframe2
                z00 hz00x hz255x hzrelx hzlowx hzupx
                hstartrelx hnextrelx.
        have hexit :=
          TargetKeygenM23Matrix.invntt_inner_exit
            start{1} len{1} (zetasctr{1} + W64.one) jL z00
            hnword hjlowx hjhighx hsum hblockx hz00x hz255x
            hzrelx hzlowx hzupx hstartrelx hnextrelx.
        have hnew :
            W64.to_uint (jL + len{1}) =
              W64.to_uint jL + W64.to_uint len{1}.
        + rewrite W64.to_uintD_small 1:/#.
          trivial.
        move: hexit.
        rewrite !W64.ultE /=.
        smt().
      wp.
      skip => /> &1 &2 hpoly hbase hbase0 hbasecap
                  hsched hlen1 hlen256 hz0 hz255 hzrel
                  hframe hguardL hguardR.
      have hlenlt : W64.to_uint len{1} < 256 by
        exact hguardR.
      have hlen128 : W64.to_uint len{1} <= 128 by
        have :=
          KeygenM23MatrixSpec.ntt_stage_len_active_bounds
            (W64.to_uint len{1}) hsched hlenlt;
        smt().
      split.
      + split; first exact hlen128.
        exists (W64.to_uint zetasctr{1}).
        smt().
      move=> startR xpL zR hn1 hn2 hlen128x
              hframe2 z0x hz0x hz255x hzrel0
              hzlow hzup hstart0 hstart256 hstartrel hcap.
      have hstartge : 256 <= W64.to_uint startR by
        move: hn1; rewrite W64.ultE /=; smt().
      have hstarteq : W64.to_uint startR = 256 by smt().
      have hlennew :
          W64.to_uint (len{1} `<<` W8.one) =
            2 * W64.to_uint len{1}.
      + rewrite /(`<<`) W64.to_uint_shl 1:/# /=.
        rewrite modz_small; smt(W64.to_uint_cmp).
      have hschednew :
          KeygenM23MatrixSpec.ntt_stage_len
            (2 * W64.to_uint len{1}) by
        apply
          (KeygenM23MatrixSpec.ntt_stage_len_double
            (W64.to_uint len{1}) hsched hlenlt).
      have hblockeq :
          2 * (W64.to_uint zR - z0x) * W64.to_uint len{1} =
            256 by
        smt().
      rewrite hlennew int_shl1_mul2.
      split; first smt().
      split; first smt().
      move=> hlt.
      rewrite W64.ultE hlennew /=.
      smt().
    skip => />.
    move=> &1 &2 hpoly hbase hbase0 hbasecap
            hsched hlen1 hlen256 hz0 hz255 hzrel
            hframe.
    rewrite W64.ultE /=.
    trivial.
  seq 2 2 :
    (={poly, base, count, zetasp, zeta_0} /\
     zetasp{1} = HpolyTarget.jzetas_inv /\
     count{1} =
       W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint poly{1} <
       KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint base{1} =
       KeygenM23MatrixSpec.poly_words_i *
         W64.to_uint poly{1} /\
     0 <= W64.to_uint base{1} /\
     W64.to_uint base{1} +
       KeygenM23MatrixSpec.poly_words_i <=
         KeygenM23MatrixSpec.array_words_i /\
     W64.to_uint j{1} = j{2} /\
     0 <= W64.to_uint j{1} <= 256 /\
     poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
     poly_slice_frame xp{2} xp{1} (W64.to_uint base{1})).
  + auto => />.
  seq 1 1 :
    (={poly, base, count, zetasp, zeta_0} /\
     zetasp{1} = HpolyTarget.jzetas_inv /\
     count{1} =
       W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint poly{1} <
       KeygenM23MatrixSpec.mode2_rows_i /\
     W64.to_uint base{1} =
       KeygenM23MatrixSpec.poly_words_i *
         W64.to_uint poly{1} /\
     0 <= W64.to_uint base{1} /\
     W64.to_uint base{1} +
       KeygenM23MatrixSpec.poly_words_i <=
         KeygenM23MatrixSpec.array_words_i /\
     W64.to_uint j{1} = j{2} /\
     0 <= W64.to_uint j{1} <= 256 /\
     poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
     poly_slice_frame xp{2} xp{1} (W64.to_uint base{1})).
  + while
      (={poly, base, count, zetasp, zeta_0} /\
       zetasp{1} = HpolyTarget.jzetas_inv /\
       count{1} =
         W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
       W64.to_uint poly{1} <
         KeygenM23MatrixSpec.mode2_rows_i /\
       W64.to_uint base{1} =
         KeygenM23MatrixSpec.poly_words_i *
           W64.to_uint poly{1} /\
       0 <= W64.to_uint base{1} /\
       W64.to_uint base{1} +
         KeygenM23MatrixSpec.poly_words_i <=
           KeygenM23MatrixSpec.array_words_i /\
       W64.to_uint j{1} = j{2} /\
       0 <= W64.to_uint j{1} <= 256 /\
       poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
       poly_slice_frame xp{2} xp{1} (W64.to_uint base{1})).
    + wp.
      call parent_single_fqmul_equiv.
      wp.
      skip => /> &1 &2 hpoly hbase hbase0 hbasecap
                  hj hframe hguardL hguardR.
      move=> hjlt.
      have hj1 :
          W64.to_uint (j{1} + W64.one) =
            W64.to_uint j{1} + 1.
      + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        trivial.
      have hbasej :
          W64.to_uint (base{2} + j{1}) =
            W64.to_uint base{2} + W64.to_uint j{1}.
      + have hbasecap' := hbasecap.
        rewrite /KeygenM23MatrixSpec.array_words_i
                /KeygenM23MatrixSpec.poly_words_i
                /BArray8192.size /= in hbasecap'.
        rewrite W64.to_uintD_small.
        + smt(W64.to_uint_cmp).
        trivial.
      have hread :
          BArray8192.get32 xp{1}
            (W64.to_uint (base{2} + j{1})) =
          BArray1024.get32
            (poly_slice xp{1} (W64.to_uint base{2}))
            (W64.to_uint j{1}).
      + rewrite hbasej.
        rewrite poly_slice_get32 1:/# 1:/#.
        trivial.
      rewrite hread.
      split; first trivial.
      move=> _ result_R.
      have hbaseok :
          0 <= W64.to_uint base{2} /\
          W64.to_uint base{2} +
            KeygenM23MatrixSpec.poly_words_i <=
              KeygenM23MatrixSpec.array_words_i by smt().
      have hjok :
          0 <= W64.to_uint j{1} <
            KeygenM23MatrixSpec.poly_words_i by smt().
      have hslice_set :=
        poly_slice_set32 xp{1} (W64.to_uint base{2})
          (W64.to_uint j{1}) result_R hbaseok hjok.
      have hframe1 :=
        poly_slice_frame_set32
          xp{2} xp{1} (W64.to_uint base{2})
          (W64.to_uint j{1}) result_R
          hbaseok hjok hguardL.
      rewrite hbasej hj1 hslice_set !W64.ultE.
      smt().
    skip => /> &1 &2 hpoly hbase hbase0 hbasecap
                hj hjcap hframe.
    rewrite W64.ultE /=.
    trivial.
  wp.
  skip => /> &1 &2 hpoly hbase hbase0 hbasecap
              hj0 hjcap.
  move=> hframe.
  have hbaseok :
      0 <= W64.to_uint base{2} /\
      W64.to_uint base{2} +
        KeygenM23MatrixSpec.poly_words_i <=
          KeygenM23MatrixSpec.array_words_i by smt().
  have hreassemble :
      xp{1} =
        put_poly_slice xp{2} (W64.to_uint base{2})
          (poly_slice xp{1} (W64.to_uint base{2})).
  + apply poly_slice_reassemble.
    + exact hbaseok.
    + trivial.
    + exact hframe.
  have hpolysucc :
      W64.to_uint (poly{2} + W64.one) =
        W64.to_uint poly{2} + 1.
  + have hpolycmp := W64.to_uint_cmp poly{2}.
    have hsmall :
        W64.to_uint poly{2} + W64.to_uint W64.one <
          W64.modulus.
    + rewrite W64.to_uint1.
      move: hpoly hpolycmp.
      rewrite /KeygenM23MatrixSpec.mode2_rows_i.
      smt().
    rewrite W64.to_uintD_small 1:hsmall W64.to_uint1.
    trivial.
  have hbasesucc :
      W64.to_uint (base{2} + W64.of_int 256) =
        W64.to_uint base{2} + 256.
  + have hbasecmp := W64.to_uint_cmp base{2}.
    have hsmall :
        W64.to_uint base{2} +
          W64.to_uint (W64.of_int 256) < W64.modulus.
    + rewrite W64.of_uintK /=.
      move: hbasecap hbasecmp.
      rewrite /KeygenM23MatrixSpec.poly_words_i
              /KeygenM23MatrixSpec.array_words_i.
      smt().
    rewrite W64.to_uintD_small 1:hsmall W64.of_uintK /=.
    trivial.
  rewrite hreassemble hpolysucc hbasesucc
          /KeygenM23MatrixSpec.poly_words_i.
  smt().
auto => />.
qed.

lemma wide_inv_spec_mode2_correct18
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [WideInvSpec._polyvec_invntt :
    xp = xp0 /\
    count = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      xp0 0 p0 18 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      xp0 KeygenM23MatrixSpec.poly_words_i p1 18
    ==>
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res 0
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt p0)) 16 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res KeygenM23MatrixSpec.poly_words_i
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt p1)) 16 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res KeygenM23MatrixSpec.mode2_b_words_i].
proof.
proc.
rcondt 3; first by auto.
rcondt 8; first by auto; call (_ : true); auto.
rcondf 13; first by
  auto; call (_ : true); auto; call (_ : true); auto.
wp.
call (TargetNTTRefinement.target_poly_invntt_correct18 p1).
wp.
call (TargetNTTRefinement.target_poly_invntt_correct18 p0).
wp.
skip.
move=> &hr [-> [hcount [hp0 hp1]]].
have hbound0 :
    0 <= 0 /\
    0 + KeygenM23MatrixSpec.poly_words_i <=
      KeygenM23MatrixSpec.array_words_i
  by rewrite /KeygenM23MatrixSpec.poly_words_i
             /KeygenM23MatrixSpec.array_words_i
             /BArray8192.size /=.
have hbound1 :
    0 <= KeygenM23MatrixSpec.poly_words_i /\
    KeygenM23MatrixSpec.poly_words_i +
      KeygenM23MatrixSpec.poly_words_i <=
        KeygenM23MatrixSpec.array_words_i
  by rewrite /KeygenM23MatrixSpec.poly_words_i
             /KeygenM23MatrixSpec.array_words_i
             /BArray8192.size /=.
have hrepr0 :
    NTT_Fq.poly_repr_bound (poly_slice xp0 0) p0 18.
+ have hbridge0 :
      (KeygenM23ArithmeticSpec.wide_slice_repr_bound xp0 0 p0 18 <=>
       NTT_Fq.poly_repr_bound (poly_slice xp0 0) p0 18).
  + apply wide_slice_poly_repr_bound.
    exact hbound0.
  rewrite -hbridge0.
  exact hp0.
have hrepr1 :
    NTT_Fq.poly_repr_bound
      (poly_slice xp0 KeygenM23MatrixSpec.poly_words_i)
      p1 18.
+ have hbridge1 :
      (KeygenM23ArithmeticSpec.wide_slice_repr_bound
         xp0 KeygenM23MatrixSpec.poly_words_i p1 18 <=>
       NTT_Fq.poly_repr_bound
         (poly_slice xp0 KeygenM23MatrixSpec.poly_words_i) p1 18).
  + apply wide_slice_poly_repr_bound.
    exact hbound1.
  rewrite -hbridge1.
  exact hp1.
have hbase1 :
    W64.to_uint (W64.zero + W64.of_int 256) =
      KeygenM23MatrixSpec.poly_words_i
  by rewrite W64.to_uintD_small 1:/#
             W64.to_uint0 W64.of_uintK
             /KeygenM23MatrixSpec.poly_words_i /=.
split.
+ exact hrepr0.
move=> _ r0 hr0.
have hslice1 :
    poly_slice (put_poly_slice xp0 0 r0)
      KeygenM23MatrixSpec.poly_words_i =
    poly_slice xp0 KeygenM23MatrixSpec.poly_words_i by
  apply poly_slice_put_other;
    [ exact hbound0
    | exact hbound1
    | right; rewrite /KeygenM23MatrixSpec.poly_words_i /= ].
simplify.
rewrite /KeygenM23MatrixSpec.poly_words_i in hslice1.
rewrite hslice1.
split.
+ exact hrepr1.
move=> _ r1 hr1.
have hsame0 :
    poly_slice (put_poly_slice xp0 0 r0) 0 = r0 by
  apply poly_slice_put_same; exact hbound0.
have hother0 :
    poly_slice
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1) 0 =
    poly_slice (put_poly_slice xp0 0 r0) 0 by
  apply poly_slice_put_other;
    [ exact hbound1
    | exact hbound0
    | left; rewrite /KeygenM23MatrixSpec.poly_words_i /= ].
have hsame1 :
    poly_slice
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      KeygenM23MatrixSpec.poly_words_i = r1 by
  apply poly_slice_put_same; exact hbound1.
have hrpost0 :
    NTT_Fq.poly_repr_bound
      (poly_slice
        (put_poly_slice
          (put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1) 0)
      (NTT_Fq.array256_mont
        (NTTFullSpec.full_invntt p0)) 16 by
  rewrite hother0 hsame0.
have hrpost1 :
    NTT_Fq.poly_repr_bound
      (poly_slice
        (put_poly_slice
          (put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        KeygenM23MatrixSpec.poly_words_i)
      (NTT_Fq.array256_mont
        (NTTFullSpec.full_invntt p1)) 16 by
  rewrite hsame1.
have hbridge0 :
    (KeygenM23ArithmeticSpec.wide_slice_repr_bound
       (put_poly_slice
         (put_poly_slice xp0 0 r0)
         KeygenM23MatrixSpec.poly_words_i r1)
       0
       (NTT_Fq.array256_mont
         (NTTFullSpec.full_invntt p0)) 16 <=>
     NTT_Fq.poly_repr_bound
       (poly_slice
         (put_poly_slice
           (put_poly_slice xp0 0 r0)
           KeygenM23MatrixSpec.poly_words_i r1) 0)
       (NTT_Fq.array256_mont
         (NTTFullSpec.full_invntt p0)) 16) by
  apply wide_slice_poly_repr_bound; exact hbound0.
have hpost0 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      0
      (NTT_Fq.array256_mont
        (NTTFullSpec.full_invntt p0)) 16 by
  rewrite hbridge0; exact hrpost0.
have hbridge1 :
    (KeygenM23ArithmeticSpec.wide_slice_repr_bound
       (put_poly_slice
         (put_poly_slice xp0 0 r0)
         KeygenM23MatrixSpec.poly_words_i r1)
       KeygenM23MatrixSpec.poly_words_i
       (NTT_Fq.array256_mont
         (NTTFullSpec.full_invntt p1)) 16 <=>
     NTT_Fq.poly_repr_bound
       (poly_slice
         (put_poly_slice
           (put_poly_slice xp0 0 r0)
           KeygenM23MatrixSpec.poly_words_i r1)
         KeygenM23MatrixSpec.poly_words_i)
       (NTT_Fq.array256_mont
         (NTTFullSpec.full_invntt p1)) 16) by
  apply wide_slice_poly_repr_bound; exact hbound1.
have hpost1 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      KeygenM23MatrixSpec.poly_words_i
      (NTT_Fq.array256_mont
        (NTTFullSpec.full_invntt p1)) 16 by
  rewrite hbridge1; exact hrpost1.
have htail0 :=
  KeygenM23MatrixSpec.word_tail_frame_refl
    xp0 KeygenM23MatrixSpec.mode2_b_words_i.
have htail1 :
    KeygenM23MatrixSpec.word_tail_frame xp0
      (put_poly_slice xp0 0 r0)
      KeygenM23MatrixSpec.mode2_b_words_i by
  apply
    (word_tail_frame_put_before
      xp0 xp0 0 KeygenM23MatrixSpec.mode2_b_words_i r0);
    [ rewrite /KeygenM23MatrixSpec.mode2_b_words_i
              /KeygenM23MatrixSpec.mode2_rows_i
              /KeygenM23MatrixSpec.poly_words_i /=
    | rewrite /KeygenM23MatrixSpec.mode2_b_words_i
              /KeygenM23MatrixSpec.mode2_rows_i
              /KeygenM23MatrixSpec.poly_words_i
              /KeygenM23MatrixSpec.array_words_i
              /BArray8192.size /=
    | exact htail0 ].
have htail2 :
    KeygenM23MatrixSpec.word_tail_frame xp0
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      KeygenM23MatrixSpec.mode2_b_words_i by
  apply
    (word_tail_frame_put_before
      xp0 (put_poly_slice xp0 0 r0)
      KeygenM23MatrixSpec.poly_words_i
      KeygenM23MatrixSpec.mode2_b_words_i r1);
    [ rewrite /KeygenM23MatrixSpec.mode2_b_words_i
              /KeygenM23MatrixSpec.mode2_rows_i
              /KeygenM23MatrixSpec.poly_words_i /=
    | rewrite /KeygenM23MatrixSpec.mode2_b_words_i
              /KeygenM23MatrixSpec.mode2_rows_i
              /KeygenM23MatrixSpec.poly_words_i
              /KeygenM23MatrixSpec.array_words_i
              /BArray8192.size /=
    | exact htail1 ].
split; first exact hpost0.
split; first exact hpost1.
exact htail2.
qed.

lemma polyvec_invntt_mode2_correct18
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Parent._polyvec_invntt :
    xp = xp0 /\
    count = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      xp0 0 p0 18 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      xp0 KeygenM23MatrixSpec.poly_words_i p1 18
    ==>
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res 0
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt p0)) 16 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res KeygenM23MatrixSpec.poly_words_i
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt p1)) 16 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res KeygenM23MatrixSpec.mode2_b_words_i].
proof.
have hwide := wide_inv_spec_mode2_correct18 xp0 p0 p1.
by conseq polyvec_invntt_mode2_equiv hwide => /#.
qed.

lemma polyvec_invntt_mode2_pointwise_correct18
    (xp0 : BArray8192.t)
    (m : BArray32768.t)
    (v : BArray8192.t) :
  hoare [Parent._polyvec_invntt :
    xp = xp0 /\
    count = W64.of_int KeygenM23MatrixSpec.mode2_rows_i /\
    KeygenM23ArithmeticSpec.mode2_pointwise_repr_bound18
      xp0 m v
    ==>
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res 0
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt
            (KeygenM23ArithmeticSpec.pointwise_row_words
              m v 0))) 16 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res KeygenM23MatrixSpec.poly_words_i
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt
            (KeygenM23ArithmeticSpec.pointwise_row_words
              m v 1))) 16 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res KeygenM23MatrixSpec.mode2_b_words_i].
proof.
have h :=
  polyvec_invntt_mode2_correct18 xp0
    (KeygenM23ArithmeticSpec.pointwise_row_words m v 0)
    (KeygenM23ArithmeticSpec.pointwise_row_words m v 1).
by conseq h => /#;
  rewrite /KeygenM23ArithmeticSpec.mode2_pointwise_repr_bound18.
qed.

end TargetKeygenM23WideInvNTT.
