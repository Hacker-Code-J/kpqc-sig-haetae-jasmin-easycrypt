require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import TargetKeygenM23WideSupport
               KeygenM23MatrixSpec
               KeygenM23ArithmeticSpec
               NTT_Fq NTTFullSpec TargetNTTRefinement.

theory TargetKeygenM23WideNTT.

module Parent = TargetKeygenM23WideSupport.Parent.
module Single = TargetKeygenM23WideSupport.Single.
import TargetKeygenM23WideSupport.

module WideSpec = {
  proc _polyvec_ntt
      (xp : BArray8192.t, count : W64.t) : BArray8192.t = {
    var poly : W64.t;
    var base : W64.t;
    var rp : BArray1024.t;

    poly <- W64.zero;
    base <- W64.zero;
    while (poly \ult count) {
      rp <- poly_slice xp (W64.to_uint base);
      rp <@ Single._poly_ntt(rp);
      xp <- put_poly_slice xp (W64.to_uint base) rp;
      base <- base + W64.of_int 256;
      poly <- poly + W64.one;
    }
    return xp;
  }
}.

lemma polyvec_ntt_mode2_equiv :
  equiv [Parent._polyvec_ntt ~ WideSpec._polyvec_ntt :
    ={xp, count} /\
    count{1} =
      W64.of_int KeygenM23MatrixSpec.mode2_cols_i
    ==> ={res}].
proof.
proc.
while
  (={xp, poly, base, count} /\
   count{1} =
     W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
   W64.to_uint poly{1} <=
     KeygenM23MatrixSpec.mode2_cols_i /\
   W64.to_uint base{1} =
     KeygenM23MatrixSpec.poly_words_i *
       W64.to_uint poly{1} /\
   0 <= W64.to_uint base{1} /\
   W64.to_uint base{1} +
     KeygenM23MatrixSpec.poly_words_i <=
       KeygenM23MatrixSpec.array_words_i /\
   zetasp{1} = HpolyTarget.jzetas).
+ inline Single._poly_ntt.
  seq 2 6 :
    (={poly, base, count, zetasp} /\
     zetasp{1} = HpolyTarget.jzetas /\
     count{1} =
       W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
     W64.to_uint poly{1} <
       KeygenM23MatrixSpec.mode2_cols_i /\
     W64.to_uint base{1} =
       KeygenM23MatrixSpec.poly_words_i *
         W64.to_uint poly{1} /\
     0 <= W64.to_uint base{1} /\
     W64.to_uint base{1} +
       KeygenM23MatrixSpec.poly_words_i <=
         KeygenM23MatrixSpec.array_words_i /\
     W64.to_uint zetasctr{1} = zetasctr{2} /\
     W64.to_uint len{1} = len{2} /\
     KeygenM23MatrixSpec.m23_fwd_len_schedule len{2} /\
     2 * (zetasctr{2} + 1) * len{2} = 256 /\
     poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
     poly_slice_frame xp{2} xp{1} (W64.to_uint base{1})).
  + wp.
    skip => /> &2 hpolyle hbaseeq hbase0 hbasecap hguard.
    move: hguard.
    rewrite W64.ultE W64.of_uintK
            /KeygenM23MatrixSpec.mode2_cols_i /=.
    trivial.
  seq 1 1 :
    (={poly, base, count, zetasp} /\
     zetasp{1} = HpolyTarget.jzetas /\
     count{1} =
       W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
     W64.to_uint poly{1} <
       KeygenM23MatrixSpec.mode2_cols_i /\
     W64.to_uint base{1} =
       KeygenM23MatrixSpec.poly_words_i *
         W64.to_uint poly{1} /\
     0 <= W64.to_uint base{1} /\
     W64.to_uint base{1} +
       KeygenM23MatrixSpec.poly_words_i <=
         KeygenM23MatrixSpec.array_words_i /\
     W64.to_uint zetasctr{1} = zetasctr{2} /\
     W64.to_uint len{1} = len{2} /\
     KeygenM23MatrixSpec.m23_fwd_len_schedule len{2} /\
     (len{2} = 0 \/
      2 * (zetasctr{2} + 1) * len{2} = 256) /\
     poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
     poly_slice_frame xp{2} xp{1} (W64.to_uint base{1})).
  + while
      (={poly, base, count, zetasp} /\
       zetasp{1} = HpolyTarget.jzetas /\
       count{1} =
         W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
       W64.to_uint poly{1} <
         KeygenM23MatrixSpec.mode2_cols_i /\
       W64.to_uint base{1} =
         KeygenM23MatrixSpec.poly_words_i *
           W64.to_uint poly{1} /\
       0 <= W64.to_uint base{1} /\
       W64.to_uint base{1} +
         KeygenM23MatrixSpec.poly_words_i <=
           KeygenM23MatrixSpec.array_words_i /\
       W64.to_uint zetasctr{1} = zetasctr{2} /\
       W64.to_uint len{1} = len{2} /\
       KeygenM23MatrixSpec.m23_fwd_len_schedule len{2} /\
       (len{2} = 0 \/
        2 * (zetasctr{2} + 1) * len{2} = 256) /\
       poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
       poly_slice_frame xp{2} xp{1} (W64.to_uint base{1})).
    + wp.
      while
        (={poly, base, count, zetasp} /\
         zetasp{1} = HpolyTarget.jzetas /\
         count{1} =
           W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
         W64.to_uint poly{1} <
           KeygenM23MatrixSpec.mode2_cols_i /\
         W64.to_uint base{1} =
           KeygenM23MatrixSpec.poly_words_i *
             W64.to_uint poly{1} /\
         0 <= W64.to_uint base{1} /\
         W64.to_uint base{1} +
           KeygenM23MatrixSpec.poly_words_i <=
             KeygenM23MatrixSpec.array_words_i /\
         W64.to_uint zetasctr{1} = zetasctr{2} /\
         W64.to_uint len{1} = len{2} /\
         KeygenM23MatrixSpec.m23_fwd_len_schedule len{2} /\
         0 < len{2} /\
         W64.to_uint start{1} = start{2} /\
         0 <= start{2} <= 256 /\
         KeygenM23MatrixSpec.m23_fwd_block_start
           len{2} start{2} /\
         2 * (zetasctr{2} + 1) * len{2} =
           256 + start{2} /\
         poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
         poly_slice_frame xp{2} xp{1} (W64.to_uint base{1})).
      + wp.
        while
          (={poly, base, count, zetasp, zeta_0} /\
           zetasp{1} = HpolyTarget.jzetas /\
           count{1} =
             W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
           W64.to_uint poly{1} <
             KeygenM23MatrixSpec.mode2_cols_i /\
           W64.to_uint base{1} =
             KeygenM23MatrixSpec.poly_words_i *
               W64.to_uint poly{1} /\
           0 <= W64.to_uint base{1} /\
           W64.to_uint base{1} +
             KeygenM23MatrixSpec.poly_words_i <=
               KeygenM23MatrixSpec.array_words_i /\
           W64.to_uint zetasctr{1} = zetasctr{2} /\
           W64.to_uint len{1} = len{2} /\
           KeygenM23MatrixSpec.m23_fwd_len_schedule len{2} /\
           0 < len{2} /\
           W64.to_uint start{1} = start{2} /\
           0 <= start{2} < 256 /\
           KeygenM23MatrixSpec.m23_fwd_block_start
             len{2} start{2} /\
           start{2} + 2 * len{2} <= 256 /\
           2 * zetasctr{2} * len{2} =
             256 + start{2} /\
           W64.to_uint cmp{1} = cmp{2} /\
           cmp{2} = start{2} + len{2} /\
           W64.to_uint j{1} = j{2} /\
           start{2} <= j{2} <= cmp{2} /\
           poly_slice xp{1} (W64.to_uint base{1}) = rp0{2} /\
           poly_slice_frame xp{2} xp{1} (W64.to_uint base{1})).
        + wp.
          call parent_single_fqmul_equiv.
          wp.
          skip => /> &1 &2 hpoly hbase hbase0 hbasecap
                      hsched hlen hstart0 hstart256 hblock hcap
                      hz hcmp hjlo hjhi hframe hguard.
          have hjlt : W64.to_uint j{1} < W64.to_uint cmp{1}.
          + move: hguard.
            rewrite W64.ultE.
            trivial.
          have hj256 : W64.to_uint j{1} < 256 by smt().
          have hjlen256 :
              W64.to_uint j{1} + W64.to_uint len{1} < 256 by smt().
          have hbase_bound :
              0 <= W64.to_uint base{2} /\
              W64.to_uint base{2} +
                KeygenM23MatrixSpec.poly_words_i <=
                  KeygenM23MatrixSpec.array_words_i.
          + split.
            * exact hbase0.
            * move: hpoly hbase.
              rewrite /KeygenM23MatrixSpec.mode2_cols_i
                      /KeygenM23MatrixSpec.poly_words_i
                      /KeygenM23MatrixSpec.array_words_i.
              smt().
          have hbase_words :
              W64.to_uint base{2} + 256 <= 2048.
          + move: hpoly hbase.
            rewrite /KeygenM23MatrixSpec.mode2_cols_i
                    /KeygenM23MatrixSpec.poly_words_i.
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
          have hbasej :
              W64.to_uint (base{2} + j{1}) =
                W64.to_uint base{2} + W64.to_uint j{1}.
          + rewrite W64.to_uintD_small 1:/#.
            trivial.
          have hbasejlen :
              W64.to_uint (base{2} + (j{1} + len{1})) =
                W64.to_uint base{2} + W64.to_uint j{1} +
                  W64.to_uint len{1}.
          + rewrite W64.to_uintD_small 1:/# hjlen.
            ring.
          have hcoeff :
              BArray8192.get32 xp{1}
                (W64.to_uint (base{2} + (j{1} + len{1}))) =
              BArray1024.get32
                (poly_slice xp{1} (W64.to_uint base{2}))
                (W64.to_uint j{1} + W64.to_uint len{1}).
          + rewrite hbasejlen.
            rewrite poly_slice_get32 1:hbase_bound 1:/#.
            trivial.
          have hslice_set :
              poly_slice
                (BArray8192.set32
                  (BArray8192.set32 xp{1}
                    (W64.to_uint
                      (base{2} + (j{1} + len{1})))
                    (BArray8192.get32 xp{1}
                       (W64.to_uint (base{2} + j{1})) -
                     t{2}))
                  (W64.to_uint (base{2} + j{1}))
                  (BArray8192.get32 xp{1}
                     (W64.to_uint (base{2} + j{1})) +
                   t{2}))
                (W64.to_uint base{2}) =
              BArray1024.set32
                (BArray1024.set32
                  (poly_slice xp{1} (W64.to_uint base{2}))
                  (W64.to_uint j{1} + W64.to_uint len{1})
                  (BArray1024.get32
                     (poly_slice xp{1} (W64.to_uint base{2}))
                     (W64.to_uint j{1}) - t{2}))
                (W64.to_uint j{1})
                (BArray1024.get32
                   (poly_slice xp{1} (W64.to_uint base{2}))
                   (W64.to_uint j{1}) + t{2}).
          + rewrite hbasejlen hbasej.
            rewrite poly_slice_set32 1:hbase_bound 1:/#.
            rewrite poly_slice_get32 1:hbase_bound 1:/#.
            trivial.
          have hframe2 :
              poly_slice_frame xp{2}
                (BArray8192.set32
                  (BArray8192.set32 xp{1}
                    (W64.to_uint
                      (base{2} + (j{1} + len{1})))
                    (BArray8192.get32 xp{1}
                       (W64.to_uint (base{2} + j{1})) - t{2}))
                  (W64.to_uint (base{2} + j{1}))
                  (BArray8192.get32 xp{1}
                     (W64.to_uint (base{2} + j{1})) + t{2}))
                (W64.to_uint base{2}).
          + rewrite /poly_slice_frame in hframe.
            rewrite /poly_slice_frame.
            move=> x hx hout.
            have hidx1 :
                W64.to_uint base{2} <=
                  W64.to_uint (base{2} + j{1}) <
                W64.to_uint base{2} + 256.
            * rewrite hbasej.
              smt().
            have hidx2 :
                W64.to_uint base{2} <=
                  W64.to_uint (base{2} + (j{1} + len{1})) <
                W64.to_uint base{2} + 256.
            * rewrite hbasejlen.
              smt().
            rewrite !BArray8192.get_set32E 1:/# 1:/#.
            have houtside := hframe x hx hout.
            smt().
          smt().
        smt().
        have hidxassoc :
            W64.to_uint base{2} + W64.to_uint j{1} +
              W64.to_uint len{1} =
            W64.to_uint base{2} +
              (W64.to_uint j{1} + W64.to_uint len{1}) by ring.
        rewrite hidxassoc.
        rewrite poly_slice_set32 1:hbase_bound 1:/#.
        trivial.
        congr; ring.
        move=> _.
        split.
        + exact hcoeff.
        move=> _ result_R.
        have hslice_result :
            poly_slice
              (BArray8192.set32
                (BArray8192.set32 xp{1}
                  (W64.to_uint (base{2} + (j{1} + len{1})))
                  (BArray8192.get32 xp{1}
                     (W64.to_uint (base{2} + j{1})) -
                   result_R))
                (W64.to_uint (base{2} + j{1}))
                (BArray8192.get32 xp{1}
                   (W64.to_uint (base{2} + j{1})) +
                 result_R))
              (W64.to_uint base{2}) =
            BArray1024.set32
              (BArray1024.set32
                (poly_slice xp{1} (W64.to_uint base{2}))
                (W64.to_uint j{1} + W64.to_uint len{1})
                (BArray1024.get32
                   (poly_slice xp{1} (W64.to_uint base{2}))
                   (W64.to_uint j{1}) - result_R))
              (W64.to_uint j{1})
              (BArray1024.get32
                 (poly_slice xp{1} (W64.to_uint base{2}))
                 (W64.to_uint j{1}) + result_R).
        + rewrite hbasejlen hbasej.
          have hidxassoc :
              W64.to_uint base{2} + W64.to_uint j{1} +
                W64.to_uint len{1} =
              W64.to_uint base{2} +
                (W64.to_uint j{1} + W64.to_uint len{1}) by ring.
          rewrite hidxassoc.
          rewrite poly_slice_set32 1:hbase_bound 1:/#.
          rewrite poly_slice_get32 1:hbase_bound 1:/#.
          trivial.
        have hframe_result :
            poly_slice_frame xp{2}
              (BArray8192.set32
                (BArray8192.set32 xp{1}
                  (W64.to_uint (base{2} + (j{1} + len{1})))
                  (BArray8192.get32 xp{1}
                     (W64.to_uint (base{2} + j{1})) -
                   result_R))
                (W64.to_uint (base{2} + j{1}))
                (BArray8192.get32 xp{1}
                   (W64.to_uint (base{2} + j{1})) +
                 result_R))
              (W64.to_uint base{2}).
        + have hframe_first :
              poly_slice_frame xp{2}
                (BArray8192.set32 xp{1}
                  (W64.to_uint base{2} +
                   (W64.to_uint j{1} + W64.to_uint len{1}))
                  (BArray8192.get32 xp{1}
                     (W64.to_uint base{2} + W64.to_uint j{1}) -
                   result_R))
                (W64.to_uint base{2}).
          * apply poly_slice_frame_set32.
            + exact hbase_bound.
            + smt().
            + exact hframe.
          have hframe_second :
              poly_slice_frame xp{2}
                (BArray8192.set32
                  (BArray8192.set32 xp{1}
                    (W64.to_uint base{2} +
                     (W64.to_uint j{1} + W64.to_uint len{1}))
                    (BArray8192.get32 xp{1}
                       (W64.to_uint base{2} + W64.to_uint j{1}) -
                     result_R))
                  (W64.to_uint base{2} + W64.to_uint j{1})
                  (BArray8192.get32 xp{1}
                     (W64.to_uint base{2} + W64.to_uint j{1}) +
                   result_R))
                (W64.to_uint base{2}).
          * apply poly_slice_frame_set32.
            + exact hbase_bound.
            + smt().
            + exact hframe_first.
          rewrite hbasejlen hbasej hidxassoc.
          exact hframe_second.
        rewrite poly_slice_set32 1:hbase_bound 1:/#.
        trivial.
        have hframe_result2 :
            poly_slice_frame xp{2}
              (BArray8192.set32
                (BArray8192.set32 xp{1}
                  (W64.to_uint (base{2} + (j{1} + len{1})))
                  (BArray8192.get32 xp{1}
                     (W64.to_uint (base{2} + j{1})) -
                   result_R))
                (W64.to_uint (base{2} + j{1}))
                (BArray8192.get32 xp{1}
                   (W64.to_uint (base{2} + j{1})) +
                 result_R))
              (W64.to_uint base{2}).
        + have hidxassoc2 :
              W64.to_uint base{2} + W64.to_uint j{1} +
                W64.to_uint len{1} =
              W64.to_uint base{2} +
                (W64.to_uint j{1} + W64.to_uint len{1}) by ring.
          rewrite hbasejlen hbasej hidxassoc2.
          apply poly_slice_frame_set32.
          * exact hbase_bound.
          * smt().
          * apply poly_slice_frame_set32.
            + exact hbase_bound.
            + smt().
            + exact hframe.
        rewrite hj1 hslice_result hframe_result2 !W64.ultE.
        smt().
      wp.
      skip => />.
      move=> &1 &2 hpoly hbase hbase0 hbasecap
              hsched hlen hstart0 hstartle hblock hz hframe
              hguardL hguardR.
      have hstartlt : W64.to_uint start{1} < 256.
      + exact hguardR.
      have hcap :=
        KeygenM23MatrixSpec.m23_fwd_block_active_bound
          (W64.to_uint len{1}) (W64.to_uint start{1})
          hsched hlen hblock hstartlt.
      rewrite /KeygenM23MatrixSpec.poly_words_i in hcap.
      have hzlt :
          W64.to_uint zetasctr{1} < 256.
      + have hsched' := hsched.
        move: hsched'.
        rewrite /KeygenM23MatrixSpec.m23_fwd_len_schedule.
        smt().
      have hz1 :
          W64.to_uint (zetasctr{1} + W64.one) =
            W64.to_uint zetasctr{1} + 1.
      + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
        trivial.
      have hstartlen :
          W64.to_uint (start{1} + len{1}) =
            W64.to_uint start{1} + W64.to_uint len{1}.
      + rewrite W64.to_uintD_small 1:/#.
        trivial.
      split.
      + rewrite hz1 hstartlen !W64.ultE /=.
        smt().
      move=> jL xpL hdoneL hdoneR _ _ _ _ hjlo hjhi hframeL.
      rewrite W64.ultE in hdoneL.
      have hj_eq :
          W64.to_uint jL =
            W64.to_uint start{1} + W64.to_uint len{1}
        by smt().
      have hjlen :
          W64.to_uint (jL + len{1}) =
            W64.to_uint jL + W64.to_uint len{1}.
      + rewrite W64.to_uintD_small 1:/#.
        trivial.
      have hnewstart :
          W64.to_uint jL + W64.to_uint len{1} =
            W64.to_uint start{1} + 2 * W64.to_uint len{1}
        by smt().
      have hblock' :=
        KeygenM23MatrixSpec.m23_fwd_block_start_step
          (W64.to_uint len{1}) (W64.to_uint start{1})
          hsched hlen hblock hstartlt.
      rewrite hjlen hnewstart !W64.ultE W64.of_uintK 1:/# /=.
    wp.
    skip => />.
    move=> &1 &2 hpoly hbase hbase0 hbasecap
            hsched hstage hframe hguardL hlen.
    split.
    + split.
      + exact
          (KeygenM23MatrixSpec.m23_fwd_block_start_zero
             (W64.to_uint len{1}) hsched hlen).
      + smt().
    move=> startL xpL zetasctrL hdoneL hdoneR
            hstart0 hstartle hblock hstage_exit hframeL.
    have hstart_eq : W64.to_uint startL = 256 by smt().
    have hshiftW :
        W64.to_uint (len{1} `>>` W8.one) =
          W64.to_uint len{1} %/ 2.
    + by rewrite W64.shr_div_le 1:/# /=.
    have hshiftI :
        W64.to_uint len{1} `|>>` 1 =
          W64.to_uint len{1} %/ 2.
    + apply int_shr1_div2.
      smt(W64.to_uint_cmp).
    have hstage' :
        W64.to_uint len{1} %/ 2 = 0 \/
        2 * (W64.to_uint zetasctrL + 1) *
          (W64.to_uint len{1} %/ 2) = 256.
    + have hsched' := hsched.
      move: hsched' hstage_exit.
      rewrite /KeygenM23MatrixSpec.m23_fwd_len_schedule.
      by move=> [->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]];
         smt().
    split.
    + split.
      + by rewrite hshiftW hshiftI.
      split.
      + rewrite hshiftI.
        exact
          (KeygenM23MatrixSpec.m23_fwd_len_schedule_shr1
             (W64.to_uint len{1}) hsched).
      + by rewrite hshiftI.
    rewrite !W64.ultE W64.to_uint0 hshiftW hshiftI.
    trivial.
  skip => />.
  move=> &1 &2 hpoly hbase hbase0 hbasecap
          hsched hstage hframe.
  rewrite W64.ultE W64.to_uint0.
  trivial.
wp.
skip => /> &1 &2 hpoly hbase hbase0 hbasecap
            hsched hstage hframe.
have hreassemble :
    xp{1} =
      put_poly_slice xp{2} (W64.to_uint base{2})
        (poly_slice xp{1} (W64.to_uint base{2})).
+ apply poly_slice_reassemble.
  + smt().
  + trivial.
  + exact hframe.
have hpolysucc :
    W64.to_uint (poly{2} + W64.one) =
      W64.to_uint poly{2} + 1.
+ rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  trivial.
have hbasesucc :
    W64.to_uint (base{2} + W64.of_int 256) =
      W64.to_uint base{2} + 256.
+ rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
  trivial.
have hslice_put :
    poly_slice
      (put_poly_slice xp{2} (W64.to_uint base{2})
        (poly_slice xp{1} (W64.to_uint base{2})))
      (W64.to_uint base{2}) =
    poly_slice xp{1} (W64.to_uint base{2}).
+ apply poly_slice_put_same.
  smt().
rewrite hreassemble hpolysucc hbasesucc
        hslice_put /KeygenM23MatrixSpec.poly_words_i.
smt().
auto => />.
qed.

lemma wide_spec_mode2_correct
    (xp0 : BArray8192.t) (p0 p1 p2 : Rq.poly) :
  hoare [WideSpec._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
    KeygenM23ArithmeticSpec.mode2_input_repr_bound16
      xp0 p0 p1 p2
    ==>
    KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
      res p0 p1 p2 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res KeygenM23MatrixSpec.mode2_s1_words_i].
proof.
proc.
rcondt 3; first by auto.
rcondt 8; first by auto; call (_ : true); auto.
rcondt 13; first by
  auto; call (_ : true); auto; call (_ : true); auto.
rcondf 18; first by
  auto; call (_ : true); auto; call (_ : true); auto;
  call (_ : true); auto.
wp.
call (TargetNTTRefinement.target_poly_ntt_correct p2).
wp.
call (TargetNTTRefinement.target_poly_ntt_correct p1).
wp.
call (TargetNTTRefinement.target_poly_ntt_correct p0).
wp.
skip.
move=> &hr [-> [hcount hin]].
move: hin.
rewrite /KeygenM23ArithmeticSpec.mode2_input_repr_bound16.
move=> [hin0 [hin1 hin2]].
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
have hbound2 :
    0 <= 2 * KeygenM23MatrixSpec.poly_words_i /\
    2 * KeygenM23MatrixSpec.poly_words_i +
      KeygenM23MatrixSpec.poly_words_i <=
      KeygenM23MatrixSpec.array_words_i by
  rewrite /KeygenM23MatrixSpec.poly_words_i
          /KeygenM23MatrixSpec.array_words_i
          /BArray8192.size /=.
have hbound256 :
    0 <= 256 /\
    256 + KeygenM23MatrixSpec.poly_words_i <=
      KeygenM23MatrixSpec.array_words_i by
  rewrite /KeygenM23MatrixSpec.poly_words_i
          /KeygenM23MatrixSpec.array_words_i
          /BArray8192.size /=.
have hbound512 :
    0 <= 512 /\
    512 + KeygenM23MatrixSpec.poly_words_i <=
      KeygenM23MatrixSpec.array_words_i by
  rewrite /KeygenM23MatrixSpec.poly_words_i
          /KeygenM23MatrixSpec.array_words_i
          /BArray8192.size /=.
have hrepr0 :
    NTT_Fq.poly_repr_bound (poly_slice xp0 0) p0 16.
+ have hbridge :
      (KeygenM23ArithmeticSpec.wide_slice_repr_bound
         xp0 0 p0 16 <=>
       NTT_Fq.poly_repr_bound (poly_slice xp0 0) p0 16).
  + apply wide_slice_poly_repr_bound.
    exact hbound0.
  move: hin0.
  by rewrite hbridge.
have hrepr1 :
    NTT_Fq.poly_repr_bound
      (poly_slice xp0 KeygenM23MatrixSpec.poly_words_i)
      p1 16.
+ have hbridge :
      (KeygenM23ArithmeticSpec.wide_slice_repr_bound
         xp0 KeygenM23MatrixSpec.poly_words_i p1 16 <=>
       NTT_Fq.poly_repr_bound
         (poly_slice xp0 KeygenM23MatrixSpec.poly_words_i)
         p1 16).
  + apply wide_slice_poly_repr_bound.
    exact hbound1.
  move: hin1.
  by rewrite hbridge.
have hrepr2 :
    NTT_Fq.poly_repr_bound
      (poly_slice xp0
        (2 * KeygenM23MatrixSpec.poly_words_i))
      p2 16.
+ have hbridge :
      (KeygenM23ArithmeticSpec.wide_slice_repr_bound
         xp0 (2 * KeygenM23MatrixSpec.poly_words_i)
         p2 16 <=>
       NTT_Fq.poly_repr_bound
         (poly_slice xp0
           (2 * KeygenM23MatrixSpec.poly_words_i))
         p2 16).
  + apply wide_slice_poly_repr_bound.
    exact hbound2.
  move: hin2.
  by rewrite hbridge.
have hrepr1_256 :
    NTT_Fq.poly_repr_bound (poly_slice xp0 256) p1 16.
+ move: hrepr1.
  by rewrite /KeygenM23MatrixSpec.poly_words_i.
have hrepr2_512 :
    NTT_Fq.poly_repr_bound (poly_slice xp0 512) p2 16.
+ move: hrepr2.
  by rewrite /KeygenM23MatrixSpec.poly_words_i.
have hbase1 :
    W64.to_uint (W64.zero + W64.of_int 256) =
      KeygenM23MatrixSpec.poly_words_i by
  rewrite W64.to_uintD_small 1:/#
          W64.to_uint0 W64.of_uintK
          /KeygenM23MatrixSpec.poly_words_i /=.
have hbase2 :
    W64.to_uint
      (W64.zero + W64.of_int 256 + W64.of_int 256) =
      2 * KeygenM23MatrixSpec.poly_words_i by
  rewrite W64.to_uintD_small 1:/#
          W64.to_uintD_small 1:/#
          W64.to_uint0 W64.of_uintK
          /KeygenM23MatrixSpec.poly_words_i /=.
split.
+ exact hrepr0.
move=> _ r0 hr0.
have hslice1 :
    poly_slice (put_poly_slice xp0 0 r0)
      256 =
    poly_slice xp0 256.
+ apply poly_slice_put_other.
  + exact hbound0.
  + exact hbound256.
  + right.
    smt().
split.
+ rewrite hslice1.
  exact hrepr1_256.
move=> _ r1 hr1.
have hslice20 :
    poly_slice (put_poly_slice xp0 0 r0)
      512 =
    poly_slice xp0 512.
+ apply poly_slice_put_other.
  + exact hbound0.
  + exact hbound512.
  + right.
    smt().
have hslice21 :
    poly_slice
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        256 r1)
      512 =
    poly_slice (put_poly_slice xp0 0 r0)
      512.
+ apply poly_slice_put_other.
  + exact hbound256.
  + exact hbound512.
  + right.
    smt().
split.
+ rewrite hslice21 hslice20.
  exact hrepr2_512.
move=> _ r2 hr2.
have hsame0 :
    poly_slice (put_poly_slice xp0 0 r0) 0 = r0.
+ apply poly_slice_put_same.
  exact hbound0.
have hother10 :
    poly_slice
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1) 0 =
    poly_slice (put_poly_slice xp0 0 r0) 0.
+ apply poly_slice_put_other.
  + exact hbound1.
  + exact hbound0.
  + left.
    smt().
have hother20 :
    poly_slice
      (put_poly_slice
        (put_poly_slice
          (put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2) 0 =
    poly_slice
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1) 0.
+ apply poly_slice_put_other.
  + exact hbound2.
  + exact hbound0.
  + left.
    smt().
have hsame1 :
    poly_slice
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      KeygenM23MatrixSpec.poly_words_i = r1.
+ apply poly_slice_put_same.
  exact hbound1.
have hother21 :
    poly_slice
      (put_poly_slice
        (put_poly_slice
          (put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      KeygenM23MatrixSpec.poly_words_i =
    poly_slice
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      KeygenM23MatrixSpec.poly_words_i.
+ apply poly_slice_put_other.
  + exact hbound2.
  + exact hbound1.
  + left.
    smt().
have hsame2 :
    poly_slice
      (put_poly_slice
        (put_poly_slice
          (put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      (2 * KeygenM23MatrixSpec.poly_words_i) = r2.
+ apply poly_slice_put_same.
  exact hbound2.
have hpost0 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (put_poly_slice
        (put_poly_slice
          (put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      0 (NTTFullSpec.full_ntt p0) 24.
+ rewrite wide_slice_poly_repr_bound 1:hbound0.
  by rewrite hother20 hother10 hsame0.
have hpost1 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (put_poly_slice
        (put_poly_slice
          (put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      KeygenM23MatrixSpec.poly_words_i
      (NTTFullSpec.full_ntt p1) 24.
+ rewrite wide_slice_poly_repr_bound 1:hbound1.
  by rewrite hother21 hsame1.
have hpost2 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (put_poly_slice
        (put_poly_slice
          (put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      (2 * KeygenM23MatrixSpec.poly_words_i)
      (NTTFullSpec.full_ntt p2) 24.
+ rewrite wide_slice_poly_repr_bound 1:hbound2.
  by rewrite hsame2.
have htail0 :
    KeygenM23MatrixSpec.word_tail_frame xp0 xp0
      KeygenM23MatrixSpec.mode2_s1_words_i by
  rewrite /KeygenM23MatrixSpec.word_tail_frame.
have htail1 :
    KeygenM23MatrixSpec.word_tail_frame xp0
      (put_poly_slice xp0 0 r0)
      KeygenM23MatrixSpec.mode2_s1_words_i by
  apply
    (word_tail_frame_put_before
      xp0 xp0 0 KeygenM23MatrixSpec.mode2_s1_words_i r0);
    [ rewrite /KeygenM23MatrixSpec.mode2_s1_words_i
              /KeygenM23MatrixSpec.mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i /=
    | rewrite /KeygenM23MatrixSpec.mode2_s1_words_i
              /KeygenM23MatrixSpec.mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i
              /KeygenM23MatrixSpec.array_words_i
              /BArray8192.size /=
    | exact htail0 ].
have htail2 :
    KeygenM23MatrixSpec.word_tail_frame xp0
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      KeygenM23MatrixSpec.mode2_s1_words_i by
  apply
    (word_tail_frame_put_before
      xp0 (put_poly_slice xp0 0 r0)
      KeygenM23MatrixSpec.poly_words_i
      KeygenM23MatrixSpec.mode2_s1_words_i r1);
    [ rewrite /KeygenM23MatrixSpec.mode2_s1_words_i
              /KeygenM23MatrixSpec.mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i /=
    | rewrite /KeygenM23MatrixSpec.mode2_s1_words_i
              /KeygenM23MatrixSpec.mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i
              /KeygenM23MatrixSpec.array_words_i
              /BArray8192.size /=
    | exact htail1 ].
have htail3 :
    KeygenM23MatrixSpec.word_tail_frame xp0
      (put_poly_slice
        (put_poly_slice
          (put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      KeygenM23MatrixSpec.mode2_s1_words_i by
  apply
    (word_tail_frame_put_before
      xp0
      (put_poly_slice
        (put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      (2 * KeygenM23MatrixSpec.poly_words_i)
      KeygenM23MatrixSpec.mode2_s1_words_i r2);
    [ rewrite /KeygenM23MatrixSpec.mode2_s1_words_i
              /KeygenM23MatrixSpec.mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i /=
    | rewrite /KeygenM23MatrixSpec.mode2_s1_words_i
              /KeygenM23MatrixSpec.mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i
              /KeygenM23MatrixSpec.array_words_i
              /BArray8192.size /=
    | exact htail2 ].
simplify.
rewrite /KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24.
split.
+ split.
  + move: hpost0.
    by rewrite /KeygenM23MatrixSpec.poly_words_i /=.
  + split.
    + move: hpost1.
      by rewrite /KeygenM23MatrixSpec.poly_words_i /=.
    + move: hpost2.
      by rewrite /KeygenM23MatrixSpec.poly_words_i /=.
+ move: htail3.
  by rewrite /KeygenM23MatrixSpec.poly_words_i /=.
qed.

lemma parent_polyvec_ntt_mode2_correct
    (xp0 : BArray8192.t) (p0 p1 p2 : Rq.poly) :
  hoare [Parent._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int KeygenM23MatrixSpec.mode2_cols_i /\
    KeygenM23ArithmeticSpec.mode2_input_repr_bound16
      xp0 p0 p1 p2
    ==>
    KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
      res p0 p1 p2 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res KeygenM23MatrixSpec.mode2_s1_words_i].
proof.
have hwide := wide_spec_mode2_correct xp0 p0 p1 p2.
by conseq polyvec_ntt_mode2_equiv hwide => /#.
qed.

end TargetKeygenM23WideNTT.
