require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8192 VerifyUnpackMode2Target.
require import Array256 Fq GFq Rq.
require import NTT_Fq NTTFullSpec NTTRowProductSpec.
require import TargetNTTRefinement
               TargetKeygenM23WideNTT
               TargetKeygenM23WideSupport
               KeygenM23ArithmeticSpec
               KeygenM23MatrixSpec.

theory VerifyUnpackV3NttPostFreeze.

module Verify = VerifyUnpackMode2Target.M.
module Parent = TargetKeygenM23WideSupport.Parent.
module Wide = TargetKeygenM23WideNTT.WideSpec.
import TargetKeygenM23WideSupport.

op verify_unpack_ntt_polys : int = 2.
op verify_unpack_ntt_words : int =
  verify_unpack_ntt_polys * KeygenM23MatrixSpec.poly_words_i.

op verify_unpack_ntt_input_repr_bound16
    (s : BArray8192.t) (p0 p1 : Rq.poly) : bool =
  KeygenM23ArithmeticSpec.wide_slice_repr_bound s 0 p0 16 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s KeygenM23MatrixSpec.poly_words_i p1 16.

op verify_unpack_ntt_repr_bound24
    (s : BArray8192.t) (p0 p1 : Rq.poly) : bool =
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s 0 (NTTFullSpec.full_ntt p0) 24 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s KeygenM23MatrixSpec.poly_words_i
    (NTTFullSpec.full_ntt p1) 24.

lemma verify_unpack_polyvec_ntt_equiv_parent :
  equiv [Verify._polyvec_ntt ~ Parent._polyvec_ntt :
    ={xp, count} ==> ={res}].
proof.
proc.
sim.
qed.

lemma parent_polyvec_ntt_equiv_wide_count2 :
  equiv [Parent._polyvec_ntt ~ Wide._polyvec_ntt :
    ={xp, count} /\
    count{1} = W64.of_int verify_unpack_ntt_polys
    ==> ={res}].
proof.
proc.
while
  (={xp, poly, base, count} /\
   count{1} = W64.of_int verify_unpack_ntt_polys /\
   W64.to_uint poly{1} <= verify_unpack_ntt_polys /\
   W64.to_uint base{1} =
     KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
   0 <= W64.to_uint base{1} /\
   W64.to_uint base{1} + KeygenM23MatrixSpec.poly_words_i <=
     KeygenM23MatrixSpec.array_words_i /\
   zetasp{1} = HpolyTarget.jzetas).
+ inline TargetKeygenM23WideSupport.Single._poly_ntt.
  seq 2 6 :
    (={poly, base, count, zetasp} /\
     zetasp{1} = HpolyTarget.jzetas /\
     count{1} = W64.of_int verify_unpack_ntt_polys /\
     W64.to_uint poly{1} < verify_unpack_ntt_polys /\
     W64.to_uint base{1} =
       KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
     0 <= W64.to_uint base{1} /\
     W64.to_uint base{1} + KeygenM23MatrixSpec.poly_words_i <=
       KeygenM23MatrixSpec.array_words_i /\
     W64.to_uint zetasctr{1} = zetasctr{2} /\
     W64.to_uint len{1} = len{2} /\
     KeygenM23MatrixSpec.m23_fwd_len_schedule len{2} /\
     2 * (zetasctr{2} + 1) * len{2} = 256 /\
     TargetKeygenM23WideSupport.poly_slice xp{1}
       (W64.to_uint base{1}) = rp0{2} /\
     TargetKeygenM23WideSupport.poly_slice_frame
       xp{2} xp{1} (W64.to_uint base{1})).
  + wp.
    skip => /> &2 hpolyle hbaseeq hbase0 hbasecap hguard.
    move: hguard.
    rewrite W64.ultE W64.of_uintK /verify_unpack_ntt_polys /=.
    trivial.
  seq 1 1 :
    (={poly, base, count, zetasp} /\
     zetasp{1} = HpolyTarget.jzetas /\
     count{1} = W64.of_int verify_unpack_ntt_polys /\
     W64.to_uint poly{1} < verify_unpack_ntt_polys /\
     W64.to_uint base{1} =
       KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
     0 <= W64.to_uint base{1} /\
     W64.to_uint base{1} + KeygenM23MatrixSpec.poly_words_i <=
       KeygenM23MatrixSpec.array_words_i /\
     W64.to_uint zetasctr{1} = zetasctr{2} /\
     W64.to_uint len{1} = len{2} /\
     KeygenM23MatrixSpec.m23_fwd_len_schedule len{2} /\
     (len{2} = 0 \/ 2 * (zetasctr{2} + 1) * len{2} = 256) /\
     TargetKeygenM23WideSupport.poly_slice xp{1}
       (W64.to_uint base{1}) = rp0{2} /\
     TargetKeygenM23WideSupport.poly_slice_frame
       xp{2} xp{1} (W64.to_uint base{1})).
  + while
      (={poly, base, count, zetasp} /\
       zetasp{1} = HpolyTarget.jzetas /\
       count{1} = W64.of_int verify_unpack_ntt_polys /\
       W64.to_uint poly{1} < verify_unpack_ntt_polys /\
       W64.to_uint base{1} =
         KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
       0 <= W64.to_uint base{1} /\
       W64.to_uint base{1} + KeygenM23MatrixSpec.poly_words_i <=
         KeygenM23MatrixSpec.array_words_i /\
       W64.to_uint zetasctr{1} = zetasctr{2} /\
       W64.to_uint len{1} = len{2} /\
       KeygenM23MatrixSpec.m23_fwd_len_schedule len{2} /\
       (len{2} = 0 \/ 2 * (zetasctr{2} + 1) * len{2} = 256) /\
       TargetKeygenM23WideSupport.poly_slice xp{1}
         (W64.to_uint base{1}) = rp0{2} /\
       TargetKeygenM23WideSupport.poly_slice_frame
         xp{2} xp{1} (W64.to_uint base{1})).
    + wp.
      while
        (={poly, base, count, zetasp} /\
         zetasp{1} = HpolyTarget.jzetas /\
         count{1} = W64.of_int verify_unpack_ntt_polys /\
         W64.to_uint poly{1} < verify_unpack_ntt_polys /\
         W64.to_uint base{1} =
           KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
         0 <= W64.to_uint base{1} /\
         W64.to_uint base{1} + KeygenM23MatrixSpec.poly_words_i <=
           KeygenM23MatrixSpec.array_words_i /\
         W64.to_uint zetasctr{1} = zetasctr{2} /\
         W64.to_uint len{1} = len{2} /\
         KeygenM23MatrixSpec.m23_fwd_len_schedule len{2} /\
         0 < len{2} /\
         W64.to_uint start{1} = start{2} /\
         0 <= start{2} <= 256 /\
         KeygenM23MatrixSpec.m23_fwd_block_start len{2} start{2} /\
         2 * (zetasctr{2} + 1) * len{2} = 256 + start{2} /\
         TargetKeygenM23WideSupport.poly_slice xp{1}
           (W64.to_uint base{1}) = rp0{2} /\
         TargetKeygenM23WideSupport.poly_slice_frame
           xp{2} xp{1} (W64.to_uint base{1})).
      + wp.
        while
          (={poly, base, count, zetasp, zeta_0} /\
           zetasp{1} = HpolyTarget.jzetas /\
           count{1} = W64.of_int verify_unpack_ntt_polys /\
           W64.to_uint poly{1} < verify_unpack_ntt_polys /\
           W64.to_uint base{1} =
             KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
           0 <= W64.to_uint base{1} /\
           W64.to_uint base{1} + KeygenM23MatrixSpec.poly_words_i <=
             KeygenM23MatrixSpec.array_words_i /\
           W64.to_uint zetasctr{1} = zetasctr{2} /\
           W64.to_uint len{1} = len{2} /\
           KeygenM23MatrixSpec.m23_fwd_len_schedule len{2} /\
           0 < len{2} /\
           W64.to_uint start{1} = start{2} /\
           0 <= start{2} < 256 /\
           KeygenM23MatrixSpec.m23_fwd_block_start len{2} start{2} /\
           start{2} + 2 * len{2} <= 256 /\
           2 * zetasctr{2} * len{2} = 256 + start{2} /\
           W64.to_uint cmp{1} = cmp{2} /\
           cmp{2} = start{2} + len{2} /\
           W64.to_uint j{1} = j{2} /\
           start{2} <= j{2} <= cmp{2} /\
           TargetKeygenM23WideSupport.poly_slice xp{1}
             (W64.to_uint base{1}) = rp0{2} /\
           TargetKeygenM23WideSupport.poly_slice_frame
             xp{2} xp{1} (W64.to_uint base{1})).
        + wp.
          call TargetKeygenM23WideSupport.parent_single_fqmul_equiv.
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
              rewrite /verify_unpack_ntt_polys
                      /KeygenM23MatrixSpec.poly_words_i
                      /KeygenM23MatrixSpec.array_words_i.
              smt().
          have hbase_words :
              W64.to_uint base{2} + 256 <= 2048.
          + move: hpoly hbase.
            rewrite /verify_unpack_ntt_polys
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

lemma wide_polyvec_ntt_verify_unpack_count2_bound24
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Wide._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound16 xp0 p0 p1
    ==>
    verify_unpack_ntt_repr_bound24 res p0 p1 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
proc.
rcondt 3; first by auto.
rcondt 8; first by auto; call (_ : true); auto.
rcondf 13; first by
  auto; call (_ : true); auto; call (_ : true); auto.
wp.
call (TargetNTTRefinement.target_poly_ntt_correct p1).
wp.
call (TargetNTTRefinement.target_poly_ntt_correct p0).
wp.
skip.
move=> &hr [-> [hcount hin]].
move: hin.
rewrite /verify_unpack_ntt_input_repr_bound16.
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
      (TargetKeygenM23WideSupport.poly_slice xp0 0) p0 16.
+ have hbridge :
      (KeygenM23ArithmeticSpec.wide_slice_repr_bound xp0 0 p0 16 <=>
       NTT_Fq.poly_repr_bound
         (TargetKeygenM23WideSupport.poly_slice xp0 0) p0 16).
  + apply TargetKeygenM23WideSupport.wide_slice_poly_repr_bound.
    exact hbound0.
  move: hin0.
  by rewrite hbridge.
have hrepr1 :
    NTT_Fq.poly_repr_bound
      (TargetKeygenM23WideSupport.poly_slice
         xp0 KeygenM23MatrixSpec.poly_words_i) p1 16.
+ have hbridge :
      (KeygenM23ArithmeticSpec.wide_slice_repr_bound
         xp0 KeygenM23MatrixSpec.poly_words_i p1 16 <=>
       NTT_Fq.poly_repr_bound
         (TargetKeygenM23WideSupport.poly_slice
            xp0 KeygenM23MatrixSpec.poly_words_i) p1 16).
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
      0 (NTTFullSpec.full_ntt p0) 24.
+ rewrite TargetKeygenM23WideSupport.wide_slice_poly_repr_bound 1:hbound0.
  by rewrite hother10 hsame0.
have hpost1 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      KeygenM23MatrixSpec.poly_words_i
      (NTTFullSpec.full_ntt p1) 24.
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
rewrite /verify_unpack_ntt_repr_bound24.
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

lemma verify_unpack_ntt_repr_bound24_forward_repr
    (before after : BArray8192.t) (p0 p1 : Rq.poly) :
  verify_unpack_ntt_input_repr_bound16 before p0 p1 =>
  verify_unpack_ntt_repr_bound24 after p0 p1 =>
  NTTRowProductSpec.vector_forward_repr
    verify_unpack_ntt_polys
    (fun col =>
      KeygenM23ArithmeticSpec.wide_poly
        after (col * KeygenM23MatrixSpec.poly_words_i))
    (fun col =>
      KeygenM23ArithmeticSpec.wide_poly
        before (col * KeygenM23MatrixSpec.poly_words_i)).
proof.
rewrite /verify_unpack_ntt_input_repr_bound16
        /verify_unpack_ntt_repr_bound24
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

lemma parent_polyvec_ntt_verify_unpack_count2_bound24
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Parent._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound16 xp0 p0 p1
    ==>
    verify_unpack_ntt_repr_bound24 res p0 p1 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
have hwide := wide_polyvec_ntt_verify_unpack_count2_bound24 xp0 p0 p1.
by conseq parent_polyvec_ntt_equiv_wide_count2 hwide => /#.
qed.

lemma parent_polyvec_ntt_verify_unpack_count2_correct
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Parent._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound16 xp0 p0 p1
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
have hparent := parent_polyvec_ntt_verify_unpack_count2_bound24 xp0 p0 p1.
conseq hparent => //=.
move=> &m [_ [_ hin]] result [hout htail].
split.
+ exact
    (verify_unpack_ntt_repr_bound24_forward_repr
      xp0 result p0 p1 hin hout).
+ exact htail.
qed.

lemma verify_unpack_polyvec_ntt_count2_bound24
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Verify._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound16 xp0 p0 p1
    ==>
    verify_unpack_ntt_repr_bound24 res p0 p1 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_unpack_ntt_words].
proof.
by conseq verify_unpack_polyvec_ntt_equiv_parent
  (parent_polyvec_ntt_verify_unpack_count2_bound24 xp0 p0 p1) => /#.
qed.

lemma verify_unpack_polyvec_ntt_count2_correct
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Verify._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound16 xp0 p0 p1
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
by conseq verify_unpack_polyvec_ntt_equiv_parent
  (parent_polyvec_ntt_verify_unpack_count2_correct xp0 p0 p1) => /#.
qed.

lemma verify_unpack_polyvec_ntt_count2_full_correct
    (xp0 : BArray8192.t) (p0 p1 : Rq.poly) :
  hoare [Verify._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_unpack_ntt_polys /\
    verify_unpack_ntt_input_repr_bound16 xp0 p0 p1
    ==>
    verify_unpack_ntt_repr_bound24 res p0 p1 /\
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
  (verify_unpack_polyvec_ntt_count2_bound24 xp0 p0 p1)
  (verify_unpack_polyvec_ntt_count2_correct xp0 p0 p1) => />.
qed.

end VerifyUnpackV3NttPostFreeze.
