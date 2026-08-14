require import AllCore IntDiv List Ring StdOrder.

from Jasmin require import JModel_x86.

import SLH64.
require import VerifyCoreTarget KeygenMode2ParentTarget.
require import KeygenM23MatrixSpec KeygenM23ArithmeticSpec.
require import Array256 Fq GFq Rq.
require import NTT_Fq NTTFullSpec NTTRowProductSpec
               NTTFullSpectralAction RefJasminNTT.
require import TargetNTTRefinement
               TargetKeygenM23Pointwise
               TargetKeygenM23WideNTT
               TargetKeygenM23WideSupport
               TargetKeygenM23WideInvNTT.

import Zq IntOrder.

theory VerifyMatrixCrtPostFreeze.

module Verify = VerifyCoreTarget.M.
module Parent = KeygenMode2ParentTarget.M.
module Single = TargetKeygenM23WideSupport.Single.
module Wide = TargetKeygenM23WideNTT.WideSpec.

op verify_mode2_rows_i : int = 2.
op verify_mode2_cols_i : int = 4.
op verify_mode2_vec_words_i : int =
  verify_mode2_cols_i * KeygenM23MatrixSpec.poly_words_i.
op verify_mode2_out_words_i : int =
  verify_mode2_rows_i * KeygenM23MatrixSpec.poly_words_i.

op verify_mode2_input_repr_bound16
    (s : BArray8192.t) (p0 p1 p2 p3 : Rq.poly) : bool =
  KeygenM23ArithmeticSpec.wide_slice_repr_bound s 0 p0 16 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s KeygenM23MatrixSpec.poly_words_i p1 16 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s (2 * KeygenM23MatrixSpec.poly_words_i) p2 16 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s (3 * KeygenM23MatrixSpec.poly_words_i) p3 16.

op verify_mode2_ntt_repr_bound24
    (s : BArray8192.t) (p0 p1 p2 p3 : Rq.poly) : bool =
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s 0 (NTTFullSpec.full_ntt p0) 24 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s KeygenM23MatrixSpec.poly_words_i
    (NTTFullSpec.full_ntt p1) 24 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s (2 * KeygenM23MatrixSpec.poly_words_i)
    (NTTFullSpec.full_ntt p2) 24 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    s (3 * KeygenM23MatrixSpec.poly_words_i)
    (NTTFullSpec.full_ntt p3) 24.

module ActualVerifyMatrixNttAccMode2 = {
  var input_z1 : BArray8192.t
  var input_high : BArray8192.t
  var input_a1 : BArray32768.t

  var after_ntt : BArray8192.t
  var after_acc : BArray8192.t
  var after_inv : BArray8192.t

  proc run
      (z1p : BArray8192.t, highp : BArray8192.t, a1p : BArray32768.t)
      : BArray8192.t * BArray8192.t = {
    input_z1 <- z1p;
    input_high <- highp;
    input_a1 <- a1p;

    z1p <@ Verify._polyvec_ntt (z1p, W64.of_int verify_mode2_cols_i);
    after_ntt <- z1p;

    highp <@ Verify._polymat_pointwise_acc
      (highp, a1p, z1p,
       W64.of_int verify_mode2_rows_i, W64.of_int verify_mode2_cols_i);
    after_acc <- highp;

    highp <@ Verify._polyvec_invntt (highp, W64.of_int verify_mode2_rows_i);
    after_inv <- highp;

    return (z1p, highp);
  }
}.

lemma verify_polyvec_ntt_equiv_parent :
  equiv [Verify._polyvec_ntt ~ Parent._polyvec_ntt :
    ={xp, count} ==> ={res}].
proof.
proc.
sim.
qed.

lemma verify_polymat_pointwise_acc_equiv_parent :
  equiv [Verify._polymat_pointwise_acc ~ Parent._polymat_pointwise_acc :
    ={tp, mp, vp, rows, cols} ==> ={res}].
proof.
proc.
sim.
qed.

lemma verify_polyvec_invntt_equiv_parent :
  equiv [Verify._polyvec_invntt ~ Parent._polyvec_invntt :
    ={xp, count} ==> ={res}].
proof.
proc.
sim.
qed.

lemma parent_polyvec_ntt_equiv_wide_cols4 :
  equiv [Parent._polyvec_ntt ~ Wide._polyvec_ntt :
    ={xp, count} /\
    count{1} = W64.of_int verify_mode2_cols_i
    ==> ={res}].
proof.
proc.
while
  (={xp, poly, base, count} /\
   count{1} = W64.of_int verify_mode2_cols_i /\
   W64.to_uint poly{1} <= verify_mode2_cols_i /\
   W64.to_uint base{1} =
     KeygenM23MatrixSpec.poly_words_i * W64.to_uint poly{1} /\
   0 <= W64.to_uint base{1} /\
   W64.to_uint base{1} + KeygenM23MatrixSpec.poly_words_i <=
     KeygenM23MatrixSpec.array_words_i /\
   zetasp{1} = HpolyTarget.jzetas).
+ inline Single._poly_ntt.
  seq 2 6 :
    (={poly, base, count, zetasp} /\
     zetasp{1} = HpolyTarget.jzetas /\
     count{1} = W64.of_int verify_mode2_cols_i /\
     W64.to_uint poly{1} < verify_mode2_cols_i /\
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
    rewrite W64.ultE W64.of_uintK /verify_mode2_cols_i /=.
    trivial.
  seq 1 1 :
    (={poly, base, count, zetasp} /\
     zetasp{1} = HpolyTarget.jzetas /\
     count{1} = W64.of_int verify_mode2_cols_i /\
     W64.to_uint poly{1} < verify_mode2_cols_i /\
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
       count{1} = W64.of_int verify_mode2_cols_i /\
       W64.to_uint poly{1} < verify_mode2_cols_i /\
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
         count{1} = W64.of_int verify_mode2_cols_i /\
         W64.to_uint poly{1} < verify_mode2_cols_i /\
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
           count{1} = W64.of_int verify_mode2_cols_i /\
           W64.to_uint poly{1} < verify_mode2_cols_i /\
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
              W64.to_uint base{2} + KeygenM23MatrixSpec.poly_words_i <=
                KeygenM23MatrixSpec.array_words_i.
          + split.
            * exact hbase0.
            * move: hpoly hbase.
              rewrite /verify_mode2_cols_i
                      /KeygenM23MatrixSpec.poly_words_i
                      /KeygenM23MatrixSpec.array_words_i.
              smt().
          have hbase_words :
              W64.to_uint base{2} + 256 <= 2048.
          + move: hpoly hbase.
            rewrite /verify_mode2_cols_i
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
                (TargetKeygenM23WideSupport.poly_slice
                   xp{1} (W64.to_uint base{2}))
                (W64.to_uint j{1} + W64.to_uint len{1}).
          + rewrite hbasejlen.
            rewrite TargetKeygenM23WideSupport.poly_slice_get32 1:hbase_bound 1:/#.
            trivial.
          have hslice_set :
              TargetKeygenM23WideSupport.poly_slice
                (BArray8192.set32
                  (BArray8192.set32 xp{1}
                    (W64.to_uint (base{2} + (j{1} + len{1})))
                    (BArray8192.get32 xp{1}
                       (W64.to_uint (base{2} + j{1})) - t{2}))
                  (W64.to_uint (base{2} + j{1}))
                  (BArray8192.get32 xp{1}
                     (W64.to_uint (base{2} + j{1})) + t{2}))
                (W64.to_uint base{2}) =
              BArray1024.set32
                (BArray1024.set32
                  (TargetKeygenM23WideSupport.poly_slice
                     xp{1} (W64.to_uint base{2}))
                  (W64.to_uint j{1} + W64.to_uint len{1})
                  (BArray1024.get32
                     (TargetKeygenM23WideSupport.poly_slice
                        xp{1} (W64.to_uint base{2}))
                     (W64.to_uint j{1}) - t{2}))
                (W64.to_uint j{1})
                (BArray1024.get32
                   (TargetKeygenM23WideSupport.poly_slice
                      xp{1} (W64.to_uint base{2}))
                   (W64.to_uint j{1}) + t{2}).
          + rewrite hbasejlen hbasej.
            rewrite TargetKeygenM23WideSupport.poly_slice_set32 1:hbase_bound 1:/#.
            rewrite TargetKeygenM23WideSupport.poly_slice_get32 1:hbase_bound 1:/#.
            trivial.
          have hframe2 :
              TargetKeygenM23WideSupport.poly_slice_frame xp{2}
                (BArray8192.set32
                  (BArray8192.set32 xp{1}
                    (W64.to_uint (base{2} + (j{1} + len{1})))
                    (BArray8192.get32 xp{1}
                       (W64.to_uint (base{2} + j{1})) - t{2}))
                  (W64.to_uint (base{2} + j{1}))
                  (BArray8192.get32 xp{1}
                     (W64.to_uint (base{2} + j{1})) + t{2}))
                (W64.to_uint base{2}).
          + rewrite /TargetKeygenM23WideSupport.poly_slice_frame in hframe.
            rewrite /TargetKeygenM23WideSupport.poly_slice_frame.
            move=> x hx hout.
            have hidx1 :
                W64.to_uint base{2} <= W64.to_uint (base{2} + j{1}) <
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
        rewrite TargetKeygenM23WideSupport.poly_slice_set32 1:hbase_bound 1:/#.
        trivial.
        congr; ring.
        move=> _.
        split.
        + exact hcoeff.
        move=> _ result_R.
        have hslice_result :
            TargetKeygenM23WideSupport.poly_slice
              (BArray8192.set32
                (BArray8192.set32 xp{1}
                  (W64.to_uint (base{2} + (j{1} + len{1})))
                  (BArray8192.get32 xp{1}
                     (W64.to_uint (base{2} + j{1})) - result_R))
                (W64.to_uint (base{2} + j{1}))
                (BArray8192.get32 xp{1}
                   (W64.to_uint (base{2} + j{1})) + result_R))
              (W64.to_uint base{2}) =
            BArray1024.set32
              (BArray1024.set32
                (TargetKeygenM23WideSupport.poly_slice
                   xp{1} (W64.to_uint base{2}))
                (W64.to_uint j{1} + W64.to_uint len{1})
                (BArray1024.get32
                   (TargetKeygenM23WideSupport.poly_slice
                      xp{1} (W64.to_uint base{2}))
                   (W64.to_uint j{1}) - result_R))
              (W64.to_uint j{1})
              (BArray1024.get32
                 (TargetKeygenM23WideSupport.poly_slice
                    xp{1} (W64.to_uint base{2}))
                 (W64.to_uint j{1}) + result_R).
        + rewrite hbasejlen hbasej.
          have hidxassoc :
              W64.to_uint base{2} + W64.to_uint j{1} +
                W64.to_uint len{1} =
              W64.to_uint base{2} +
                (W64.to_uint j{1} + W64.to_uint len{1}) by ring.
          rewrite hidxassoc.
          rewrite TargetKeygenM23WideSupport.poly_slice_set32 1:hbase_bound 1:/#.
          rewrite TargetKeygenM23WideSupport.poly_slice_get32 1:hbase_bound 1:/#.
          trivial.
        have hframe_result :
            TargetKeygenM23WideSupport.poly_slice_frame xp{2}
              (BArray8192.set32
                (BArray8192.set32 xp{1}
                  (W64.to_uint (base{2} + (j{1} + len{1})))
                  (BArray8192.get32 xp{1}
                     (W64.to_uint (base{2} + j{1})) - result_R))
                (W64.to_uint (base{2} + j{1}))
                (BArray8192.get32 xp{1}
                   (W64.to_uint (base{2} + j{1})) + result_R))
              (W64.to_uint base{2}).
        + have hidxassoc2 :
              W64.to_uint base{2} + W64.to_uint j{1} +
                W64.to_uint len{1} =
              W64.to_uint base{2} +
                (W64.to_uint j{1} + W64.to_uint len{1}) by ring.
          rewrite hbasejlen hbasej hidxassoc2.
          apply TargetKeygenM23WideSupport.poly_slice_frame_set32.
          * exact hbase_bound.
          * smt().
          * apply TargetKeygenM23WideSupport.poly_slice_frame_set32.
            + exact hbase_bound.
            + smt().
            + exact hframe.
        rewrite TargetKeygenM23WideSupport.poly_slice_set32
          1:hbase_bound 1:/#.
        trivial.
        have hframe_result2 :
            TargetKeygenM23WideSupport.poly_slice_frame xp{2}
              (BArray8192.set32
                (BArray8192.set32 xp{1}
                  (W64.to_uint (base{2} + (j{1} + len{1})))
                  (BArray8192.get32 xp{1}
                     (W64.to_uint (base{2} + j{1})) - result_R))
                (W64.to_uint (base{2} + j{1}))
                (BArray8192.get32 xp{1}
                   (W64.to_uint (base{2} + j{1})) + result_R))
              (W64.to_uint base{2}).
        + have hidxassoc2 :
              W64.to_uint base{2} + W64.to_uint j{1} +
                W64.to_uint len{1} =
              W64.to_uint base{2} +
                (W64.to_uint j{1} + W64.to_uint len{1}) by ring.
          rewrite hbasejlen hbasej hidxassoc2.
          apply TargetKeygenM23WideSupport.poly_slice_frame_set32.
          * exact hbase_bound.
          * smt().
          * apply TargetKeygenM23WideSupport.poly_slice_frame_set32.
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
    + apply TargetKeygenM23WideSupport.int_shr1_div2.
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
  move=> &1 &2 hpoly hbase hbase0 hbasecap hsched hstage hframe.
  rewrite W64.ultE W64.to_uint0.
  trivial.
wp.
skip => /> &1 &2 hpoly hbase hbase0 hbasecap hsched hstage hframe.
have hreassemble :
    xp{1} =
      TargetKeygenM23WideSupport.put_poly_slice xp{2}
        (W64.to_uint base{2})
        (TargetKeygenM23WideSupport.poly_slice
           xp{1} (W64.to_uint base{2})).
+ apply TargetKeygenM23WideSupport.poly_slice_reassemble.
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
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        xp{2} (W64.to_uint base{2})
        (TargetKeygenM23WideSupport.poly_slice
           xp{1} (W64.to_uint base{2})))
      (W64.to_uint base{2}) =
    TargetKeygenM23WideSupport.poly_slice
      xp{1} (W64.to_uint base{2}).
+ apply TargetKeygenM23WideSupport.poly_slice_put_same.
  smt().
rewrite hreassemble hpolysucc hbasesucc hslice_put
        /KeygenM23MatrixSpec.poly_words_i.
smt().
auto => />.
qed.

lemma wide_polyvec_ntt_verify_cols4_correct
    (xp0 : BArray8192.t) (p0 p1 p2 p3 : Rq.poly) :
  hoare [Wide._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_mode2_cols_i /\
    verify_mode2_input_repr_bound16 xp0 p0 p1 p2 p3
    ==>
    verify_mode2_ntt_repr_bound24 res p0 p1 p2 p3 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_mode2_vec_words_i].
proof.
proc.
rcondt 3; first by auto.
rcondt 8; first by auto; call (_ : true); auto.
rcondt 13; first by auto; call (_ : true); auto; call (_ : true); auto.
rcondt 18; first by
  auto; call (_ : true); auto; call (_ : true); auto; call (_ : true); auto.
rcondf 23; first by
  auto; call (_ : true); auto; call (_ : true); auto;
  call (_ : true); auto; call (_ : true); auto.
wp.
call (TargetNTTRefinement.target_poly_ntt_correct p3).
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
rewrite /verify_mode2_input_repr_bound16.
move=> [hin0 [hin1 [hin2 hin3]]].
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
have hbound3 :
    0 <= 3 * KeygenM23MatrixSpec.poly_words_i /\
    3 * KeygenM23MatrixSpec.poly_words_i +
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
have hbound768 :
    0 <= 768 /\
    768 + KeygenM23MatrixSpec.poly_words_i <=
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
have hrepr2 :
    NTT_Fq.poly_repr_bound
      (TargetKeygenM23WideSupport.poly_slice
         xp0 (2 * KeygenM23MatrixSpec.poly_words_i)) p2 16.
+ have hbridge :
      (KeygenM23ArithmeticSpec.wide_slice_repr_bound
         xp0 (2 * KeygenM23MatrixSpec.poly_words_i) p2 16 <=>
       NTT_Fq.poly_repr_bound
         (TargetKeygenM23WideSupport.poly_slice
            xp0 (2 * KeygenM23MatrixSpec.poly_words_i)) p2 16).
  + apply TargetKeygenM23WideSupport.wide_slice_poly_repr_bound.
    exact hbound2.
  move: hin2.
  by rewrite hbridge.
have hrepr3 :
    NTT_Fq.poly_repr_bound
      (TargetKeygenM23WideSupport.poly_slice
         xp0 (3 * KeygenM23MatrixSpec.poly_words_i)) p3 16.
+ have hbridge :
      (KeygenM23ArithmeticSpec.wide_slice_repr_bound
         xp0 (3 * KeygenM23MatrixSpec.poly_words_i) p3 16 <=>
       NTT_Fq.poly_repr_bound
         (TargetKeygenM23WideSupport.poly_slice
            xp0 (3 * KeygenM23MatrixSpec.poly_words_i)) p3 16).
  + apply TargetKeygenM23WideSupport.wide_slice_poly_repr_bound.
    exact hbound3.
  move: hin3.
  by rewrite hbridge.
split.
+ exact hrepr0.
move=> _ r0 hr0.
have hslice1 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0) 256 =
    TargetKeygenM23WideSupport.poly_slice xp0 256.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound0.
  + exact hbound256.
  + right.
    smt().
split.
+ rewrite hslice1.
  move: hrepr1.
  by rewrite /KeygenM23MatrixSpec.poly_words_i.
move=> _ r1 hr1.
have hslice20 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0) 512 =
    TargetKeygenM23WideSupport.poly_slice xp0 512.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound0.
  + exact hbound512.
  + right.
    smt().
have hslice21 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        256 r1) 512 =
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0) 512.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound256.
  + exact hbound512.
  + right.
    smt().
split.
+ rewrite hslice21 hslice20.
  move: hrepr2.
  by rewrite /KeygenM23MatrixSpec.poly_words_i.
move=> _ r2 hr2.
have hslice30 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0) 768 =
    TargetKeygenM23WideSupport.poly_slice xp0 768.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound0.
  + exact hbound768.
  + right.
    smt().
have hslice31 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        256 r1) 768 =
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0) 768.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound256.
  + exact hbound768.
  + right.
    smt().
have hslice32 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
          256 r1)
        512 r2) 768 =
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        256 r1) 768.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound512.
  + exact hbound768.
  + right.
    smt().
split.
+ rewrite hslice32 hslice31 hslice30.
  move: hrepr3.
  by rewrite /KeygenM23MatrixSpec.poly_words_i.
move=> _ r3 hr3.
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
have hother20 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2) 0 =
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1) 0.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound2.
  + exact hbound0.
  + left.
    smt().
have hother30 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice
            (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
            KeygenM23MatrixSpec.poly_words_i r1)
          (2 * KeygenM23MatrixSpec.poly_words_i) r2)
        (3 * KeygenM23MatrixSpec.poly_words_i) r3) 0 =
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2) 0.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound3.
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
have hother21 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      KeygenM23MatrixSpec.poly_words_i =
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      KeygenM23MatrixSpec.poly_words_i.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound2.
  + exact hbound1.
  + left.
    smt().
have hother31 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice
            (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
            KeygenM23MatrixSpec.poly_words_i r1)
          (2 * KeygenM23MatrixSpec.poly_words_i) r2)
        (3 * KeygenM23MatrixSpec.poly_words_i) r3)
      KeygenM23MatrixSpec.poly_words_i =
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      KeygenM23MatrixSpec.poly_words_i.
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound3.
  + exact hbound1.
  + left.
    smt().
have hsame2 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      (2 * KeygenM23MatrixSpec.poly_words_i) = r2.
+ apply TargetKeygenM23WideSupport.poly_slice_put_same.
  exact hbound2.
have hother32 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice
            (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
            KeygenM23MatrixSpec.poly_words_i r1)
          (2 * KeygenM23MatrixSpec.poly_words_i) r2)
        (3 * KeygenM23MatrixSpec.poly_words_i) r3)
      (2 * KeygenM23MatrixSpec.poly_words_i) =
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      (2 * KeygenM23MatrixSpec.poly_words_i).
+ apply TargetKeygenM23WideSupport.poly_slice_put_other.
  + exact hbound3.
  + exact hbound2.
  + left.
    smt().
have hsame3 :
    TargetKeygenM23WideSupport.poly_slice
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice
            (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
            KeygenM23MatrixSpec.poly_words_i r1)
          (2 * KeygenM23MatrixSpec.poly_words_i) r2)
        (3 * KeygenM23MatrixSpec.poly_words_i) r3)
      (3 * KeygenM23MatrixSpec.poly_words_i) = r3.
+ apply TargetKeygenM23WideSupport.poly_slice_put_same.
  exact hbound3.
have hpost0 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice
            (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
            KeygenM23MatrixSpec.poly_words_i r1)
          (2 * KeygenM23MatrixSpec.poly_words_i) r2)
        (3 * KeygenM23MatrixSpec.poly_words_i) r3)
      0 (NTTFullSpec.full_ntt p0) 24.
+ rewrite TargetKeygenM23WideSupport.wide_slice_poly_repr_bound 1:hbound0.
  by rewrite hother30 hother20 hother10 hsame0.
have hpost1 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice
            (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
            KeygenM23MatrixSpec.poly_words_i r1)
          (2 * KeygenM23MatrixSpec.poly_words_i) r2)
        (3 * KeygenM23MatrixSpec.poly_words_i) r3)
      KeygenM23MatrixSpec.poly_words_i
      (NTTFullSpec.full_ntt p1) 24.
+ rewrite TargetKeygenM23WideSupport.wide_slice_poly_repr_bound 1:hbound1.
  by rewrite hother31 hother21 hsame1.
have hpost2 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice
            (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
            KeygenM23MatrixSpec.poly_words_i r1)
          (2 * KeygenM23MatrixSpec.poly_words_i) r2)
        (3 * KeygenM23MatrixSpec.poly_words_i) r3)
      (2 * KeygenM23MatrixSpec.poly_words_i)
      (NTTFullSpec.full_ntt p2) 24.
+ rewrite TargetKeygenM23WideSupport.wide_slice_poly_repr_bound 1:hbound2.
  by rewrite hother32 hsame2.
have hpost3 :
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice
            (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
            KeygenM23MatrixSpec.poly_words_i r1)
          (2 * KeygenM23MatrixSpec.poly_words_i) r2)
        (3 * KeygenM23MatrixSpec.poly_words_i) r3)
      (3 * KeygenM23MatrixSpec.poly_words_i)
      (NTTFullSpec.full_ntt p3) 24.
+ rewrite TargetKeygenM23WideSupport.wide_slice_poly_repr_bound 1:hbound3.
  by rewrite hsame3.
have htail0 :
    KeygenM23MatrixSpec.word_tail_frame
      xp0 xp0 verify_mode2_vec_words_i by
  rewrite /KeygenM23MatrixSpec.word_tail_frame.
have htail1 :
    KeygenM23MatrixSpec.word_tail_frame
      xp0
      (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
      verify_mode2_vec_words_i by
  apply
    (TargetKeygenM23WideSupport.word_tail_frame_put_before
      xp0 xp0 0 verify_mode2_vec_words_i r0);
    [ rewrite /verify_mode2_vec_words_i
              /verify_mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i /=
    | rewrite /verify_mode2_vec_words_i
              /verify_mode2_cols_i
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
      verify_mode2_vec_words_i by
  apply
    (TargetKeygenM23WideSupport.word_tail_frame_put_before
      xp0 (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
      KeygenM23MatrixSpec.poly_words_i verify_mode2_vec_words_i r1);
    [ rewrite /verify_mode2_vec_words_i
              /verify_mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i /=
    | rewrite /verify_mode2_vec_words_i
              /verify_mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i
              /KeygenM23MatrixSpec.array_words_i
              /BArray8192.size /=
    | exact htail1 ].
have htail3 :
    KeygenM23MatrixSpec.word_tail_frame
      xp0
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      verify_mode2_vec_words_i by
  apply
    (TargetKeygenM23WideSupport.word_tail_frame_put_before
      xp0
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
        KeygenM23MatrixSpec.poly_words_i r1)
      (2 * KeygenM23MatrixSpec.poly_words_i) verify_mode2_vec_words_i r2);
    [ rewrite /verify_mode2_vec_words_i
              /verify_mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i /=
    | rewrite /verify_mode2_vec_words_i
              /verify_mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i
              /KeygenM23MatrixSpec.array_words_i
              /BArray8192.size /=
    | exact htail2 ].
have htail4 :
    KeygenM23MatrixSpec.word_tail_frame
      xp0
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice
            (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
            KeygenM23MatrixSpec.poly_words_i r1)
          (2 * KeygenM23MatrixSpec.poly_words_i) r2)
        (3 * KeygenM23MatrixSpec.poly_words_i) r3)
      verify_mode2_vec_words_i by
  apply
    (TargetKeygenM23WideSupport.word_tail_frame_put_before
      xp0
      (TargetKeygenM23WideSupport.put_poly_slice
        (TargetKeygenM23WideSupport.put_poly_slice
          (TargetKeygenM23WideSupport.put_poly_slice xp0 0 r0)
          KeygenM23MatrixSpec.poly_words_i r1)
        (2 * KeygenM23MatrixSpec.poly_words_i) r2)
      (3 * KeygenM23MatrixSpec.poly_words_i) verify_mode2_vec_words_i r3);
    [ rewrite /verify_mode2_vec_words_i
              /verify_mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i /=
    | rewrite /verify_mode2_vec_words_i
              /verify_mode2_cols_i
              /KeygenM23MatrixSpec.poly_words_i
              /KeygenM23MatrixSpec.array_words_i
              /BArray8192.size /=
    | exact htail3 ].
simplify.
rewrite /verify_mode2_ntt_repr_bound24.
split.
+ split.
  + exact hpost0.
  + split.
    + move: hpost1.
      by rewrite /KeygenM23MatrixSpec.poly_words_i /=.
    + split.
      + move: hpost2.
        by rewrite /KeygenM23MatrixSpec.poly_words_i /=.
      + move: hpost3.
        by rewrite /KeygenM23MatrixSpec.poly_words_i /=.
+ move: htail4.
  by rewrite /KeygenM23MatrixSpec.poly_words_i /=.
qed.

lemma verify_mode2_ntt_repr_bound24_forward_repr
    (before after : BArray8192.t) (p0 p1 p2 p3 : Rq.poly) :
  verify_mode2_input_repr_bound16 before p0 p1 p2 p3 =>
  verify_mode2_ntt_repr_bound24 after p0 p1 p2 p3 =>
  NTTRowProductSpec.vector_forward_repr
    verify_mode2_cols_i
    (fun col =>
      KeygenM23ArithmeticSpec.wide_poly
        after (col * KeygenM23MatrixSpec.poly_words_i))
    (fun col =>
      KeygenM23ArithmeticSpec.wide_poly
        before (col * KeygenM23MatrixSpec.poly_words_i)).
proof.
rewrite /verify_mode2_input_repr_bound16
        /verify_mode2_ntt_repr_bound24
        /NTTRowProductSpec.vector_forward_repr.
move=> [hin0 [hin1 [hin2 hin3]]] [hout0 [hout1 [hout2 hout3]]] col hcol.
case (col = 0) => h0.
+ subst col.
  move: hin0 hout0.
  rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  by move=> [-> _] [-> _].
case (col = 1) => h1.
+ subst col.
  move: hin1 hout1.
  rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound
          /KeygenM23MatrixSpec.poly_words_i /=.
  by move=> [-> _] [-> _].
case (col = 2) => h2.
+ subst col.
  move: hin2 hout2.
  rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound
          /KeygenM23MatrixSpec.poly_words_i /=.
  by move=> [-> _] [-> _].
have h3 : col = 3 by smt().
subst col.
move: hin3 hout3.
rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound
        /KeygenM23MatrixSpec.poly_words_i /=.
by move=> [-> _] [-> _].
qed.

lemma parent_polyvec_ntt_verify_cols4_correct
    (xp0 : BArray8192.t) (p0 p1 p2 p3 : Rq.poly) :
  hoare [Parent._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_mode2_cols_i /\
    verify_mode2_input_repr_bound16 xp0 p0 p1 p2 p3
    ==>
    NTTRowProductSpec.vector_forward_repr
      verify_mode2_cols_i
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          res (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          xp0 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_mode2_vec_words_i].
proof.
have hwide := wide_polyvec_ntt_verify_cols4_correct xp0 p0 p1 p2 p3.
have hparent :
  hoare [Parent._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_mode2_cols_i /\
    verify_mode2_input_repr_bound16 xp0 p0 p1 p2 p3
    ==>
    verify_mode2_ntt_repr_bound24 res p0 p1 p2 p3 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_mode2_vec_words_i].
+ by conseq parent_polyvec_ntt_equiv_wide_cols4 hwide => /#.
conseq hparent => //=.
move=> &m [_ [_ hin]] result [hout htail].
split.
+ exact
    (verify_mode2_ntt_repr_bound24_forward_repr
      xp0 result p0 p1 p2 p3 hin hout).
+ exact htail.
qed.

lemma verify_polyvec_ntt_verify_cols4_correct
    (xp0 : BArray8192.t) (p0 p1 p2 p3 : Rq.poly) :
  hoare [Verify._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_mode2_cols_i /\
    verify_mode2_input_repr_bound16 xp0 p0 p1 p2 p3
    ==>
    NTTRowProductSpec.vector_forward_repr
      verify_mode2_cols_i
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          res (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          xp0 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_mode2_vec_words_i].
proof.
by conseq verify_polyvec_ntt_equiv_parent
  (parent_polyvec_ntt_verify_cols4_correct xp0 p0 p1 p2 p3) => /#.
qed.

lemma parent_polyvec_ntt_verify_cols4_bound24
    (xp0 : BArray8192.t) (p0 p1 p2 p3 : Rq.poly) :
  hoare [Parent._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_mode2_cols_i /\
    verify_mode2_input_repr_bound16 xp0 p0 p1 p2 p3
    ==>
    verify_mode2_ntt_repr_bound24 res p0 p1 p2 p3 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_mode2_vec_words_i].
proof.
have hwide := wide_polyvec_ntt_verify_cols4_correct xp0 p0 p1 p2 p3.
by conseq parent_polyvec_ntt_equiv_wide_cols4 hwide => /#.
qed.

lemma verify_polyvec_ntt_verify_cols4_bound24
    (xp0 : BArray8192.t) (p0 p1 p2 p3 : Rq.poly) :
  hoare [Verify._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_mode2_cols_i /\
    verify_mode2_input_repr_bound16 xp0 p0 p1 p2 p3
    ==>
    verify_mode2_ntt_repr_bound24 res p0 p1 p2 p3 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_mode2_vec_words_i].
proof.
by conseq verify_polyvec_ntt_equiv_parent
  (parent_polyvec_ntt_verify_cols4_bound24 xp0 p0 p1 p2 p3) => /#.
qed.

lemma verify_polyvec_ntt_verify_cols4_full_correct
    (xp0 : BArray8192.t) (p0 p1 p2 p3 : Rq.poly) :
  hoare [Verify._polyvec_ntt :
    xp = xp0 /\
    count = W64.of_int verify_mode2_cols_i /\
    verify_mode2_input_repr_bound16 xp0 p0 p1 p2 p3
    ==>
    verify_mode2_ntt_repr_bound24 res p0 p1 p2 p3 /\
    NTTRowProductSpec.vector_forward_repr
      verify_mode2_cols_i
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          res (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          xp0 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_mode2_vec_words_i].
proof.
conseq
  (verify_polyvec_ntt_verify_cols4_bound24 xp0 p0 p1 p2 p3)
  (verify_polyvec_ntt_verify_cols4_correct xp0 p0 p1 p2 p3) => />.
qed.

op prefix_bound8192
    (a : BArray8192.t) (words sz : int) : bool =
  TargetKeygenM23Pointwise.prefix_bound8192 a words sz.

op row_zero_prefix
    (a : BArray8192.t) (base upto : int) : bool =
  TargetKeygenM23Pointwise.row_zero_prefix a base upto.

op row_bound8192
    (a : BArray8192.t) (base sz : int) : bool =
  TargetKeygenM23Pointwise.row_bound8192 a base sz.

op verify_matrix_slice_bound16
    (mp : BArray32768.t) (base : int) : bool =
  forall j, 0 <= j < KeygenM23MatrixSpec.poly_words_i =>
    Fq.bw32 (BArray32768.get32 mp (base + j)) 16.

op verify_mode2_matrix_repr_bound16
    (mp : BArray32768.t) : bool =
  verify_matrix_slice_bound16 mp 0 /\
  verify_matrix_slice_bound16
    mp KeygenM23MatrixSpec.poly_words_i /\
  verify_matrix_slice_bound16
    mp (2 * KeygenM23MatrixSpec.poly_words_i) /\
  verify_matrix_slice_bound16
    mp (3 * KeygenM23MatrixSpec.poly_words_i) /\
  verify_matrix_slice_bound16
    mp (4 * KeygenM23MatrixSpec.poly_words_i) /\
  verify_matrix_slice_bound16
    mp (5 * KeygenM23MatrixSpec.poly_words_i) /\
  verify_matrix_slice_bound16
    mp (6 * KeygenM23MatrixSpec.poly_words_i) /\
  verify_matrix_slice_bound16
    mp (7 * KeygenM23MatrixSpec.poly_words_i).

op verify_mode2_matrix_bound16
    (mp : BArray32768.t) : bool =
  forall i,
    0 <= i < verify_mode2_rows_i * verify_mode2_cols_i *
      KeygenM23MatrixSpec.poly_words_i =>
    Fq.bw32 (BArray32768.get32 mp i) 16.

op verify_mode2_vector_bound24
    (vp : BArray8192.t) : bool =
  forall i, 0 <= i < verify_mode2_vec_words_i =>
    Fq.bw32 (BArray8192.get32 vp i) 24.

op verify_mode2_pointwise_term
    (mp : BArray32768.t) (vp : BArray8192.t)
    (row col j : int) : coeff =
  NTT_Fq.word_to_coeff
    (BArray32768.get32 mp
      ((row * verify_mode2_cols_i + col) *
         KeygenM23MatrixSpec.poly_words_i + j)) *
  NTT_Fq.word_to_coeff
    (BArray8192.get32 vp
      (col * KeygenM23MatrixSpec.poly_words_i + j)) *
  inv NTT_Fq.R.

op verify_mode2_partial_sum
    (mp : BArray32768.t) (vp : BArray8192.t)
    (row j col : int) : coeff =
  if col = 0 then Zq.zero
  else if col = 1 then
    verify_mode2_pointwise_term mp vp row 0 j
  else if col = 2 then
    verify_mode2_pointwise_term mp vp row 0 j +
    verify_mode2_pointwise_term mp vp row 1 j
  else if col = 3 then
    (verify_mode2_pointwise_term mp vp row 0 j +
     verify_mode2_pointwise_term mp vp row 1 j) +
    verify_mode2_pointwise_term mp vp row 2 j
  else
    ((verify_mode2_pointwise_term mp vp row 0 j +
      verify_mode2_pointwise_term mp vp row 1 j) +
     verify_mode2_pointwise_term mp vp row 2 j) +
    verify_mode2_pointwise_term mp vp row 3 j.

op verify_mode2_pointwise_row_words
    (mp : BArray32768.t) (vp : BArray8192.t)
    (row : int) : Rq.poly =
  Array256.init (fun j =>
      verify_mode2_pointwise_term mp vp row 0 j
    + verify_mode2_pointwise_term mp vp row 1 j
    + verify_mode2_pointwise_term mp vp row 2 j
    + verify_mode2_pointwise_term mp vp row 3 j).

op verify_mode2_pointwise_repr_bound18
    (b : BArray8192.t) (mp : BArray32768.t)
    (vp : BArray8192.t) : bool =
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    b 0 (verify_mode2_pointwise_row_words mp vp 0) 18 /\
  KeygenM23ArithmeticSpec.wide_slice_repr_bound
    b KeygenM23MatrixSpec.poly_words_i
    (verify_mode2_pointwise_row_words mp vp 1) 18.

op verify_acc_bits (col : int) : int =
  if col = 0 then 0
  else if col = 1 then 16
  else if col = 2 then 17
  else 18.

op verify_acc_exact_ok (w : W32.t) (col : int) : bool =
  if col = 0 then w = W32.zero
  else - col * 2^16 <= W32.to_sint w < col * 2^16.

op verify_acc_word_ok (w : W32.t) (col : int) : bool =
  Fq.bw32 w (verify_acc_bits col) /\ verify_acc_exact_ok w col.

lemma verify_acc_word_ok_eq (w1 w2 : W32.t) (col : int) :
  w1 = w2 =>
  verify_acc_word_ok w1 col =>
  verify_acc_word_ok w2 col.
proof.
move=> ->.
trivial.
qed.

op verify_row_acc_ok
    (a : BArray8192.t) (base col : int) : bool =
  forall j, 0 <= j < 256 =>
    verify_acc_word_ok (BArray8192.get32 a (base + j)) col.

op verify_row_mixed_acc_ok
    (a : BArray8192.t) (base upto col : int) : bool =
  (forall j, 0 <= j < upto =>
     verify_acc_word_ok (BArray8192.get32 a (base + j)) (col + 1)) /\
  (forall j, upto <= j < 256 =>
     verify_acc_word_ok (BArray8192.get32 a (base + j)) col).

lemma verify_row_mixed_acc_ok_array_eq
    (a b : BArray8192.t) (base upto col : int) :
  a = b =>
  verify_row_mixed_acc_ok a base upto col =>
  verify_row_mixed_acc_ok b base upto col.
proof.
move=> ->.
trivial.
qed.

lemma verify_set32_add_addr
    (a : BArray8192.t) (x y : int) (w : W32.t) :
  BArray8192.set32 a (x + y) w =
  BArray8192.set32d a (4 * x + 4 * y) w.
proof.
congr.
smt().
qed.

lemma verify_get32_add_addr
    (a : BArray8192.t) (x y : int) :
  BArray8192.get32 a (x + y) =
  BArray8192.get32d a (4 * x + 4 * y).
proof.
congr.
smt().
qed.

lemma verify_acc_word_ok_get32_add_addr
    (a : BArray8192.t) (x y col : int) :
  verify_acc_word_ok (BArray8192.get32 a (x + y)) col =>
  verify_acc_word_ok
    (BArray8192.get32d a (4 * x + 4 * y)) col.
proof.
move=> h.
by rewrite -(verify_get32_add_addr a x y).
qed.

lemma verify_set32_add_update_addr
    (a : BArray8192.t) (x y : int) (w : W32.t) :
  BArray8192.set32 a (x + y) (BArray8192.get32 a (x + y) + w) =
  BArray8192.set32d a (4 * x + 4 * y)
    (BArray8192.get32d a (4 * x + 4 * y) + w).
proof.
rewrite (verify_set32_add_addr a x y
           (BArray8192.get32 a (x + y) + w)).
congr.
congr.
smt().
qed.

op verify_row_acc_sem
    (a : BArray8192.t) (mp : BArray32768.t) (vp : BArray8192.t)
    (row col : int) : bool =
  forall j, 0 <= j < 256 =>
    NTT_Fq.word_to_coeff
      (BArray8192.get32 a (256 * row + j)) =
    verify_mode2_partial_sum mp vp row j col.

op verify_row_mixed_sem
    (a : BArray8192.t) (mp : BArray32768.t) (vp : BArray8192.t)
    (row upto col : int) : bool =
  (forall j, 0 <= j < upto =>
     NTT_Fq.word_to_coeff
       (BArray8192.get32 a (256 * row + j)) =
     verify_mode2_partial_sum mp vp row j (col + 1)) /\
  (forall j, upto <= j < 256 =>
     NTT_Fq.word_to_coeff
       (BArray8192.get32 a (256 * row + j)) =
     verify_mode2_partial_sum mp vp row j col).

op verify_rows_sem
    (a : BArray8192.t) (mp : BArray32768.t) (vp : BArray8192.t)
    (upto : int) : bool =
  forall row j,
    0 <= row < upto =>
    0 <= j < 256 =>
    NTT_Fq.word_to_coeff
      (BArray8192.get32 a (256 * row + j)) =
    (verify_mode2_pointwise_row_words mp vp row).[j].

op verify_pointwise_rows_repr
    (a : BArray8192.t) (mp : BArray32768.t)
    (vp : BArray8192.t) : bool =
  KeygenM23ArithmeticSpec.wide_poly a 0 =
    verify_mode2_pointwise_row_words mp vp 0 /\
  KeygenM23ArithmeticSpec.wide_poly a 256 =
    verify_mode2_pointwise_row_words mp vp 1.

lemma verify_acc_bits_range col :
  0 <= col < verify_mode2_cols_i =>
  0 <= verify_acc_bits col < 31.
proof.
rewrite /verify_mode2_cols_i /verify_acc_bits.
smt().
qed.

lemma verify_word_to_coeff_add (a b : W32.t) (asz bsz : int) :
  0 <= asz < 31 =>
  0 <= bsz < 31 =>
  Fq.bw32 a asz =>
  Fq.bw32 b bsz =>
  NTT_Fq.word_to_coeff (a + b) =
    NTT_Fq.word_to_coeff a + NTT_Fq.word_to_coeff b.
proof.
exact (RefJasminNTT.word_to_coeff_add a b asz bsz).
qed.

lemma verify_acc_add_bound (col : int) (a b : W32.t) :
  0 <= col < verify_mode2_cols_i =>
  verify_acc_word_ok a col =>
  Fq.bw32 b 16 =>
  verify_acc_word_ok (a + b) (col + 1).
proof.
rewrite /verify_acc_word_ok /verify_acc_exact_ok /verify_acc_bits
        /Fq.bw32.
move=> hcol [hbw hacc] hb.
have hcases : col = 0 \/ col = 1 \/ col = 2 \/ col = 3 by smt().
move: hcases hbw hacc => [->|[->|[->|->]]] hbw hacc.
+ split.
  + move: hacc => ->.
    by rewrite add0z.
  move: hacc => ->.
  rewrite add0z /=.
  smt().
+ have hsum :
      W32.to_sint (a + b) =
      W32.to_sint a + W32.to_sint b.
  + rewrite W32.to_sintD_small 1:/#.
    move: hacc hb.
    smt().
  split.
  + rewrite /= hsum.
    move: hacc hb.
    smt().
  rewrite /= hsum.
  move: hacc hb.
  smt().
+ have hsum :
      W32.to_sint (a + b) =
      W32.to_sint a + W32.to_sint b.
  + rewrite W32.to_sintD_small 1:/#.
    move: hacc hb.
    smt().
  split.
  + rewrite /= hsum.
    move: hacc hb.
    smt().
  rewrite /= hsum.
  move: hacc hb.
  smt().
have hsum :
    W32.to_sint (a + b) =
    W32.to_sint a + W32.to_sint b.
+ rewrite W32.to_sintD_small 1:/#.
  move: hacc hb.
  smt().
split.
+ rewrite /= hsum.
  move: hacc hb.
  smt().
rewrite /= hsum.
move: hacc hb.
smt().
qed.

lemma verify_row_zero_prefix_to_acc0 a base :
  row_zero_prefix a base 256 =>
  verify_row_acc_ok a base 0.
proof.
rewrite /row_zero_prefix /verify_row_acc_ok
        /verify_acc_word_ok /verify_acc_bits /verify_acc_exact_ok.
move=> hzero j hj.
have -> : BArray8192.get32 a (base + j) = W32.zero
  by apply hzero.
split; last trivial.
by rewrite /Fq.bw32 W32.to_sintK_small /=.
qed.

lemma verify_row_acc_to_mixed0 a base col :
  verify_row_acc_ok a base col =>
  verify_row_mixed_acc_ok a base 0 col.
proof.
rewrite /verify_row_acc_ok /verify_row_mixed_acc_ok.
move=> h.
split.
+ smt().
move=> j hj.
by apply h; smt().
qed.

lemma verify_row_mixed_acc_step
    a base upto col w :
  0 <= base =>
  base + 256 <= KeygenM23MatrixSpec.array_words_i =>
  0 <= upto < 256 =>
  verify_row_mixed_acc_ok a base upto col =>
  verify_acc_word_ok w (col + 1) =>
  verify_row_mixed_acc_ok
    (BArray8192.set32 a (base + upto) w)
    base (upto + 1) col.
proof.
rewrite /verify_row_mixed_acc_ok.
move=> hbase hcap hupto [hdone htodo] hw.
split.
+ move=> j hj.
  rewrite BArray8192.get_set32E 1:/# 1:/#.
  case (base + upto = base + j) => heq.
  + exact hw.
  apply hdone.
  smt().
move=> j hj.
rewrite BArray8192.get_set32E 1:/# 1:/#.
have hne : base + upto <> base + j by smt().
rewrite ifF 1:/#.
apply htodo.
smt().
qed.

lemma verify_row_mixed_acc_to_next a base col :
  verify_row_mixed_acc_ok a base 256 col =>
  verify_row_acc_ok a base (col + 1).
proof.
rewrite /verify_row_mixed_acc_ok /verify_row_acc_ok.
move=> [hdone _] j hj.
by apply hdone; smt().
qed.

lemma verify_row_acc4_bound18 a base :
  verify_row_acc_ok a base verify_mode2_cols_i =>
  row_bound8192 a base 18.
proof.
rewrite /verify_row_acc_ok /row_bound8192
        /verify_acc_word_ok /verify_acc_bits /verify_mode2_cols_i.
move=> h j hj.
have := h j hj.
by smt().
qed.

lemma verify_partial_sum_succ mp vp row j col :
  0 <= col < verify_mode2_cols_i =>
  verify_mode2_partial_sum mp vp row j (col + 1) =
    verify_mode2_partial_sum mp vp row j col +
    verify_mode2_pointwise_term mp vp row col j.
proof.
move=> hcol.
have hc : col = 0 \/ col = 1 \/ col = 2 \/ col = 3 by smt().
move: hc.
move=> [->|[->|[->|->]]].
+ by rewrite /verify_mode2_partial_sum /=; ring.
+ by rewrite /verify_mode2_partial_sum /=.
+ by rewrite /verify_mode2_partial_sum /=.
by rewrite /verify_mode2_partial_sum /=.
qed.

lemma verify_partial_sum4_pointwise mp vp row j :
  0 <= j < 256 =>
  verify_mode2_partial_sum mp vp row j verify_mode2_cols_i =
    (verify_mode2_pointwise_row_words mp vp row).[j].
proof.
move=> hj.
rewrite /verify_mode2_cols_i /verify_mode2_partial_sum /verify_mode2_pointwise_row_words.
by rewrite Array256.initiE 1:/#.
qed.

lemma verify_rows_sem_set_current a mp vp row j w :
  0 <= row < 2 =>
  0 <= j < 256 =>
  verify_rows_sem a mp vp row =>
  verify_rows_sem
    (BArray8192.set32 a (256 * row + j) w)
    mp vp row.
proof.
rewrite /verify_rows_sem.
move=> hrow hj hsem r k hr hk.
rewrite BArray8192.get_set32E 1:/# 1:/#.
have hne : 256 * row + j <> 256 * r + k by smt().
rewrite ifF 1:/#.
by apply hsem.
qed.

lemma verify_row_zero_prefix_to_sem0 a mp vp row :
  row_zero_prefix a (256 * row) 256 =>
  verify_row_acc_sem a mp vp row 0.
proof.
rewrite /row_zero_prefix /verify_row_acc_sem /verify_mode2_partial_sum.
move=> hzero j hj.
rewrite (hzero j hj).
by rewrite /NTT_Fq.word_to_coeff W32.to_sintK_small.
qed.

lemma verify_row_acc_sem_to_mixed0 a mp vp row col :
  verify_row_acc_sem a mp vp row col =>
  verify_row_mixed_sem a mp vp row 0 col.
proof.
rewrite /verify_row_acc_sem /verify_row_mixed_sem.
move=> hsem.
split.
+ smt().
move=> j hj.
by apply hsem; smt().
qed.

lemma verify_row_mixed_sem_to_next a mp vp row col :
  verify_row_mixed_sem a mp vp row 256 col =>
  verify_row_acc_sem a mp vp row (col + 1).
proof.
rewrite /verify_row_mixed_sem /verify_row_acc_sem.
move=> [hdone _] j hj.
by apply hdone; smt().
qed.

lemma verify_row_mixed_sem_step a mp vp row upto col t :
  0 <= row < 2 =>
  0 <= upto < 256 =>
  0 <= col < verify_mode2_cols_i =>
  verify_row_mixed_acc_ok a (256 * row) upto col =>
  verify_row_mixed_sem a mp vp row upto col =>
  Fq.bw32 t 16 =>
  NTT_Fq.word_to_coeff t =
    verify_mode2_pointwise_term mp vp row col upto =>
  verify_row_mixed_sem
    (BArray8192.set32 a (256 * row + upto)
      (BArray8192.get32 a (256 * row + upto) + t))
    mp vp row (upto + 1) col.
proof.
move=> hrow hupto hcol.
rewrite /verify_row_mixed_acc_ok /verify_row_mixed_sem.
move=> [hbdone hbtodo] [hsdone hstodo] htb htsem.
split.
+ move=> j hj.
  rewrite BArray8192.get_set32E 1:/# 1:/#.
  case (256 * row + upto = 256 * row + j) => heq.
  + have -> : j = upto by smt().
    have hold := hbtodo upto _.
    + smt().
    move: hold => [hold _].
    rewrite
      (verify_word_to_coeff_add
        (BArray8192.get32 a (256 * row + upto)) t
        (verify_acc_bits col) 16)
      1:(verify_acc_bits_range col hcol) 1:/# 1:hold 1:htb.
    rewrite (hstodo upto) 1:/# htsem.
    by rewrite -verify_partial_sum_succ 1:hcol.
  apply hsdone.
  smt().
move=> j hj.
rewrite BArray8192.get_set32E 1:/# 1:/#.
have hne : 256 * row + upto <> 256 * row + j by smt().
rewrite ifF 1:hne.
have hsem := hstodo j _.
+ smt().
smt().
smt().
qed.

lemma verify_rows_sem_extend a mp vp row :
  0 <= row < 2 =>
  verify_rows_sem a mp vp row =>
  verify_row_acc_sem a mp vp row verify_mode2_cols_i =>
  verify_rows_sem a mp vp (row + 1).
proof.
rewrite /verify_rows_sem /verify_row_acc_sem.
move=> hrow hrows hacc r j hr hj.
case (r < row) => hlt.
+ apply hrows; smt().
have -> : r = row by smt().
rewrite -verify_partial_sum4_pointwise 1:hj.
by apply hacc.
qed.

lemma verify_rows_sem2_to_repr a mp vp :
  verify_rows_sem a mp vp 2 =>
  verify_pointwise_rows_repr a mp vp.
proof.
move=> hrows.
rewrite /verify_rows_sem in hrows.
rewrite /verify_pointwise_rows_repr.
split.
+ apply/Array256.ext_eq => j hj.
  rewrite KeygenM23ArithmeticSpec.wide_poly_get 1:/#.
  have hrow0 : 0 <= 0 < 2 by smt().
  have hj0 : 0 <= j < 256 by smt().
  have h := hrows 0 j hrow0 hj0.
  rewrite /= in h.
  exact h.
+ apply/Array256.ext_eq => j hj.
  rewrite KeygenM23ArithmeticSpec.wide_poly_get 1:/#.
  have hrow1 : 0 <= 1 < 2 by smt().
  have hj1 : 0 <= j < 256 by smt().
  have h := hrows 1 j hrow1 hj1.
  rewrite /= in h.
  exact h.
qed.

lemma verify_mode2_matrix_repr_bound16_get mp i :
  verify_mode2_matrix_repr_bound16 mp =>
  0 <= i < verify_mode2_rows_i * verify_mode2_cols_i *
    KeygenM23MatrixSpec.poly_words_i =>
  Fq.bw32 (BArray32768.get32 mp i) 16.
proof.
rewrite /verify_mode2_matrix_repr_bound16
        /verify_matrix_slice_bound16.
move=> [h0 [h1 [h2 [h3 [h4 [h5 [h6 h7]]]]]]] hi.
rewrite /verify_mode2_rows_i /verify_mode2_cols_i
        /KeygenM23MatrixSpec.poly_words_i in hi.
case (i < 256) => hi0.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp (0 + i)
    by congr; ring.
  apply h0.
  smt().
case (i < 512) => hi1.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp (256 + (i - 256))
    by congr; ring.
  apply h1.
  smt().
case (i < 768) => hi2.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp (512 + (i - 512))
    by congr; ring.
  apply h2.
  smt().
case (i < 1024) => hi3.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp (768 + (i - 768))
    by congr; ring.
  apply h3.
  smt().
case (i < 1280) => hi4.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp (1024 + (i - 1024))
    by congr; ring.
  apply h4.
  smt().
case (i < 1536) => hi5.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp (1280 + (i - 1280))
    by congr; ring.
  apply h5.
  smt().
case (i < 1792) => hi6.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp (1536 + (i - 1536))
    by congr; ring.
  apply h6.
  smt().
have -> :
    BArray32768.get32 mp i =
    BArray32768.get32 mp (1792 + (i - 1792))
  by congr; ring.
apply h7.
smt().
qed.

lemma verify_mode2_matrix_repr_bound16_to_bound mp :
  verify_mode2_matrix_repr_bound16 mp =>
  verify_mode2_matrix_bound16 mp.
proof.
move=> hmatrix.
rewrite /verify_mode2_matrix_bound16.
move=> i hi.
apply (verify_mode2_matrix_repr_bound16_get mp i).
+ exact hmatrix.
exact hi.
qed.

lemma verify_mode2_ntt_repr_bound24_to_vector4
    vp p0 p1 p2 p3 :
  verify_mode2_ntt_repr_bound24 vp p0 p1 p2 p3 =>
  verify_mode2_vector_bound24 vp.
proof.
rewrite /verify_mode2_ntt_repr_bound24
        /KeygenM23ArithmeticSpec.wide_slice_repr_bound
        /KeygenM23ArithmeticSpec.wide_slice_bound
        /verify_mode2_vector_bound24.
move=> [[_ h0] [[_ h1] [[_ h2] [_ h3]]]] i hi.
rewrite /verify_mode2_vec_words_i /verify_mode2_cols_i
        /KeygenM23MatrixSpec.poly_words_i in hi.
case (i < 256) => hi0.
+ have -> :
      BArray8192.get32 vp i =
      BArray8192.get32 vp (0 + i)
    by congr; ring.
  apply h0.
  rewrite /KeygenM23MatrixSpec.poly_words_i.
  smt().
case (i < 512) => hi1.
+ have -> :
      BArray8192.get32 vp i =
      BArray8192.get32 vp
        (KeygenM23MatrixSpec.poly_words_i + (i - 256))
    by congr; rewrite /KeygenM23MatrixSpec.poly_words_i; ring.
  apply h1.
  rewrite /KeygenM23MatrixSpec.poly_words_i.
  smt().
case (i < 768) => hi2.
+ have -> :
      BArray8192.get32 vp i =
      BArray8192.get32 vp
        (2 * KeygenM23MatrixSpec.poly_words_i + (i - 512))
    by congr; rewrite /KeygenM23MatrixSpec.poly_words_i; ring.
  apply h2.
  rewrite /KeygenM23MatrixSpec.poly_words_i.
  smt().
have -> :
    BArray8192.get32 vp i =
    BArray8192.get32 vp
      (3 * KeygenM23MatrixSpec.poly_words_i + (i - 768))
  by congr; rewrite /KeygenM23MatrixSpec.poly_words_i; ring.
apply h3.
rewrite /KeygenM23MatrixSpec.poly_words_i.
smt().
qed.

lemma verify_mode2_pointwise_rows_prefix_to_repr_bound18 a mp vp :
  verify_pointwise_rows_repr a mp vp =>
  prefix_bound8192 a 512 18 =>
  verify_mode2_pointwise_repr_bound18 a mp vp.
proof.
rewrite /verify_pointwise_rows_repr
        /verify_mode2_pointwise_repr_bound18
        /KeygenM23ArithmeticSpec.wide_slice_repr_bound
        /KeygenM23ArithmeticSpec.wide_slice_bound
        /prefix_bound8192
        /TargetKeygenM23Pointwise.prefix_bound8192.
move=> [hrow0 hrow1] hbound.
split.
+ split.
  + by rewrite hrow0.
  + move=> j hj.
    apply hbound.
    rewrite /KeygenM23MatrixSpec.poly_words_i in hj.
    rewrite /KeygenM23MatrixSpec.poly_words_i.
    smt().
+ split.
  + by rewrite /KeygenM23MatrixSpec.poly_words_i hrow1.
  + move=> j hj.
    apply hbound.
    rewrite /KeygenM23MatrixSpec.poly_words_i in hj.
    rewrite /KeygenM23MatrixSpec.poly_words_i.
    smt().
qed.

lemma parent_polymat_pointwise_acc_verify_cols4_bound18_frame
    (tp0 : BArray8192.t)
    (mp0 : BArray32768.t)
    (vp0 : BArray8192.t) :
  hoare [Parent._polymat_pointwise_acc :
    tp = tp0 /\ mp = mp0 /\ vp = vp0 /\
    rows = W64.of_int verify_mode2_rows_i /\
    cols = W64.of_int verify_mode2_cols_i /\
    verify_mode2_matrix_bound16 mp0 /\
    verify_mode2_vector_bound24 vp0
    ==>
    prefix_bound8192 res 512 18 /\
    KeygenM23MatrixSpec.word_tail_frame tp0 res 512].
proof.
proc.
while
  (mp = mp0 /\ vp = vp0 /\
   rows = W64.of_int verify_mode2_rows_i /\
   cols = W64.of_int verify_mode2_cols_i /\
   verify_mode2_matrix_bound16 mp0 /\
   verify_mode2_vector_bound24 vp0 /\
   0 <= W64.to_uint row <= verify_mode2_rows_i /\
   W64.to_uint row_out = 256 * W64.to_uint row /\
   W64.to_uint row_mat = 1024 * W64.to_uint row /\
   prefix_bound8192 tp (W64.to_uint row_out) 18 /\
   KeygenM23MatrixSpec.word_tail_frame tp0 tp 512).
+ wp.
  while
    (mp = mp0 /\ vp = vp0 /\
     rows = W64.of_int verify_mode2_rows_i /\
     cols = W64.of_int verify_mode2_cols_i /\
     verify_mode2_matrix_bound16 mp0 /\
     verify_mode2_vector_bound24 vp0 /\
     0 <= W64.to_uint row < verify_mode2_rows_i /\
     W64.to_uint row_out = 256 * W64.to_uint row /\
     W64.to_uint row_mat = 1024 * W64.to_uint row /\
     0 <= W64.to_uint col <= verify_mode2_cols_i /\
     W64.to_uint col_off = 256 * W64.to_uint col /\
     prefix_bound8192 tp (W64.to_uint row_out) 18 /\
     verify_row_acc_ok tp (W64.to_uint row_out) (W64.to_uint col) /\
     KeygenM23MatrixSpec.word_tail_frame tp0 tp 512).
  + wp.
    while
      (mp = mp0 /\ vp = vp0 /\
       rows = W64.of_int verify_mode2_rows_i /\
       cols = W64.of_int verify_mode2_cols_i /\
       verify_mode2_matrix_bound16 mp0 /\
       verify_mode2_vector_bound24 vp0 /\
       0 <= W64.to_uint row < verify_mode2_rows_i /\
       W64.to_uint row_out = 256 * W64.to_uint row /\
       W64.to_uint row_mat = 1024 * W64.to_uint row /\
       0 <= W64.to_uint col < verify_mode2_cols_i /\
       W64.to_uint col_off = 256 * W64.to_uint col /\
       0 <= W64.to_uint j <= 256 /\
       prefix_bound8192 tp (W64.to_uint row_out) 18 /\
       verify_row_mixed_acc_ok tp (W64.to_uint row_out)
         (W64.to_uint j) (W64.to_uint col) /\
       KeygenM23MatrixSpec.word_tail_frame tp0 tp 512).
    + seq 9 :
        (mp = mp0 /\ vp = vp0 /\
         rows = W64.of_int verify_mode2_rows_i /\
         cols = W64.of_int verify_mode2_cols_i /\
         verify_mode2_matrix_bound16 mp0 /\
         verify_mode2_vector_bound24 vp0 /\
         0 <= W64.to_uint row < verify_mode2_rows_i /\
         W64.to_uint row_out = 256 * W64.to_uint row /\
         W64.to_uint row_mat = 1024 * W64.to_uint row /\
         0 <= W64.to_uint col < verify_mode2_cols_i /\
         W64.to_uint col_off = 256 * W64.to_uint col /\
         0 <= W64.to_uint j < 256 /\
         prefix_bound8192 tp (W64.to_uint row_out) 18 /\
         verify_row_mixed_acc_ok tp (W64.to_uint row_out)
           (W64.to_uint j) (W64.to_uint col) /\
         KeygenM23MatrixSpec.word_tail_frame tp0 tp 512 /\
         oidx = row_out + j /\
         a = BArray32768.get32 mp0
           (W64.to_uint (row_mat + col_off + j)) /\
         b = BArray8192.get32 vp0
           (W64.to_uint (col_off + j)) /\
         Fq.bw32 a 16 /\ Fq.bw32 b 24).
      + auto => /> &hr hmp hvp hrow0 hrowlt hrowout hrowmat
                    hcol0 hcollt hcoloff hj0 hjle _ _ _ _ hguard.
        have hjlt : W64.to_uint j{hr} < 256.
        + move: hguard.
          rewrite W64.ultE W64.of_uintK /=.
          trivial.
        have hmidx :
            W64.to_uint (row_mat{hr} + col_off{hr} + j{hr}) =
            W64.to_uint row_mat{hr} +
            W64.to_uint col_off{hr} + W64.to_uint j{hr}.
        + rewrite !W64.to_uintD_small 1:/# 1:/# 1:/#.
          ring.
        have hvidx :
            W64.to_uint (col_off{hr} + j{hr}) =
            W64.to_uint col_off{hr} + W64.to_uint j{hr}.
        + rewrite W64.to_uintD_small 1:/#.
          trivial.
        split; first exact hjlt.
        split.
        + rewrite hmidx.
          apply hmp.
          rewrite hrowmat hcoloff /verify_mode2_rows_i
                  /verify_mode2_cols_i
                  /KeygenM23MatrixSpec.poly_words_i.
          smt().
        rewrite hvidx hcoloff.
        apply hvp.
        rewrite /verify_mode2_vec_words_i
                /verify_mode2_cols_i
                /KeygenM23MatrixSpec.poly_words_i.
        smt().
      + wp.
        exlim a => aa.
        exlim b => bb.
        call (TargetKeygenM23Pointwise.parent_fqmul_16_24 aa bb).
        auto => &hr hpre.
        split.
        + move: hpre.
          smt().
        move: hpre => [hbb hpre].
        move: hpre => [haa hpre].
        move: hpre => [hmp_eq hpre].
        move: hpre => [hvp_eq hpre].
        move: hpre => [hrows_eq hpre].
        move: hpre => [hcols_eq hpre].
        move: hpre => [hmatrix hpre].
        move: hpre => [hvector hpre].
        move: hpre => [hrow hpre].
        move: hpre => [hrowout hpre].
        move: hpre => [hrowmat hpre].
        move: hpre => [hcol hpre].
        move: hpre => [hcoloff hpre].
        move: hpre => [hj hpre].
        move: hpre => [hpref hpre].
        move: hpre => [hmixed hpre].
        move: hpre => [hframe hpre].
        move: hpre => [hoidx hpre].
        move: hpre => [ha_def hpre].
        move: hpre => [hb_def hpre].
        move: hpre => [ha_bound hb_bound].
        move: hrow hcol hj => [hrow0 hrowlt] [hcol0 hcollt]
                             [hj0 hjlt].
        move=> hcall result hresult.
        move: hresult => [hressem hres].
        have hjsucc :
            W64.to_uint (j{hr} + W64.one) =
            W64.to_uint j{hr} + 1.
        + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
          trivial.
        have hidx :
            W64.to_uint (row_out{hr} + j{hr}) =
            W64.to_uint row_out{hr} + W64.to_uint j{hr}.
        + rewrite W64.to_uintD_small 1:/#.
          trivial.
        have hold :
            verify_acc_word_ok
              (BArray8192.get32 tp{hr}
              (W64.to_uint row_out{hr} + W64.to_uint j{hr}))
              (W64.to_uint col{hr}).
        + have htodo :
              forall k, W64.to_uint j{hr} <= k < 256 =>
                verify_acc_word_ok
                  (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + k))
                  (W64.to_uint col{hr}).
          + move: hmixed.
            rewrite /verify_row_mixed_acc_ok.
            smt().
          apply htodo.
          smt().
        have hnew :
            verify_acc_word_ok
              (BArray8192.get32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
               result)
              (W64.to_uint col{hr} + 1).
        + apply (verify_acc_add_bound (W64.to_uint col{hr})
                   (BArray8192.get32 tp{hr}
                     (W64.to_uint row_out{hr} + W64.to_uint j{hr}))
                   result).
          + smt().
          + exact hold.
          exact hres.
        have hpref' :
            prefix_bound8192
              (BArray8192.set32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                 (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                  result))
              (W64.to_uint row_out{hr}) 18.
        + apply (TargetKeygenM23Pointwise.prefix_bound8192_set_after
                   tp{hr}
                   (W64.to_uint row_out{hr})
                   (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                   (BArray8192.get32 tp{hr}
                      (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                    result) 18).
          + smt().
          + rewrite /KeygenM23MatrixSpec.array_words_i
                    /BArray8192.size.
            smt().
          exact hpref.
        have hmixed_next :
            verify_row_mixed_acc_ok
              (BArray8192.set32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                 (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                  result))
              (W64.to_uint row_out{hr})
              (W64.to_uint j{hr} + 1) (W64.to_uint col{hr}).
        + apply (verify_row_mixed_acc_step tp{hr}
                   (W64.to_uint row_out{hr}) (W64.to_uint j{hr})
                   (W64.to_uint col{hr})
                   (BArray8192.get32 tp{hr}
                      (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                    result)).
          + smt().
          + rewrite /KeygenM23MatrixSpec.array_words_i
                    /BArray8192.size.
            smt().
          + smt().
          + exact hmixed.
          exact hnew.
        have hframe' :
            KeygenM23MatrixSpec.word_tail_frame tp0
              (BArray8192.set32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                 (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                  result)) 512.
        + apply (KeygenM23MatrixSpec.word_tail_frame_set32_before
                   tp0 tp{hr}
                   (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                   512
                   (BArray8192.get32 tp{hr}
                      (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                    result)).
          + rewrite hrowout.
            split; smt().
          + rewrite /KeygenM23MatrixSpec.array_words_i
                    /BArray8192.size.
            smt().
          exact hframe.
        rewrite (verify_set32_add_update_addr tp{hr}
                   (W64.to_uint row_out{hr})
                   (W64.to_uint j{hr}) result) in hmixed_next.
        rewrite hoidx hjsucc hidx.
        rewrite
          (_ : 4 * W64.to_uint row_out{hr} + 4 * W64.to_uint j{hr} =
               4 * (W64.to_uint row_out{hr} + W64.to_uint j{hr}))
          1:#ring in hmixed_next.
        smt().
    wp.
    skip => &hr hpre jinit.
    move: hpre => [hpre hguard].
    move: hpre => [hmp_eq hpre].
    move: hpre => [hvp_eq hpre].
    move: hpre => [hrows_eq hpre].
    move: hpre => [hcols_eq hpre].
    move: hpre => [hmatrix hpre].
    move: hpre => [hvector hpre].
    move: hpre => [hrow hpre].
    move: hpre => [hrowout hpre].
    move: hpre => [hrowmat hpre].
    move: hpre => [hcol hpre].
    move: hpre => [hcoloff hpre].
    move: hpre => [hpref hpre].
    move: hpre => [hrowacc hframe].
    move: hrow hcol => [hrow0 hrowlt] [hcol0 hcolle].
    have hcollt : W64.to_uint col{hr} < verify_mode2_cols_i.
    + move: hguard.
      rewrite W64.ultE hcols_eq W64.of_uintK
              /verify_mode2_cols_i /=.
      trivial.
    split.
    + split; first exact hmp_eq.
      split; first exact hvp_eq.
      split; first exact hrows_eq.
      split; first exact hcols_eq.
      split; first exact hmatrix.
      split; first exact hvector.
      split; first by split.
      split; first exact hrowout.
      split; first exact hrowmat.
      split; first by split.
      split; first exact hcoloff.
      split.
      + smt().
      split; first exact hpref.
      split.
      + rewrite /verify_row_mixed_acc_ok.
        split.
        + move=> k hk.
          smt().
        move=> k hk.
        apply hrowacc.
        smt().
      exact hframe.
    move=> j0 tp1 hjdone hpost.
    move: hpost => [hmp_eq1 hpost].
    move: hpost => [hvp_eq1 hpost].
    move: hpost => [hrows_eq1 hpost].
    move: hpost => [hcols_eq1 hpost].
    move: hpost => [hmatrix1 hpost].
    move: hpost => [hvector1 hpost].
    move: hpost => [hrow1 hpost].
    move: hpost => [hrowout1 hpost].
    move: hpost => [hrowmat1 hpost].
    move: hpost => [hcol1 hpost].
    move: hpost => [hcoloff1 hpost].
    move: hpost => [hj1 hpost].
    move: hpost => [hpref1 hpost].
    move: hpost => [hmixed1 hframe1].
    move: hj1 => [hj00 hj0le].
    have hjeq : W64.to_uint j0 = 256.
    + move: hjdone.
      rewrite W64.ultE W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    have hnext :
        verify_row_acc_ok tp1 (W64.to_uint row_out{hr})
          (W64.to_uint col{hr} + 1)
      by apply (verify_row_mixed_acc_to_next tp1
                  (W64.to_uint row_out{hr}) (W64.to_uint col{hr}));
         rewrite -hjeq; exact hmixed1.
    have hcolsucc :
        W64.to_uint (col{hr} + W64.one) =
        W64.to_uint col{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hoffsucc :
        W64.to_uint (col_off{hr} + W64.of_int 256) =
        W64.to_uint col_off{hr} + 256.
    + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
      trivial.
    split; first exact hmp_eq1.
    split; first exact hvp_eq1.
    split; first exact hrows_eq1.
    split; first exact hcols_eq1.
    split; first exact hmatrix1.
    split; first exact hvector1.
    split; first exact hrow1.
    split; first exact hrowout1.
    split; first exact hrowmat1.
    split.
    + rewrite hcolsucc.
      split; smt().
    split.
    + rewrite hcolsucc hoffsucc hcoloff1.
      ring.
    split; first exact hpref1.
    rewrite hcolsucc.
    split; first exact hnext.
    exact hframe1.
  wp.
  while
    (mp = mp0 /\ vp = vp0 /\
     rows = W64.of_int verify_mode2_rows_i /\
     cols = W64.of_int verify_mode2_cols_i /\
     verify_mode2_matrix_bound16 mp0 /\
     verify_mode2_vector_bound24 vp0 /\
     0 <= W64.to_uint row < verify_mode2_rows_i /\
     W64.to_uint row_out = 256 * W64.to_uint row /\
     W64.to_uint row_mat = 1024 * W64.to_uint row /\
     0 <= W64.to_uint j <= 256 /\
     prefix_bound8192 tp (W64.to_uint row_out) 18 /\
     row_zero_prefix tp (W64.to_uint row_out) (W64.to_uint j) /\
     KeygenM23MatrixSpec.word_tail_frame tp0 tp 512).
  + auto => /> &hr _ _ hrow0 hrowlt hrowout _ hj0 hjle
                hpref hzero hframe hguard.
    have hjlt : W64.to_uint j{hr} < 256.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /=.
      trivial.
    have hjsucc :
        W64.to_uint (j{hr} + W64.one) =
        W64.to_uint j{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hidx :
        W64.to_uint (row_out{hr} + j{hr}) =
        W64.to_uint row_out{hr} + W64.to_uint j{hr}.
    + rewrite W64.to_uintD_small 1:/#.
      trivial.
    have hpref' :
        prefix_bound8192
          (BArray8192.set32 tp{hr}
             (W64.to_uint row_out{hr} + W64.to_uint j{hr}) W32.zero)
          (W64.to_uint row_out{hr}) 18.
    + apply (TargetKeygenM23Pointwise.prefix_bound8192_set_after
               tp{hr}
               (W64.to_uint row_out{hr})
               (W64.to_uint row_out{hr} + W64.to_uint j{hr})
               W32.zero 18).
      + smt().
      + rewrite /KeygenM23MatrixSpec.array_words_i
                /BArray8192.size hrowout.
        smt().
      exact hpref.
    have hzero' :
        row_zero_prefix
          (BArray8192.set32 tp{hr}
             (W64.to_uint row_out{hr} + W64.to_uint j{hr}) W32.zero)
          (W64.to_uint row_out{hr}) (W64.to_uint j{hr} + 1).
    + apply (TargetKeygenM23Pointwise.row_zero_prefix_step tp{hr}
               (W64.to_uint row_out{hr}) (W64.to_uint j{hr})).
      + smt().
      + rewrite /KeygenM23MatrixSpec.array_words_i
                /BArray8192.size hrowout.
        smt().
      + smt().
      exact hzero.
    have hframe' :
        KeygenM23MatrixSpec.word_tail_frame tp0
          (BArray8192.set32 tp{hr}
             (W64.to_uint row_out{hr} + W64.to_uint j{hr}) W32.zero)
          512.
    + apply (KeygenM23MatrixSpec.word_tail_frame_set32_before
               tp0 tp{hr}
               (W64.to_uint row_out{hr} + W64.to_uint j{hr})
               512 W32.zero).
      + rewrite hrowout.
        split; smt().
      + rewrite /KeygenM23MatrixSpec.array_words_i
                /BArray8192.size.
        smt().
      exact hframe.
    rewrite hjsucc hidx.
    split.
    + split; smt().
    split.
    + exact hpref'.
    split.
    + exact hzero'.
    exact hframe'.
  wp.
  skip => /> &hr _ _ hrow0 hrowle hrowout hrowmat
                hpref hframe hguard.
  have hrowlt : W64.to_uint row{hr} < verify_mode2_rows_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /verify_mode2_rows_i /=.
    trivial.
  split.
  + split; first exact hrowlt.
    rewrite /row_zero_prefix.
    smt().
  move=> j0 tp1 hjdone _ hj00 hj0le hpref1 hzero hframe1.
  have hjeq : W64.to_uint j0 = 256.
  + move: hjdone.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hzero256 :
      row_zero_prefix tp1 (W64.to_uint row_out{hr}) 256.
  + rewrite -hjeq.
    exact hzero.
  split.
  + apply (verify_row_zero_prefix_to_acc0 tp1
             (W64.to_uint row_out{hr})).
    exact hzero256.
  move=> col0 col_off0 tp2 hcoldone hcol00 hcol0le hcoloff
          hpref2 hrowacc hframe2.
  have hcoleq : W64.to_uint col0 = verify_mode2_cols_i.
  + move: hcoldone.
    rewrite W64.ultE W64.of_uintK /verify_mode2_cols_i /=.
    smt(W64.to_uint_cmp).
  have hacc4 :
      verify_row_acc_ok tp2 (W64.to_uint row_out{hr})
        verify_mode2_cols_i.
  + rewrite -hcoleq.
    exact hrowacc.
  have hrowbound :
      row_bound8192 tp2 (W64.to_uint row_out{hr}) 18
    by apply (verify_row_acc4_bound18 tp2 (W64.to_uint row_out{hr})).
  have hprefnext :
      prefix_bound8192 tp2 (W64.to_uint row_out{hr} + 256) 18.
  + apply (TargetKeygenM23Pointwise.prefix_plus_row_bound18 tp2
             (W64.to_uint row_out{hr})).
    + smt().
    + rewrite /KeygenM23MatrixSpec.array_words_i
              /BArray8192.size hrowout.
      smt().
    + exact hpref2.
    exact hrowbound.
  have hrowsucc :
      W64.to_uint (row{hr} + W64.one) =
      W64.to_uint row{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have houtsucc :
      W64.to_uint (row_out{hr} + W64.of_int 256) =
      W64.to_uint row_out{hr} + 256.
  + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
    trivial.
  have hmatsucc :
      W64.to_uint (row_mat{hr} + col_off0) =
      W64.to_uint row_mat{hr} + W64.to_uint col_off0.
  + rewrite W64.to_uintD_small 1:/#.
    trivial.
  rewrite hrowsucc houtsucc hmatsucc hrowout hrowmat
          hcoloff hcoleq /verify_mode2_cols_i
          /KeygenM23MatrixSpec.poly_words_i.
  split.
  + split; smt().
  split.
  + ring.
  split.
  + ring.
  rewrite hrowout in hprefnext.
  exact hprefnext.
wp.
skip => /> _ _.
split.
+ rewrite /prefix_bound8192 /TargetKeygenM23Pointwise.prefix_bound8192.
  smt().
move=> row0 row_mat0 row_out0 tp1 hdone hrow0 hrowle
        hrowout _ hpref _.
have hnotlt : ! (W64.to_uint row0 < verify_mode2_rows_i).
+ move: hdone.
  rewrite W64.ultE W64.of_uintK /verify_mode2_rows_i /=.
  trivial.
have hroweq : W64.to_uint row0 = verify_mode2_rows_i by smt().
have hout : W64.to_uint row_out0 = 512 by smt().
rewrite -hout.
exact hpref.
qed.

lemma parent_polymat_pointwise_acc_verify_cols4_semantics
    (tp0 : BArray8192.t)
    (mp0 : BArray32768.t)
    (vp0 : BArray8192.t) :
  hoare [Parent._polymat_pointwise_acc :
    tp = tp0 /\ mp = mp0 /\ vp = vp0 /\
    rows = W64.of_int verify_mode2_rows_i /\
    cols = W64.of_int verify_mode2_cols_i /\
    verify_mode2_matrix_bound16 mp0 /\
    verify_mode2_vector_bound24 vp0
    ==>
    verify_pointwise_rows_repr res mp0 vp0].
proof.
proc.
while
  (mp = mp0 /\ vp = vp0 /\
   rows = W64.of_int verify_mode2_rows_i /\
   cols = W64.of_int verify_mode2_cols_i /\
   verify_mode2_matrix_bound16 mp0 /\
   verify_mode2_vector_bound24 vp0 /\
   0 <= W64.to_uint row <= verify_mode2_rows_i /\
   W64.to_uint row_out = 256 * W64.to_uint row /\
   W64.to_uint row_mat = 1024 * W64.to_uint row /\
   verify_rows_sem tp mp0 vp0 (W64.to_uint row)).
+ wp.
  while
    (mp = mp0 /\ vp = vp0 /\
     rows = W64.of_int verify_mode2_rows_i /\
     cols = W64.of_int verify_mode2_cols_i /\
     verify_mode2_matrix_bound16 mp0 /\
     verify_mode2_vector_bound24 vp0 /\
     0 <= W64.to_uint row < verify_mode2_rows_i /\
     W64.to_uint row_out = 256 * W64.to_uint row /\
     W64.to_uint row_mat = 1024 * W64.to_uint row /\
     0 <= W64.to_uint col <= verify_mode2_cols_i /\
     W64.to_uint col_off = 256 * W64.to_uint col /\
     verify_rows_sem tp mp0 vp0 (W64.to_uint row) /\
     verify_row_acc_ok tp (W64.to_uint row_out) (W64.to_uint col) /\
     verify_row_acc_sem tp mp0 vp0
       (W64.to_uint row) (W64.to_uint col)).
  + wp.
    while
      (mp = mp0 /\ vp = vp0 /\
       rows = W64.of_int verify_mode2_rows_i /\
       cols = W64.of_int verify_mode2_cols_i /\
       verify_mode2_matrix_bound16 mp0 /\
       verify_mode2_vector_bound24 vp0 /\
       0 <= W64.to_uint row < verify_mode2_rows_i /\
       W64.to_uint row_out = 256 * W64.to_uint row /\
       W64.to_uint row_mat = 1024 * W64.to_uint row /\
       0 <= W64.to_uint col < verify_mode2_cols_i /\
       W64.to_uint col_off = 256 * W64.to_uint col /\
       0 <= W64.to_uint j <= 256 /\
       verify_rows_sem tp mp0 vp0 (W64.to_uint row) /\
       verify_row_mixed_acc_ok tp (W64.to_uint row_out)
         (W64.to_uint j) (W64.to_uint col) /\
       verify_row_mixed_sem tp mp0 vp0 (W64.to_uint row)
         (W64.to_uint j) (W64.to_uint col)).
    + seq 9 :
        (mp = mp0 /\ vp = vp0 /\
         rows = W64.of_int verify_mode2_rows_i /\
         cols = W64.of_int verify_mode2_cols_i /\
         verify_mode2_matrix_bound16 mp0 /\
         verify_mode2_vector_bound24 vp0 /\
         0 <= W64.to_uint row < verify_mode2_rows_i /\
         W64.to_uint row_out = 256 * W64.to_uint row /\
         W64.to_uint row_mat = 1024 * W64.to_uint row /\
         0 <= W64.to_uint col < verify_mode2_cols_i /\
         W64.to_uint col_off = 256 * W64.to_uint col /\
         0 <= W64.to_uint j < 256 /\
         verify_rows_sem tp mp0 vp0 (W64.to_uint row) /\
         verify_row_mixed_acc_ok tp (W64.to_uint row_out)
           (W64.to_uint j) (W64.to_uint col) /\
         verify_row_mixed_sem tp mp0 vp0 (W64.to_uint row)
           (W64.to_uint j) (W64.to_uint col) /\
         oidx = row_out + j /\
         a = BArray32768.get32 mp0
           (W64.to_uint (row_mat + col_off + j)) /\
         b = BArray8192.get32 vp0
           (W64.to_uint (col_off + j)) /\
         Fq.bw32 a 16 /\ Fq.bw32 b 24).
      + auto => /> &hr hmp hvp hrow0 hrowlt hrowout hrowmat
                    hcol0 hcollt hcoloff hj0 hjle _ _ _ _ _
                    hguard.
        have hjlt : W64.to_uint j{hr} < 256.
        + move: hguard.
          rewrite W64.ultE W64.of_uintK /=.
          trivial.
        have hmidx :
            W64.to_uint (row_mat{hr} + col_off{hr} + j{hr}) =
            W64.to_uint row_mat{hr} +
            W64.to_uint col_off{hr} + W64.to_uint j{hr}.
        + rewrite !W64.to_uintD_small 1:/# 1:/# 1:/#.
          ring.
        have hvidx :
            W64.to_uint (col_off{hr} + j{hr}) =
            W64.to_uint col_off{hr} + W64.to_uint j{hr}.
        + rewrite W64.to_uintD_small 1:/#.
          trivial.
        split; first exact hjlt.
        split.
        + rewrite hmidx.
          apply hmp.
          rewrite hrowmat hcoloff /verify_mode2_rows_i
                  /verify_mode2_cols_i
                  /KeygenM23MatrixSpec.poly_words_i.
          smt().
        rewrite hvidx hcoloff.
        apply hvp.
        rewrite /verify_mode2_vec_words_i
                /verify_mode2_cols_i
                /KeygenM23MatrixSpec.poly_words_i.
        smt().
      + wp.
        exlim a => aa.
        exlim b => bb.
        call (TargetKeygenM23Pointwise.parent_fqmul_16_24 aa bb).
        auto => &hr hpre.
        split.
        + move: hpre.
          smt().
        move: hpre => [hbb hpre].
        move: hpre => [haa hpre].
        move: hpre => [hmp_eq hpre].
        move: hpre => [hvp_eq hpre].
        move: hpre => [hrows_eq hpre].
        move: hpre => [hcols_eq hpre].
        move: hpre => [hmatrix hpre].
        move: hpre => [hvector hpre].
        move: hpre => [hrow hpre].
        move: hpre => [hrowout hpre].
        move: hpre => [hrowmat hpre].
        move: hpre => [hcol hpre].
        move: hpre => [hcoloff hpre].
        move: hpre => [hj hpre].
        move: hpre => [hrows_sem hpre].
        move: hpre => [hmixed hpre].
        move: hpre => [hmixsem hpre].
        move: hpre => [hoidx hpre].
        move: hpre => [ha_def hpre].
        move: hpre => [hb_def hpre].
        move: hpre => [ha_bound hb_bound].
        move: hrow hcol hj => [hrow0 hrowlt] [hcol0 hcollt]
                             [hj0 hjlt].
        move=> hcall result hresult.
        move: hresult => [hressem hres].
        have hjsucc :
            W64.to_uint (j{hr} + W64.one) =
            W64.to_uint j{hr} + 1.
        + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
          trivial.
        have hidx :
            W64.to_uint (row_out{hr} + j{hr}) =
            W64.to_uint row_out{hr} + W64.to_uint j{hr}.
        + rewrite W64.to_uintD_small 1:/#.
          trivial.
        have hmidx :
            W64.to_uint (row_mat{hr} + col_off{hr} + j{hr}) =
            W64.to_uint row_mat{hr} +
            W64.to_uint col_off{hr} + W64.to_uint j{hr}.
        + rewrite !W64.to_uintD_small 1:/# 1:/# 1:/#.
          ring.
        have hvidx :
            W64.to_uint (col_off{hr} + j{hr}) =
            W64.to_uint col_off{hr} + W64.to_uint j{hr}.
        + rewrite W64.to_uintD_small 1:/#.
          trivial.
        have hmword :
            BArray32768.get32 mp0
              (W64.to_uint
                (row_mat{hr} + col_off{hr} + j{hr})) =
            BArray32768.get32 mp0
              (((W64.to_uint row{hr} * verify_mode2_cols_i +
                   W64.to_uint col{hr}) *
                  KeygenM23MatrixSpec.poly_words_i) +
                W64.to_uint j{hr}).
        + congr.
          rewrite hmidx hrowmat hcoloff
                  /verify_mode2_cols_i
                  /KeygenM23MatrixSpec.poly_words_i.
          ring.
        have hvword :
            BArray8192.get32 vp0
              (W64.to_uint (col_off{hr} + j{hr})) =
            BArray8192.get32 vp0
              (W64.to_uint col{hr} *
                 KeygenM23MatrixSpec.poly_words_i +
               W64.to_uint j{hr}).
        + congr.
          rewrite hvidx hcoloff
                  /KeygenM23MatrixSpec.poly_words_i.
          ring.
        have hterm :
            NTT_Fq.word_to_coeff result =
            verify_mode2_pointwise_term mp0 vp0
              (W64.to_uint row{hr}) (W64.to_uint col{hr})
              (W64.to_uint j{hr}).
        + rewrite /verify_mode2_pointwise_term.
          smt().
        have hrows0 :
            verify_rows_sem tp{hr} mp0 vp0 (W64.to_uint row{hr}).
        + exact hrows_sem.
        have hold :
            verify_acc_word_ok
              (BArray8192.get32 tp{hr}
                (W64.to_uint row_out{hr} + W64.to_uint j{hr}))
              (W64.to_uint col{hr}).
        + have htodo :
              forall k, W64.to_uint j{hr} <= k < 256 =>
                verify_acc_word_ok
                  (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + k))
                  (W64.to_uint col{hr}).
          + move: hmixed.
            rewrite /verify_row_mixed_acc_ok.
            smt().
          apply htodo.
          smt().
        have hnew :
            verify_acc_word_ok
              (BArray8192.get32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
               result)
              (W64.to_uint col{hr} + 1).
        + apply (verify_acc_add_bound (W64.to_uint col{hr})
                   (BArray8192.get32 tp{hr}
                     (W64.to_uint row_out{hr} + W64.to_uint j{hr}))
                   result).
          + smt().
          + exact hold.
          exact hres.
        have hmixed_next :
            verify_row_mixed_acc_ok
              (BArray8192.set32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                 (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                  result))
              (W64.to_uint row_out{hr})
              (W64.to_uint j{hr} + 1) (W64.to_uint col{hr}).
        + apply (verify_row_mixed_acc_step tp{hr}
                   (W64.to_uint row_out{hr}) (W64.to_uint j{hr})
                   (W64.to_uint col{hr})
                   (BArray8192.get32 tp{hr}
                      (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                    result)).
          + smt().
          + rewrite /KeygenM23MatrixSpec.array_words_i
                    /BArray8192.size.
            smt().
          + smt().
          + exact hmixed.
          exact hnew.
        have hrows_next :
            verify_rows_sem
              (BArray8192.set32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                 (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                  result))
              mp0 vp0 (W64.to_uint row{hr}).
        + rewrite hrowout.
          apply verify_rows_sem_set_current.
          + smt().
          + smt().
          exact hrows0.
        have hmixsem_next :
            verify_row_mixed_sem
              (BArray8192.set32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                 (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                  result))
              mp0 vp0 (W64.to_uint row{hr})
              (W64.to_uint j{hr} + 1) (W64.to_uint col{hr}).
        + rewrite hrowout.
          apply (verify_row_mixed_sem_step tp{hr} mp0 vp0
                   (W64.to_uint row{hr}) (W64.to_uint j{hr})
                   (W64.to_uint col{hr}) result).
          + smt().
          + smt().
          + smt().
          + rewrite -hrowout.
            exact hmixed.
          + exact hmixsem.
          + exact hres.
          exact hterm.
        rewrite (verify_set32_add_update_addr tp{hr}
                   (W64.to_uint row_out{hr})
                   (W64.to_uint j{hr}) result) in hmixed_next.
        rewrite (verify_set32_add_update_addr tp{hr}
                   (W64.to_uint row_out{hr})
                   (W64.to_uint j{hr}) result) in hrows_next.
        rewrite (verify_set32_add_update_addr tp{hr}
                   (W64.to_uint row_out{hr})
                   (W64.to_uint j{hr}) result) in hmixsem_next.
        rewrite hoidx hjsucc hidx.
        rewrite
          (_ : 4 * W64.to_uint row_out{hr} + 4 * W64.to_uint j{hr} =
               4 * (W64.to_uint row_out{hr} + W64.to_uint j{hr}))
          1:#ring in hmixed_next.
        rewrite
          (_ : 4 * W64.to_uint row_out{hr} + 4 * W64.to_uint j{hr} =
               4 * (W64.to_uint row_out{hr} + W64.to_uint j{hr}))
          1:#ring in hrows_next.
        rewrite
          (_ : 4 * W64.to_uint row_out{hr} + 4 * W64.to_uint j{hr} =
               4 * (W64.to_uint row_out{hr} + W64.to_uint j{hr}))
          1:#ring in hmixsem_next.
        smt().
    wp.
    skip => &hr hpre jinit.
    move: hpre => [hpre hguard].
    move: hpre => [hmp_eq hpre].
    move: hpre => [hvp_eq hpre].
    move: hpre => [hrows_eq hpre].
    move: hpre => [hcols_eq hpre].
    move: hpre => [hmatrix hpre].
    move: hpre => [hvector hpre].
    move: hpre => [hrow hpre].
    move: hpre => [hrowout hpre].
    move: hpre => [hrowmat hpre].
    move: hpre => [hcol hpre].
    move: hpre => [hcoloff hpre].
    move: hpre => [hrows_sem hpre].
    move: hpre => [hrowacc hrowsem].
    move: hrow hcol => [hrow0 hrowlt] [hcol0 hcolle].
    have hcollt : W64.to_uint col{hr} < verify_mode2_cols_i.
    + move: hguard.
      rewrite W64.ultE hcols_eq W64.of_uintK
              /verify_mode2_cols_i /=.
      trivial.
    split.
    + split; first exact hmp_eq.
      split; first exact hvp_eq.
      split; first exact hrows_eq.
      split; first exact hcols_eq.
      split; first exact hmatrix.
      split; first exact hvector.
      split; first by split.
      split; first exact hrowout.
      split; first exact hrowmat.
      split; first by split.
      split; first exact hcoloff.
      split.
      + smt().
      split; first exact hrows_sem.
      split.
      + rewrite /verify_row_mixed_acc_ok.
        split.
        + move=> k hk.
          smt().
        move=> k hk.
        apply hrowacc.
        smt().
      rewrite /verify_row_mixed_sem.
      split.
      + move=> k hk.
        smt().
      move=> k hk.
      apply hrowsem.
      smt().
    move=> j0 tp1 hjdone hpost.
    move: hpost => [hmp_eq1 hpost].
    move: hpost => [hvp_eq1 hpost].
    move: hpost => [hrows_eq1 hpost].
    move: hpost => [hcols_eq1 hpost].
    move: hpost => [hmatrix1 hpost].
    move: hpost => [hvector1 hpost].
    move: hpost => [hrow1 hpost].
    move: hpost => [hrowout1 hpost].
    move: hpost => [hrowmat1 hpost].
    move: hpost => [hcol1 hpost].
    move: hpost => [hcoloff1 hpost].
    move: hpost => [hj1 hpost].
    move: hpost => [hrows_sem1 hpost].
    move: hpost => [hmixed1 hmixsem1].
    move: hj1 => [hj00 hj0le].
    have hjeq : W64.to_uint j0 = 256.
    + move: hjdone.
      rewrite W64.ultE W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    have hnext :
        verify_row_acc_ok tp1 (W64.to_uint row_out{hr})
          (W64.to_uint col{hr} + 1)
      by apply (verify_row_mixed_acc_to_next tp1
                  (W64.to_uint row_out{hr}) (W64.to_uint col{hr}));
         rewrite -hjeq; exact hmixed1.
    have hsemnext :
        verify_row_acc_sem tp1 mp0 vp0 (W64.to_uint row{hr})
          (W64.to_uint col{hr} + 1)
      by apply (verify_row_mixed_sem_to_next tp1 mp0 vp0
                  (W64.to_uint row{hr}) (W64.to_uint col{hr}));
         rewrite -hjeq; exact hmixsem1.
    have hcolsucc :
        W64.to_uint (col{hr} + W64.one) =
        W64.to_uint col{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hoffsucc :
        W64.to_uint (col_off{hr} + W64.of_int 256) =
        W64.to_uint col_off{hr} + 256.
    + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
      trivial.
    split; first exact hmp_eq1.
    split; first exact hvp_eq1.
    split; first exact hrows_eq1.
    split; first exact hcols_eq1.
    split; first exact hmatrix1.
    split; first exact hvector1.
    split; first exact hrow1.
    split; first exact hrowout1.
    split; first exact hrowmat1.
    split.
    + rewrite hcolsucc.
      split; smt().
    split.
    + rewrite hcolsucc hoffsucc hcoloff1.
      ring.
    split; first exact hrows_sem1.
    split.
    + rewrite hcolsucc.
      exact hnext.
    rewrite hcolsucc.
    exact hsemnext.
  wp.
  while
    (mp = mp0 /\ vp = vp0 /\
     rows = W64.of_int verify_mode2_rows_i /\
     cols = W64.of_int verify_mode2_cols_i /\
     verify_mode2_matrix_bound16 mp0 /\
     verify_mode2_vector_bound24 vp0 /\
     0 <= W64.to_uint row < verify_mode2_rows_i /\
     W64.to_uint row_out = 256 * W64.to_uint row /\
     W64.to_uint row_mat = 1024 * W64.to_uint row /\
     0 <= W64.to_uint j <= 256 /\
     verify_rows_sem tp mp0 vp0 (W64.to_uint row) /\
     row_zero_prefix tp (W64.to_uint row_out) (W64.to_uint j)).
  + auto => /> &hr _ _ hrow0 hrowlt hrowout _ hj0 hjle
                hrows hzero hguard.
    have hjlt : W64.to_uint j{hr} < 256.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /=.
      trivial.
    have hjsucc :
        W64.to_uint (j{hr} + W64.one) =
        W64.to_uint j{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hidx :
        W64.to_uint (row_out{hr} + j{hr}) =
        W64.to_uint row_out{hr} + W64.to_uint j{hr}.
    + rewrite W64.to_uintD_small 1:/#.
      trivial.
    have hrows0 :
        verify_rows_sem tp{hr} mp0 vp0 (W64.to_uint row{hr}).
    + rewrite /verify_rows_sem.
      exact hrows.
    have hrows' :
        verify_rows_sem
          (BArray8192.set32 tp{hr}
             (W64.to_uint row_out{hr} + W64.to_uint j{hr}) W32.zero)
          mp0 vp0 (W64.to_uint row{hr}).
    + rewrite hrowout.
      apply verify_rows_sem_set_current.
      + smt().
      + smt().
      exact hrows0.
    have hzero' :
        row_zero_prefix
          (BArray8192.set32 tp{hr}
             (W64.to_uint row_out{hr} + W64.to_uint j{hr}) W32.zero)
          (W64.to_uint row_out{hr}) (W64.to_uint j{hr} + 1).
    + apply (TargetKeygenM23Pointwise.row_zero_prefix_step tp{hr}
               (W64.to_uint row_out{hr}) (W64.to_uint j{hr})).
      + smt().
      + rewrite /KeygenM23MatrixSpec.array_words_i
                /BArray8192.size hrowout.
        smt().
      + smt().
      exact hzero.
    rewrite hjsucc hidx.
    split.
    + split; smt().
    split.
    + exact hrows'.
    exact hzero'.
  wp.
  skip => /> &hr _ _ hrow0 hrowle hrowout hrowmat
                hrows hguard.
  have hrowlt : W64.to_uint row{hr} < verify_mode2_rows_i.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /verify_mode2_rows_i /=.
    trivial.
  split.
  + split; first exact hrowlt.
    rewrite /row_zero_prefix.
    smt().
  move=> j0 tp1 hjdone _ hj00 hj0le hrows1 hzero.
  have hjeq : W64.to_uint j0 = 256.
  + move: hjdone.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hzero256 :
      row_zero_prefix tp1 (W64.to_uint row_out{hr}) 256.
  + rewrite -hjeq.
    exact hzero.
  have hacc0 :
      verify_row_acc_ok tp1 (W64.to_uint row_out{hr}) 0.
  + apply (verify_row_zero_prefix_to_acc0 tp1
             (W64.to_uint row_out{hr})).
    exact hzero256.
  have hsem0 :
      verify_row_acc_sem tp1 mp0 vp0 (W64.to_uint row{hr}) 0.
  + apply (verify_row_zero_prefix_to_sem0 tp1 mp0 vp0
             (W64.to_uint row{hr})).
    rewrite -hrowout.
    exact hzero256.
  split.
  + split.
    + exact hacc0.
    exact hsem0.
  move=> col0 col_off0 tp2 hcoldone hcol00 hcol0le hcoloff
          hrows2 hrowacc hrowsem.
  have hcoleq : W64.to_uint col0 = verify_mode2_cols_i.
  + move: hcoldone.
    rewrite W64.ultE W64.of_uintK /verify_mode2_cols_i /=.
    smt(W64.to_uint_cmp).
  have hrows0 :
      verify_rows_sem tp2 mp0 vp0 (W64.to_uint row{hr}).
  + rewrite /verify_rows_sem.
    exact hrows2.
  have hsem4 :
      verify_row_acc_sem tp2 mp0 vp0 (W64.to_uint row{hr})
        verify_mode2_cols_i.
  + rewrite -hcoleq.
    exact hrowsem.
  have hrowsnext :
      verify_rows_sem tp2 mp0 vp0 (W64.to_uint row{hr} + 1).
  + apply verify_rows_sem_extend.
    + smt().
    + exact hrows0.
    exact hsem4.
  have hrowsucc :
      W64.to_uint (row{hr} + W64.one) =
      W64.to_uint row{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have houtsucc :
      W64.to_uint (row_out{hr} + W64.of_int 256) =
      W64.to_uint row_out{hr} + 256.
  + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
    trivial.
  have hmatsucc :
      W64.to_uint (row_mat{hr} + col_off0) =
      W64.to_uint row_mat{hr} + W64.to_uint col_off0.
  + rewrite W64.to_uintD_small 1:/#.
    trivial.
  rewrite hrowsucc houtsucc hmatsucc hrowout hrowmat
          hcoloff hcoleq /verify_mode2_cols_i
          /KeygenM23MatrixSpec.poly_words_i.
  split.
  + split; smt().
  split.
  + ring.
  split.
  + ring.
  exact hrowsnext.
wp.
skip => /> _ _.
split.
+ rewrite /verify_rows_sem.
  smt().
move=> row0 row_mat0 row_out0 tp1 hdone hrow0 hrowle
        hrowout hrowmat hrows.
have hnotlt : ! (W64.to_uint row0 < verify_mode2_rows_i).
+ move: hdone.
  rewrite W64.ultE W64.of_uintK /verify_mode2_rows_i /=.
  trivial.
have hroweq : W64.to_uint row0 = verify_mode2_rows_i by smt().
have hrows2 : verify_rows_sem tp1 mp0 vp0 verify_mode2_rows_i.
+ rewrite /verify_rows_sem.
  move=> r j hr hj.
  apply hrows.
  + rewrite hroweq.
    exact hr.
  exact hj.
have hrepr : verify_pointwise_rows_repr tp1 mp0 vp0.
+ apply (verify_rows_sem2_to_repr tp1 mp0 vp0).
  exact hrows2.
rewrite /verify_pointwise_rows_repr in hrepr.
exact hrepr.
qed.

lemma parent_polymat_pointwise_acc_verify_cols4_local_spec
    (tp0 : BArray8192.t)
    (mp0 : BArray32768.t)
    (vp0 : BArray8192.t) :
  hoare [Parent._polymat_pointwise_acc :
    tp = tp0 /\ mp = mp0 /\ vp = vp0 /\
    rows = W64.of_int verify_mode2_rows_i /\
    cols = W64.of_int verify_mode2_cols_i /\
    verify_mode2_matrix_bound16 mp0 /\
    verify_mode2_vector_bound24 vp0
    ==>
    prefix_bound8192 res 512 18 /\
    KeygenM23MatrixSpec.word_tail_frame tp0 res 512 /\
    verify_pointwise_rows_repr res mp0 vp0].
proof.
conseq
  (parent_polymat_pointwise_acc_verify_cols4_bound18_frame tp0 mp0 vp0)
  (parent_polymat_pointwise_acc_verify_cols4_semantics tp0 mp0 vp0) => />.
qed.

lemma parent_polymat_pointwise_acc_verify_cols4_correct
    (tp0 : BArray8192.t)
    (mp0 : BArray32768.t)
    (vp0 : BArray8192.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [Parent._polymat_pointwise_acc :
    tp = tp0 /\ mp = mp0 /\ vp = vp0 /\
    rows = W64.of_int verify_mode2_rows_i /\
    cols = W64.of_int verify_mode2_cols_i /\
    verify_mode2_matrix_repr_bound16 mp0 /\
    verify_mode2_ntt_repr_bound24 vp0 p0 p1 p2 p3
    ==>
    verify_mode2_pointwise_repr_bound18 res mp0 vp0 /\
    KeygenM23MatrixSpec.word_tail_frame tp0 res 512].
proof.
conseq
  (parent_polymat_pointwise_acc_verify_cols4_local_spec tp0 mp0 vp0).
+ move=> &hr hpre.
  move: hpre => [htp hpre].
  move: hpre => [hmp hpre].
  move: hpre => [hvp hpre].
  move: hpre => [hrows hpre].
  move: hpre => [hcols hpre].
  move: hpre => [hmatrix hntt].
  have hmatrix_bound : verify_mode2_matrix_bound16 mp0.
  + apply (verify_mode2_matrix_repr_bound16_to_bound mp0).
    exact hmatrix.
  have hvector_bound : verify_mode2_vector_bound24 vp0.
  + apply (verify_mode2_ntt_repr_bound24_to_vector4
             vp0 p0 p1 p2 p3).
    exact hntt.
  rewrite /verify_mode2_matrix_bound16 /Fq.bw32 in hmatrix_bound.
  rewrite /verify_mode2_vector_bound24 /Fq.bw32 in hvector_bound.
  split; first exact htp.
  split; first exact hmp.
  split; first exact hvp.
  split; first exact hrows.
  split; first exact hcols.
  smt().
move=> &hr _ result hpost_local.
move: hpost_local => [hprefix hpost_local].
move: hpost_local => [hframe hrows_repr].
have hpost :
    verify_mode2_pointwise_repr_bound18
      result mp0 vp0.
+ apply
    (verify_mode2_pointwise_rows_prefix_to_repr_bound18
      result mp0 vp0).
  + exact hrows_repr.
  exact hprefix.
split.
+ exact hpost.
exact hframe.
qed.

lemma verify_polymat_pointwise_acc_verify_cols4_correct
    (tp0 : BArray8192.t)
    (mp0 : BArray32768.t)
    (vp0 : BArray8192.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [Verify._polymat_pointwise_acc :
    tp = tp0 /\ mp = mp0 /\ vp = vp0 /\
    rows = W64.of_int verify_mode2_rows_i /\
    cols = W64.of_int verify_mode2_cols_i /\
    verify_mode2_matrix_repr_bound16 mp0 /\
    verify_mode2_ntt_repr_bound24 vp0 p0 p1 p2 p3
    ==>
    verify_mode2_pointwise_repr_bound18 res mp0 vp0 /\
    KeygenM23MatrixSpec.word_tail_frame tp0 res 512].
proof.
by conseq verify_polymat_pointwise_acc_equiv_parent
  (parent_polymat_pointwise_acc_verify_cols4_correct
     tp0 mp0 vp0 p0 p1 p2 p3) => /#.
qed.

lemma parent_polyvec_invntt_verify_cols4_correct18
    (xp0 : BArray8192.t)
    (mp0 : BArray32768.t)
    (vp0 : BArray8192.t) :
  hoare [Parent._polyvec_invntt :
    xp = xp0 /\
    count = W64.of_int verify_mode2_rows_i /\
    verify_mode2_pointwise_repr_bound18 xp0 mp0 vp0
    ==>
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res 0
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt
            (verify_mode2_pointwise_row_words mp0 vp0 0))) 16 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res KeygenM23MatrixSpec.poly_words_i
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt
            (verify_mode2_pointwise_row_words mp0 vp0 1))) 16 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_mode2_out_words_i].
proof.
have h :=
  TargetKeygenM23WideInvNTT.polyvec_invntt_mode2_correct18 xp0
    (verify_mode2_pointwise_row_words mp0 vp0 0)
    (verify_mode2_pointwise_row_words mp0 vp0 1).
by conseq h => /#; rewrite /verify_mode2_pointwise_repr_bound18.
qed.

lemma verify_polyvec_invntt_verify_cols4_correct18
    (xp0 : BArray8192.t)
    (mp0 : BArray32768.t)
    (vp0 : BArray8192.t) :
  hoare [Verify._polyvec_invntt :
    xp = xp0 /\
    count = W64.of_int verify_mode2_rows_i /\
    verify_mode2_pointwise_repr_bound18 xp0 mp0 vp0
    ==>
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res 0
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt
            (verify_mode2_pointwise_row_words mp0 vp0 0))) 16 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res KeygenM23MatrixSpec.poly_words_i
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt
            (verify_mode2_pointwise_row_words mp0 vp0 1))) 16 /\
    KeygenM23MatrixSpec.word_tail_frame
      xp0 res verify_mode2_out_words_i].
proof.
by conseq verify_polyvec_invntt_equiv_parent
  (parent_polyvec_invntt_verify_cols4_correct18 xp0 mp0 vp0) => /#.
qed.

lemma verify_matrix_ntt_acc_mode2_cols4_spectral_correct
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [ActualVerifyMatrixNttAccMode2.run :
    z1p = z10 /\ highp = high0 /\ a1p = a10 /\
    verify_mode2_input_repr_bound16 z10 p0 p1 p2 p3 /\
    verify_mode2_matrix_repr_bound16 a10
    ==>
    NTTRowProductSpec.vector_forward_repr
      verify_mode2_cols_i
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          res.`1 (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          z10 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res.`2 0
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt
            (verify_mode2_pointwise_row_words a10 res.`1 0))) 16 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res.`2 KeygenM23MatrixSpec.poly_words_i
        (NTT_Fq.array256_mont
          (NTTFullSpec.full_invntt
            (verify_mode2_pointwise_row_words a10 res.`1 1))) 16 /\
    KeygenM23MatrixSpec.word_tail_frame
      z10 res.`1 verify_mode2_vec_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      high0 res.`2 verify_mode2_out_words_i].
proof.
proc.
seq 5 :
  (highp = high0 /\ a1p = a10 /\
   verify_mode2_matrix_repr_bound16 a10 /\
   verify_mode2_ntt_repr_bound24 z1p p0 p1 p2 p3 /\
   NTTRowProductSpec.vector_forward_repr
     verify_mode2_cols_i
     (fun col =>
       KeygenM23ArithmeticSpec.wide_poly
         z1p (col * KeygenM23MatrixSpec.poly_words_i))
     (fun col =>
       KeygenM23ArithmeticSpec.wide_poly
         z10 (col * KeygenM23MatrixSpec.poly_words_i)) /\
   KeygenM23MatrixSpec.word_tail_frame
     z10 z1p verify_mode2_vec_words_i).
+ wp.
  call (verify_polyvec_ntt_verify_cols4_full_correct z10 p0 p1 p2 p3).
  auto => />.
exlim z1p => transformed.
seq 2 :
  (z1p = transformed /\ a1p = a10 /\
   NTTRowProductSpec.vector_forward_repr
     verify_mode2_cols_i
     (fun col =>
       KeygenM23ArithmeticSpec.wide_poly
         z1p (col * KeygenM23MatrixSpec.poly_words_i))
     (fun col =>
       KeygenM23ArithmeticSpec.wide_poly
         z10 (col * KeygenM23MatrixSpec.poly_words_i)) /\
   KeygenM23MatrixSpec.word_tail_frame
     z10 z1p verify_mode2_vec_words_i /\
   verify_mode2_pointwise_repr_bound18 highp a10 z1p /\
   KeygenM23MatrixSpec.word_tail_frame
     high0 highp verify_mode2_out_words_i).
+ wp.
  call
    (verify_polymat_pointwise_acc_verify_cols4_correct
      high0 a10 transformed p0 p1 p2 p3).
  auto => />.
exlim highp => pointwise.
wp.
call
  (verify_polyvec_invntt_verify_cols4_correct18
    pointwise a10 transformed).
auto => />.
move=> hforward htail_ntt
        hrow0 hbound0 hrow1 hbound1 htail_pointwise
        result
        hout0_eq hout0_bound hout1_eq hout1_bound htail_inv.
exact
  (KeygenM23MatrixSpec.word_tail_frame_trans
    high0 pointwise result verify_mode2_out_words_i
    htail_pointwise htail_inv).
qed.

op verify_mode2_matrix_hat4
    (m : BArray32768.t) (row col : int) : Rq.poly =
  Array256.init (fun j =>
    NTT_Fq.word_to_coeff
      (BArray32768.get32 m
        ((row * verify_mode2_cols_i + col) *
           KeygenM23MatrixSpec.poly_words_i + j))).

op verify_mode2_vector_words4
    (v : BArray8192.t) (col : int) : Rq.poly =
  KeygenM23ArithmeticSpec.wide_poly
    v (col * KeygenM23MatrixSpec.poly_words_i).

lemma verify_mode2_matrix_hat4_get m row col j :
  0 <= j < 256 =>
  (verify_mode2_matrix_hat4 m row col).[j] =
  NTT_Fq.word_to_coeff
    (BArray32768.get32 m
      ((row * verify_mode2_cols_i + col) *
         KeygenM23MatrixSpec.poly_words_i + j)).
proof.
move=> hj.
by rewrite /verify_mode2_matrix_hat4 Array256.initiE.
qed.

lemma verify_mode2_vector_words4_get v col j :
  0 <= j < 256 =>
  (verify_mode2_vector_words4 v col).[j] =
  NTT_Fq.word_to_coeff
    (BArray8192.get32 v
      (col * KeygenM23MatrixSpec.poly_words_i + j)).
proof.
move=> hj.
rewrite /verify_mode2_vector_words4.
exact (KeygenM23ArithmeticSpec.wide_poly_get
  v (col * KeygenM23MatrixSpec.poly_words_i) j hj).
qed.

lemma verify_mode2_pointwise_row_words_shared m v row :
  verify_mode2_pointwise_row_words m v row =
  NTTRowProductSpec.pointwise_row_hat
    verify_mode2_cols_i
    (verify_mode2_matrix_hat4 m)
    (verify_mode2_vector_words4 v) row.
proof.
apply Array256.ext_eq => j hj.
rewrite /verify_mode2_pointwise_row_words Array256.initiE 1:hj.
rewrite NTTRowProductSpec.pointwise_row_hat_get 1:hj.
rewrite /verify_mode2_cols_i.
rewrite /Rq.BigDom.BAdd.big /range /= filter_predT foldr_map.
rewrite (@iotaS 0 3) 1:/# /=
        (@iotaS 1 2) 1:/# /=
        (@iotaS 2 1) 1:/# /=
        (@iotaS 3 0) 1:/# /=
        (@iota0 4 0) 1:/# /=.
rewrite !verify_mode2_matrix_hat4_get 1:hj 1:hj 1:hj 1:hj.
rewrite !verify_mode2_vector_words4_get 1:hj 1:hj 1:hj 1:hj.
rewrite /verify_mode2_pointwise_term /verify_mode2_cols_i.
ring.
qed.

op verify_mode2_coefficient_row_product
    (m : BArray32768.t) (v : BArray8192.t)
    (row : int) : Rq.poly =
  NTTRowProductSpec.coefficient_row_product
    verify_mode2_cols_i
    (fun r col =>
      NTTFullSpec.full_invntt (verify_mode2_matrix_hat4 m r col))
    (verify_mode2_vector_words4 v) row.

lemma verify_mode2_inverse_pointwise_row_product m transformed input row :
  NTTRowProductSpec.vector_forward_repr
    verify_mode2_cols_i
    (verify_mode2_vector_words4 transformed)
    (verify_mode2_vector_words4 input) =>
  NTT_Fq.array256_mont
    (NTTFullSpec.full_invntt
      (verify_mode2_pointwise_row_words m transformed row)) =
  verify_mode2_coefficient_row_product m input row.
proof.
move=> hforward.
rewrite -/NTTRowProductSpec.inverse_row.
rewrite verify_mode2_pointwise_row_words_shared.
rewrite (NTTRowProductSpec.pointwise_row_from_forward_repr
  verify_mode2_cols_i
  (verify_mode2_matrix_hat4 m)
  (verify_mode2_vector_words4 transformed)
  (verify_mode2_vector_words4 input) row hforward).
rewrite /verify_mode2_coefficient_row_product.
exact (NTTFullSpectralAction.full_ntt_montgomery_row_product
  verify_mode2_cols_i
  (verify_mode2_matrix_hat4 m)
  (verify_mode2_vector_words4 input) row).
qed.

lemma verify_matrix_ntt_acc_mode2_cols4_correct
    (z10 high0 : BArray8192.t)
    (a10 : BArray32768.t)
    (p0 p1 p2 p3 : Rq.poly) :
  hoare [ActualVerifyMatrixNttAccMode2.run :
    z1p = z10 /\ highp = high0 /\ a1p = a10 /\
    verify_mode2_input_repr_bound16 z10 p0 p1 p2 p3 /\
    verify_mode2_matrix_repr_bound16 a10
    ==>
    NTTRowProductSpec.vector_forward_repr
      verify_mode2_cols_i
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          res.`1 (col * KeygenM23MatrixSpec.poly_words_i))
      (fun col =>
        KeygenM23ArithmeticSpec.wide_poly
          z10 (col * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res.`2 0
        (verify_mode2_coefficient_row_product a10 z10 0) 16 /\
    KeygenM23ArithmeticSpec.wide_slice_repr_bound
      res.`2 KeygenM23MatrixSpec.poly_words_i
        (verify_mode2_coefficient_row_product a10 z10 1) 16 /\
    KeygenM23MatrixSpec.word_tail_frame
      z10 res.`1 verify_mode2_vec_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      high0 res.`2 verify_mode2_out_words_i].
proof.
conseq
  (verify_matrix_ntt_acc_mode2_cols4_spectral_correct
    z10 high0 a10 p0 p1 p2 p3) => //=.
move=> &m _ result
        [hforward [hout0 [hout1 [htail_ntt htail_out]]]].
have hforward4 :
    NTTRowProductSpec.vector_forward_repr
      verify_mode2_cols_i
      (verify_mode2_vector_words4 result.`1)
      (verify_mode2_vector_words4 z10).
+ exact hforward.
move: hout0; rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
move=> [hout0_eq hout0_bound].
move: hout1; rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
move=> [hout1_eq hout1_bound].
split; first exact hforward.
split.
+ rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  split.
  + rewrite -hout0_eq.
    apply eq_sym.
    apply
      (verify_mode2_inverse_pointwise_row_product
        a10 result.`1 z10 0).
    exact hforward4.
  exact hout0_bound.
split.
+ rewrite /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  split.
  + rewrite -hout1_eq.
    apply eq_sym.
    apply
      (verify_mode2_inverse_pointwise_row_product
        a10 result.`1 z10 1).
    exact hforward4.
  exact hout1_bound.
split; first exact htail_ntt.
exact htail_out.
qed.

end VerifyMatrixCrtPostFreeze.
