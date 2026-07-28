require import AllCore IntDiv Ring StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenMode2ParentTarget KeygenM23MatrixSpec
               KeygenM23ArithmeticSpec.
require import Array256 Fq GFq Rq NTT_Fq Hpoly_loop RefJasminNTTLoop.

import Zq IntOrder.

theory TargetKeygenM23Pointwise.

module Parent = KeygenMode2ParentTarget.M.
module Loop = Hpoly_loop.M.

op matrix6_bound16 (mp : BArray32768.t) : bool =
  forall i, 0 <= i < 6 * 256 =>
    Fq.bw32 (BArray32768.get32 mp i) 16.

op vector3_bound24 (vp : BArray8192.t) : bool =
  forall i, 0 <= i < 3 * 256 =>
    Fq.bw32 (BArray8192.get32 vp i) 24.

op prefix_bound8192
    (a : BArray8192.t) (words sz : int) : bool =
  forall i, 0 <= i < words =>
    Fq.bw32 (BArray8192.get32 a i) sz.

op row_bound8192
    (a : BArray8192.t) (base sz : int) : bool =
  forall j, 0 <= j < 256 =>
    Fq.bw32 (BArray8192.get32 a (base + j)) sz.

op row_mixed_bound8192
    (a : BArray8192.t) (base upto oldsz newsz : int) : bool =
  forall j, 0 <= j < 256 =>
    Fq.bw32 (BArray8192.get32 a (base + j))
      (if j < upto then newsz else oldsz).

op acc_bits (col : int) : int =
  if col = 0 then 0 else 15 + col.

op acc_word_ok (w : W32.t) (col : int) : bool =
  Fq.bw32 w (acc_bits col) /\
  (col = 0 => w = W32.zero).

op row_acc_ok
    (a : BArray8192.t) (base col : int) : bool =
  forall j, 0 <= j < 256 =>
    acc_word_ok (BArray8192.get32 a (base + j)) col.

op row_mixed_acc_ok
    (a : BArray8192.t) (base upto col : int) : bool =
  (forall j, 0 <= j < upto =>
     acc_word_ok (BArray8192.get32 a (base + j)) (col + 1)) /\
  (forall j, upto <= j < 256 =>
     acc_word_ok (BArray8192.get32 a (base + j)) col).

lemma parent_fqmul_loop_equiv :
  equiv [Parent.__fqmul ~ Loop.__fqmul :
    ={a, b} ==> ={res}].
proof.
proc.
inline {2} Hpoly_loop.M.__fqmul.
inline {2} Hpoly_extract.M.__fqmul.
sim.
qed.

lemma loop_fqmul_16_24 (aa bb : W32.t) :
  hoare [Loop.__fqmul :
    a = aa /\ b = bb /\
    Fq.bw32 aa 16 /\ Fq.bw32 bb 24
    ==>
    NTT_Fq.word_to_coeff res =
      NTT_Fq.word_to_coeff aa *
      NTT_Fq.word_to_coeff bb * inv NTT_Fq.R /\
    Fq.bw32 res 16].
proof.
conseq
  (RefJasminNTT.fqmul_word_to_coeff_mul_bound_h
     (W32.to_sint aa) (W32.to_sint bb)).
+ move=> &hr [-> [-> [haa hbb]]].
  split; first trivial.
  split; first trivial.
  exact (RefJasminNTT.fqmul_product_bound_16_24 aa bb haa hbb).
move=> &hr _ result [hsem hbound] /=.
split; last exact hbound.
exact hsem.
qed.

lemma parent_fqmul_16_24 (aa bb : W32.t) :
  hoare [Parent.__fqmul :
    a = aa /\ b = bb /\
    Fq.bw32 aa 16 /\ Fq.bw32 bb 24
    ==>
    NTT_Fq.word_to_coeff res =
      NTT_Fq.word_to_coeff aa *
      NTT_Fq.word_to_coeff bb * inv NTT_Fq.R /\
    Fq.bw32 res 16].
proof.
by conseq parent_fqmul_loop_equiv (loop_fqmul_16_24 aa bb) => /#.
qed.

lemma acc_add_bound (col : int) (a b : W32.t) :
  0 <= col < 3 =>
  acc_word_ok a col =>
  Fq.bw32 b 16 =>
  acc_word_ok (a + b) (col + 1).
proof.
move=> hcol [ha hzero] hb.
split.
+ case (col = 0) => h0.
  + subst col.
    rewrite /acc_bits /= in ha.
    rewrite /acc_bits /=.
    by rewrite (hzero _).
  case (col = 1) => h1.
  + subst col.
    rewrite /acc_bits /= in ha.
    rewrite /acc_bits /=.
    exact (Fq.add_corr a b 16 16 _ _ ha hb); smt().
  have h2 : col = 2 by smt().
  subst col.
  rewrite /acc_bits /= in ha.
  rewrite /acc_bits /=.
  exact (Fq.add_corr a b 17 16 _ _ ha hb); smt().
+ smt().
qed.

lemma prefix_bound8192_zero :
  prefix_bound8192 witness 0 18.
proof.
rewrite /prefix_bound8192.
smt().
qed.

op row_zero_prefix
    (a : BArray8192.t) (base upto : int) : bool =
  forall j, 0 <= j < upto =>
    BArray8192.get32 a (base + j) = W32.zero.

lemma prefix_bound8192_set_after
    a prefix idx w sz :
  0 <= prefix <= idx =>
  idx < KeygenM23MatrixSpec.array_words_i =>
  prefix_bound8192 a prefix sz =>
  prefix_bound8192 (BArray8192.set32 a idx w) prefix sz.
proof.
rewrite /prefix_bound8192.
move=> hp hidx hbound i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
have hne : idx <> i by smt().
by rewrite ifF 1:/#; apply hbound.
qed.

lemma row_zero_prefix_step
    a base upto :
  0 <= base =>
  base + 256 <= KeygenM23MatrixSpec.array_words_i =>
  0 <= upto < 256 =>
  row_zero_prefix a base upto =>
  row_zero_prefix
    (BArray8192.set32 a (base + upto) W32.zero)
    base (upto + 1).
proof.
rewrite /row_zero_prefix.
move=> hbase hcap hupto hzero j hj.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (base + upto = base + j) => heq.
+ trivial.
apply hzero.
smt().
qed.

lemma row_zero_prefix_to_acc0 a base :
  row_zero_prefix a base 256 =>
  row_acc_ok a base 0.
proof.
rewrite /row_zero_prefix /row_acc_ok /acc_word_ok /acc_bits.
move=> hzero j hj.
have -> : BArray8192.get32 a (base + j) = W32.zero
  by apply hzero.
split; last trivial.
by rewrite /Fq.bw32 W32.to_sintK_small /=.
qed.

lemma row_acc_to_mixed0 a base col :
  row_acc_ok a base col =>
  row_mixed_acc_ok a base 0 col.
proof.
rewrite /row_acc_ok /row_mixed_acc_ok.
move=> h.
split.
+ smt().
move=> j hj.
by apply h; smt().
qed.

lemma row_mixed_acc_step
    a base upto col w :
  0 <= base =>
  base + 256 <= KeygenM23MatrixSpec.array_words_i =>
  0 <= upto < 256 =>
  row_mixed_acc_ok a base upto col =>
  acc_word_ok w (col + 1) =>
  row_mixed_acc_ok
    (BArray8192.set32 a (base + upto) w)
    base (upto + 1) col.
proof.
rewrite /row_mixed_acc_ok.
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

lemma row_mixed_acc_to_next a base col :
  row_mixed_acc_ok a base 256 col =>
  row_acc_ok a base (col + 1).
proof.
rewrite /row_mixed_acc_ok /row_acc_ok.
move=> [hdone _] j hj.
by apply hdone; smt().
qed.

lemma row_acc3_bound18 a base :
  row_acc_ok a base 3 =>
  row_bound8192 a base 18.
proof.
rewrite /row_acc_ok /row_bound8192 /acc_word_ok /acc_bits.
move=> h j hj.
have := h j hj.
by move=> [hbound _].
qed.

lemma prefix_plus_row_bound18 a base :
  0 <= base =>
  base + 256 <= KeygenM23MatrixSpec.array_words_i =>
  prefix_bound8192 a base 18 =>
  row_bound8192 a base 18 =>
  prefix_bound8192 a (base + 256) 18.
proof.
rewrite /prefix_bound8192 /row_bound8192.
move=> hbase hcap hprefix hrow i hi.
case (i < base) => hlt.
+ have hi0 : 0 <= i < base by smt().
  exact (hprefix i hi0).
have hoff : 0 <= i - base < 256 by smt().
have h := hrow (i - base) hoff.
have -> : i = base + (i - base) by ring.
exact h.
qed.

lemma polymat_pointwise_mode2_bound18_frame
    (tp0 : BArray8192.t)
    (mp0 : BArray32768.t)
    (vp0 : BArray8192.t) :
  hoare [Parent._polymat_pointwise_acc :
    tp = tp0 /\ mp = mp0 /\ vp = vp0 /\
    rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
    matrix6_bound16 mp0 /\ vector3_bound24 vp0
    ==>
    prefix_bound8192 res 512 18 /\
    KeygenM23MatrixSpec.word_tail_frame tp0 res 512].
proof.
proc.
while
  (mp = mp0 /\ vp = vp0 /\
   rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
   matrix6_bound16 mp0 /\ vector3_bound24 vp0 /\
   0 <= W64.to_uint row <= 2 /\
   W64.to_uint row_out = 256 * W64.to_uint row /\
   W64.to_uint row_mat = 768 * W64.to_uint row /\
   prefix_bound8192 tp (W64.to_uint row_out) 18 /\
   KeygenM23MatrixSpec.word_tail_frame tp0 tp 512).
+ wp.
  while
    (mp = mp0 /\ vp = vp0 /\
     rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
     matrix6_bound16 mp0 /\ vector3_bound24 vp0 /\
     0 <= W64.to_uint row < 2 /\
     W64.to_uint row_out = 256 * W64.to_uint row /\
     W64.to_uint row_mat = 768 * W64.to_uint row /\
     0 <= W64.to_uint col <= 3 /\
     W64.to_uint col_off = 256 * W64.to_uint col /\
     prefix_bound8192 tp (W64.to_uint row_out) 18 /\
     row_acc_ok tp (W64.to_uint row_out) (W64.to_uint col) /\
     KeygenM23MatrixSpec.word_tail_frame tp0 tp 512).
  + wp.
    while
      (mp = mp0 /\ vp = vp0 /\
       rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
       matrix6_bound16 mp0 /\ vector3_bound24 vp0 /\
       0 <= W64.to_uint row < 2 /\
       W64.to_uint row_out = 256 * W64.to_uint row /\
       W64.to_uint row_mat = 768 * W64.to_uint row /\
       0 <= W64.to_uint col < 3 /\
       W64.to_uint col_off = 256 * W64.to_uint col /\
       0 <= W64.to_uint j <= 256 /\
       prefix_bound8192 tp (W64.to_uint row_out) 18 /\
       row_mixed_acc_ok tp (W64.to_uint row_out)
         (W64.to_uint j) (W64.to_uint col) /\
       KeygenM23MatrixSpec.word_tail_frame tp0 tp 512).
    + seq 9 :
        (mp = mp0 /\ vp = vp0 /\
         rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
         matrix6_bound16 mp0 /\ vector3_bound24 vp0 /\
         0 <= W64.to_uint row < 2 /\
         W64.to_uint row_out = 256 * W64.to_uint row /\
         W64.to_uint row_mat = 768 * W64.to_uint row /\
         0 <= W64.to_uint col < 3 /\
         W64.to_uint col_off = 256 * W64.to_uint col /\
         0 <= W64.to_uint j < 256 /\
         prefix_bound8192 tp (W64.to_uint row_out) 18 /\
         row_mixed_acc_ok tp (W64.to_uint row_out)
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
        + rewrite hmidx hrowmat hcoloff.
          apply hmp.
          smt().
        rewrite hvidx hcoloff.
        apply hvp.
        smt().
      + wp.
        exlim a => aa.
        exlim b => bb.
        call (parent_fqmul_16_24 aa bb).
        auto => /> &hr _ _ hrow0 hrowlt hrowout _ hcol0 hcollt
                      _ hj0 hjlt hpref hdone htodo hframe
                      _ _ _ _ result _ hres0 hres1.
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
        have hmixed :
            row_mixed_acc_ok tp{hr} (W64.to_uint row_out{hr})
              (W64.to_uint j{hr}) (W64.to_uint col{hr})
          by split; [exact hdone | exact htodo].
        have hold :
            acc_word_ok
              (BArray8192.get32 tp{hr}
                (W64.to_uint row_out{hr} + W64.to_uint j{hr}))
              (W64.to_uint col{hr}).
        + apply htodo.
          smt().
        have hres : Fq.bw32 result 16.
        + rewrite /Fq.bw32.
          split; [exact hres0 | exact hres1].
        have hnew :
            acc_word_ok
              (BArray8192.get32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
               result)
              (W64.to_uint col{hr} + 1).
        + apply (acc_add_bound (W64.to_uint col{hr})
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
        + apply (prefix_bound8192_set_after tp{hr}
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
        have hmixed' :
            row_mixed_acc_ok
              (BArray8192.set32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                 (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                  result))
              (W64.to_uint row_out{hr})
              (W64.to_uint j{hr} + 1) (W64.to_uint col{hr}).
        + apply (row_mixed_acc_step tp{hr}
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
        rewrite hjsucc hidx.
        split.
        + split; smt().
        split.
        + exact hpref'.
        split.
        + rewrite /row_mixed_acc_ok in hmixed'.
          move: hmixed' => [hdone' htodo'].
          split.
          + move=> j0 hj00 hj0lt.
            apply hdone'.
            smt().
          move=> j0 hj0lo hj0hi.
          apply htodo'.
          smt().
        exact hframe'.
    wp.
    skip => /> &hr _ _ hrow0 hrowlt hrowout hrowmat
                  hcol0 hcolle hcoloff hpref hrowacc hframe hguard.
    have hcollt : W64.to_uint col{hr} < 3.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /=.
      trivial.
    split.
    + split; first exact hcollt.
      split.
      + smt().
      move=> j0 hj00 hj0lt.
      have hjok := hrowacc j0 _.
      + smt().
      rewrite /acc_word_ok /Fq.bw32 in hjok.
      exact hjok.
    move=> j0 tp1 hjdone _ hj00 hj0le hpref1 hdone htodo hframe1.
    have hjeq : W64.to_uint j0 = 256.
    + move: hjdone.
      rewrite W64.ultE W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    have hmixed :
        row_mixed_acc_ok tp1 (W64.to_uint row_out{hr}) 256
          (W64.to_uint col{hr}).
    + rewrite /row_mixed_acc_ok.
      split.
      + move=> k hk.
        apply hdone.
        rewrite hjeq.
        exact hk.
      move=> k hk.
      apply htodo.
      rewrite hjeq.
      exact hk.
    have hnext :
        row_acc_ok tp1 (W64.to_uint row_out{hr})
          (W64.to_uint col{hr} + 1)
      by apply (row_mixed_acc_to_next tp1
                  (W64.to_uint row_out{hr}) (W64.to_uint col{hr})).
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
    rewrite hcolsucc hoffsucc hcoloff.
    split.
    + split; smt().
    split.
    + ring.
    exact hnext.
  wp.
  while
    (mp = mp0 /\ vp = vp0 /\
     rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
     matrix6_bound16 mp0 /\ vector3_bound24 vp0 /\
     0 <= W64.to_uint row < 2 /\
     W64.to_uint row_out = 256 * W64.to_uint row /\
     W64.to_uint row_mat = 768 * W64.to_uint row /\
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
    + apply (prefix_bound8192_set_after tp{hr}
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
    + apply (row_zero_prefix_step tp{hr}
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
  have hrowlt : W64.to_uint row{hr} < 2.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
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
  + apply (row_zero_prefix_to_acc0 tp1
             (W64.to_uint row_out{hr})).
    exact hzero256.
  move=> col0 col_off0 tp2 hcoldone hcol00 hcol0le hcoloff
          hpref2 hrowacc hframe2.
  have hcoleq : W64.to_uint col0 = 3.
  + move: hcoldone.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hacc3 :
      row_acc_ok tp2 (W64.to_uint row_out{hr}) 3.
  + rewrite -hcoleq.
    exact hrowacc.
  have hrowbound :
      row_bound8192 tp2 (W64.to_uint row_out{hr}) 18
    by apply (row_acc3_bound18 tp2 (W64.to_uint row_out{hr})).
  have hprefnext :
      prefix_bound8192 tp2 (W64.to_uint row_out{hr} + 256) 18.
  + apply (prefix_plus_row_bound18 tp2
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
          hcoloff hcoleq.
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
+ rewrite /prefix_bound8192.
  smt().
move=> row0 row_mat0 row_out0 tp1 hdone hrow0 hrowle
        hrowout _ hpref _.
have hnotlt : ! (W64.to_uint row0 < 2).
+ move: hdone.
  rewrite W64.ultE W64.of_uintK /=.
  trivial.
have hroweq : W64.to_uint row0 = 2 by smt().
have hout : W64.to_uint row_out0 = 512 by smt().
rewrite -hout.
exact hpref.
qed.

op pointwise_term
    (mp : BArray32768.t) (vp : BArray8192.t)
    (row col j : int) : coeff =
  NTT_Fq.word_to_coeff
    (BArray32768.get32 mp ((row * 3 + col) * 256 + j)) *
  NTT_Fq.word_to_coeff
    (BArray8192.get32 vp (col * 256 + j)) *
  inv NTT_Fq.R.

op partial_sum
    (mp : BArray32768.t) (vp : BArray8192.t)
    (row j col : int) : coeff =
  if col = 0 then Zq.zero
  else if col = 1 then pointwise_term mp vp row 0 j
  else if col = 2 then
    pointwise_term mp vp row 0 j +
    pointwise_term mp vp row 1 j
  else
    (pointwise_term mp vp row 0 j +
     pointwise_term mp vp row 1 j) +
    pointwise_term mp vp row 2 j.

op row_acc_sem
    (a : BArray8192.t) (mp : BArray32768.t) (vp : BArray8192.t)
    (row col : int) : bool =
  forall j, 0 <= j < 256 =>
    NTT_Fq.word_to_coeff
      (BArray8192.get32 a (256 * row + j)) =
    partial_sum mp vp row j col.

op row_mixed_sem
    (a : BArray8192.t) (mp : BArray32768.t) (vp : BArray8192.t)
    (row upto col : int) : bool =
  (forall j, 0 <= j < upto =>
     NTT_Fq.word_to_coeff
       (BArray8192.get32 a (256 * row + j)) =
     partial_sum mp vp row j (col + 1)) /\
  (forall j, upto <= j < 256 =>
     NTT_Fq.word_to_coeff
       (BArray8192.get32 a (256 * row + j)) =
     partial_sum mp vp row j col).

op rows_sem
    (a : BArray8192.t) (mp : BArray32768.t) (vp : BArray8192.t)
    (upto : int) : bool =
  forall row j,
    0 <= row < upto =>
    0 <= j < 256 =>
    NTT_Fq.word_to_coeff
      (BArray8192.get32 a (256 * row + j)) =
    (KeygenM23ArithmeticSpec.pointwise_row_words mp vp row).[j].

op pointwise_rows_repr
    (a : BArray8192.t) (mp : BArray32768.t)
    (vp : BArray8192.t) : bool =
  KeygenM23ArithmeticSpec.wide_poly a 0 =
    KeygenM23ArithmeticSpec.pointwise_row_words mp vp 0 /\
  KeygenM23ArithmeticSpec.wide_poly a 256 =
    KeygenM23ArithmeticSpec.pointwise_row_words mp vp 1.

lemma partial_sum_succ mp vp row j col :
  0 <= col < 3 =>
  partial_sum mp vp row j (col + 1) =
    partial_sum mp vp row j col +
    pointwise_term mp vp row col j.
proof.
move=> hcol.
have hc : col = 0 \/ col = 1 \/ col = 2 by smt().
move: hc.
move=> [->|[->|->]].
+ by rewrite /partial_sum /=; ring.
+ by rewrite /partial_sum /=.
+ by rewrite /partial_sum /=.
qed.

lemma partial_sum3_pointwise mp vp row j :
  0 <= j < 256 =>
  partial_sum mp vp row j 3 =
    (KeygenM23ArithmeticSpec.pointwise_row_words mp vp row).[j].
proof.
move=> hj.
rewrite /partial_sum /=.
rewrite KeygenM23ArithmeticSpec.pointwise_row_words_get 1:/#.
rewrite /pointwise_term
        /KeygenM23MatrixSpec.mode2_cols_i
        /KeygenM23MatrixSpec.poly_words_i /=.
smt().
qed.

lemma rows_sem_set_current a mp vp row j w :
  0 <= row < 2 =>
  0 <= j < 256 =>
  rows_sem a mp vp row =>
  rows_sem
    (BArray8192.set32 a (256 * row + j) w)
    mp vp row.
proof.
rewrite /rows_sem.
move=> hrow hj hsem r k hr hk.
rewrite BArray8192.get_set32E 1:/# 1:/#.
have hne : 256 * row + j <> 256 * r + k by smt().
rewrite ifF 1:/#.
by apply hsem.
qed.

lemma row_zero_prefix_to_sem0 a mp vp row :
  row_zero_prefix a (256 * row) 256 =>
  row_acc_sem a mp vp row 0.
proof.
rewrite /row_zero_prefix /row_acc_sem /partial_sum.
move=> hzero j hj.
rewrite (hzero j hj).
by rewrite /NTT_Fq.word_to_coeff W32.to_sintK_small.
qed.

lemma row_acc_sem_to_mixed0 a mp vp row col :
  row_acc_sem a mp vp row col =>
  row_mixed_sem a mp vp row 0 col.
proof.
rewrite /row_acc_sem /row_mixed_sem.
move=> hsem.
split.
+ smt().
move=> j hj.
by apply hsem; smt().
qed.

lemma row_mixed_sem_to_next a mp vp row col :
  row_mixed_sem a mp vp row 256 col =>
  row_acc_sem a mp vp row (col + 1).
proof.
rewrite /row_mixed_sem /row_acc_sem.
move=> [hdone _] j hj.
by apply hdone; smt().
qed.

lemma acc_bits_range col :
  0 <= col < 3 =>
  0 <= acc_bits col < 31.
proof.
rewrite /acc_bits.
smt().
qed.

lemma row_mixed_sem_step a mp vp row upto col t :
  0 <= row < 2 =>
  0 <= upto < 256 =>
  0 <= col < 3 =>
  row_mixed_acc_ok a (256 * row) upto col =>
  row_mixed_sem a mp vp row upto col =>
  Fq.bw32 t 16 =>
  NTT_Fq.word_to_coeff t = pointwise_term mp vp row col upto =>
  row_mixed_sem
    (BArray8192.set32 a (256 * row + upto)
      (BArray8192.get32 a (256 * row + upto) + t))
    mp vp row (upto + 1) col.
proof.
move=> hrow hupto hcol.
rewrite /row_mixed_acc_ok /row_mixed_sem.
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
      (RefJasminNTT.word_to_coeff_add
        (BArray8192.get32 a (256 * row + upto)) t
        (acc_bits col) 16)
      1:(acc_bits_range col hcol) 1:/# 1:hold 1:htb.
    rewrite (hstodo upto) 1:/# htsem.
    by rewrite -partial_sum_succ 1:hcol.
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

lemma rows_sem_extend a mp vp row :
  0 <= row < 2 =>
  rows_sem a mp vp row =>
  row_acc_sem a mp vp row 3 =>
  rows_sem a mp vp (row + 1).
proof.
rewrite /rows_sem /row_acc_sem.
move=> hrow hrows hacc r j hr hj.
case (r < row) => hlt.
+ apply hrows; smt().
have -> : r = row by smt().
rewrite -partial_sum3_pointwise 1:hj.
by apply hacc.
qed.

lemma rows_sem2_to_repr a mp vp :
  rows_sem a mp vp 2 =>
  pointwise_rows_repr a mp vp.
proof.
move=> hrows.
rewrite /rows_sem in hrows.
rewrite /pointwise_rows_repr.
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

lemma matrix_active_bound16_to_matrix6 mp :
  KeygenM23ArithmeticSpec.matrix_active_bound16 mp =>
  matrix6_bound16 mp.
proof.
rewrite /KeygenM23ArithmeticSpec.matrix_active_bound16
        /matrix6_bound16.
move=> h i hi.
case (i < 256) => hi0.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp
        ((0 * KeygenM23MatrixSpec.mode2_cols_i + 0) *
           KeygenM23MatrixSpec.poly_words_i + i)
    by congr; rewrite /KeygenM23MatrixSpec.mode2_cols_i
                      /KeygenM23MatrixSpec.poly_words_i; ring.
  apply h; smt().
case (i < 2 * 256) => hi1.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp
        ((0 * KeygenM23MatrixSpec.mode2_cols_i + 1) *
           KeygenM23MatrixSpec.poly_words_i + (i - 256))
    by congr; rewrite /KeygenM23MatrixSpec.mode2_cols_i
                      /KeygenM23MatrixSpec.poly_words_i; ring.
  apply h; smt().
case (i < 3 * 256) => hi2.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp
        ((0 * KeygenM23MatrixSpec.mode2_cols_i + 2) *
           KeygenM23MatrixSpec.poly_words_i + (i - 2 * 256))
    by congr; rewrite /KeygenM23MatrixSpec.mode2_cols_i
                      /KeygenM23MatrixSpec.poly_words_i; ring.
  apply h; smt().
case (i < 4 * 256) => hi3.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp
        ((1 * KeygenM23MatrixSpec.mode2_cols_i + 0) *
           KeygenM23MatrixSpec.poly_words_i + (i - 3 * 256))
    by congr; rewrite /KeygenM23MatrixSpec.mode2_cols_i
                      /KeygenM23MatrixSpec.poly_words_i; ring.
  apply h; smt().
case (i < 5 * 256) => hi4.
+ have -> :
      BArray32768.get32 mp i =
      BArray32768.get32 mp
        ((1 * KeygenM23MatrixSpec.mode2_cols_i + 1) *
           KeygenM23MatrixSpec.poly_words_i + (i - 4 * 256))
    by congr; rewrite /KeygenM23MatrixSpec.mode2_cols_i
                      /KeygenM23MatrixSpec.poly_words_i; ring.
  apply h; smt().
have -> :
    BArray32768.get32 mp i =
    BArray32768.get32 mp
      ((1 * KeygenM23MatrixSpec.mode2_cols_i + 2) *
         KeygenM23MatrixSpec.poly_words_i + (i - 5 * 256))
  by congr; rewrite /KeygenM23MatrixSpec.mode2_cols_i
                    /KeygenM23MatrixSpec.poly_words_i; ring.
apply h; smt().
qed.

lemma mode2_ntt_repr_bound24_to_vector3 vp p0 p1 p2 :
  KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24 vp p0 p1 p2 =>
  vector3_bound24 vp.
proof.
rewrite /KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
        /KeygenM23ArithmeticSpec.wide_slice_repr_bound
        /KeygenM23ArithmeticSpec.wide_slice_bound
        /vector3_bound24.
move=> [[_ h0] [[_ h1] [_ h2]]] i hi.
case (i < 256) => hi0.
+ have -> :
      BArray8192.get32 vp i =
      BArray8192.get32 vp (0 + i)
    by congr; ring.
  apply h0.
  rewrite /KeygenM23MatrixSpec.poly_words_i.
  smt().
case (i < 2 * 256) => hi1.
+ have -> :
      BArray8192.get32 vp i =
      BArray8192.get32 vp
        (KeygenM23MatrixSpec.poly_words_i + (i - 256))
    by congr; rewrite /KeygenM23MatrixSpec.poly_words_i; ring.
  apply h1.
  rewrite /KeygenM23MatrixSpec.poly_words_i.
  smt().
have -> :
    BArray8192.get32 vp i =
    BArray8192.get32 vp
      (2 * KeygenM23MatrixSpec.poly_words_i + (i - 2 * 256))
  by congr; rewrite /KeygenM23MatrixSpec.poly_words_i; ring.
apply h2.
rewrite /KeygenM23MatrixSpec.poly_words_i.
smt().
qed.

lemma polymat_pointwise_mode2_semantics
    (tp0 : BArray8192.t)
    (mp0 : BArray32768.t)
    (vp0 : BArray8192.t) :
  hoare [Parent._polymat_pointwise_acc :
    tp = tp0 /\ mp = mp0 /\ vp = vp0 /\
    rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
    matrix6_bound16 mp0 /\ vector3_bound24 vp0
    ==>
    pointwise_rows_repr res mp0 vp0].
proof.
proc.
while
  (mp = mp0 /\ vp = vp0 /\
   rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
   matrix6_bound16 mp0 /\ vector3_bound24 vp0 /\
   0 <= W64.to_uint row <= 2 /\
   W64.to_uint row_out = 256 * W64.to_uint row /\
   W64.to_uint row_mat = 768 * W64.to_uint row /\
   rows_sem tp mp0 vp0 (W64.to_uint row)).
+ wp.
  while
    (mp = mp0 /\ vp = vp0 /\
     rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
     matrix6_bound16 mp0 /\ vector3_bound24 vp0 /\
     0 <= W64.to_uint row < 2 /\
     W64.to_uint row_out = 256 * W64.to_uint row /\
     W64.to_uint row_mat = 768 * W64.to_uint row /\
     0 <= W64.to_uint col <= 3 /\
     W64.to_uint col_off = 256 * W64.to_uint col /\
     rows_sem tp mp0 vp0 (W64.to_uint row) /\
     row_acc_ok tp (W64.to_uint row_out) (W64.to_uint col) /\
     row_acc_sem tp mp0 vp0
       (W64.to_uint row) (W64.to_uint col)).
  + wp.
    while
      (mp = mp0 /\ vp = vp0 /\
       rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
       matrix6_bound16 mp0 /\ vector3_bound24 vp0 /\
       0 <= W64.to_uint row < 2 /\
       W64.to_uint row_out = 256 * W64.to_uint row /\
       W64.to_uint row_mat = 768 * W64.to_uint row /\
       0 <= W64.to_uint col < 3 /\
       W64.to_uint col_off = 256 * W64.to_uint col /\
       0 <= W64.to_uint j <= 256 /\
       rows_sem tp mp0 vp0 (W64.to_uint row) /\
       row_mixed_acc_ok tp (W64.to_uint row_out)
         (W64.to_uint j) (W64.to_uint col) /\
       row_mixed_sem tp mp0 vp0 (W64.to_uint row)
         (W64.to_uint j) (W64.to_uint col)).
    + seq 9 :
        (mp = mp0 /\ vp = vp0 /\
         rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
         matrix6_bound16 mp0 /\ vector3_bound24 vp0 /\
         0 <= W64.to_uint row < 2 /\
         W64.to_uint row_out = 256 * W64.to_uint row /\
         W64.to_uint row_mat = 768 * W64.to_uint row /\
         0 <= W64.to_uint col < 3 /\
         W64.to_uint col_off = 256 * W64.to_uint col /\
         0 <= W64.to_uint j < 256 /\
         rows_sem tp mp0 vp0 (W64.to_uint row) /\
         row_mixed_acc_ok tp (W64.to_uint row_out)
           (W64.to_uint j) (W64.to_uint col) /\
         row_mixed_sem tp mp0 vp0 (W64.to_uint row)
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
        + rewrite hmidx hrowmat hcoloff.
          apply hmp.
          smt().
        rewrite hvidx hcoloff.
        apply hvp.
        smt().
      + wp.
        exlim a => aa.
        exlim b => bb.
        call (parent_fqmul_16_24 aa bb).
        auto => /> &hr _ _ hrow0 hrowlt hrowout hrowmat
                      hcol0 hcollt hcoloff hj0 hjlt
                      hrows hdone htodo hsdone hstodo
                      _ _ _ _ result hressem hres0 hres1.
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
              (((W64.to_uint row{hr} * 3 +
                   W64.to_uint col{hr}) * 256) +
                W64.to_uint j{hr}).
        + congr.
          rewrite hmidx hrowmat hcoloff.
          ring.
        have hvword :
            BArray8192.get32 vp0
              (W64.to_uint (col_off{hr} + j{hr})) =
            BArray8192.get32 vp0
              (W64.to_uint col{hr} * 256 +
               W64.to_uint j{hr}).
        + congr.
          rewrite hvidx hcoloff.
          ring.
        have hterm :
            NTT_Fq.word_to_coeff result =
            pointwise_term mp0 vp0
              (W64.to_uint row{hr}) (W64.to_uint col{hr})
              (W64.to_uint j{hr}).
        + rewrite /pointwise_term -hmword -hvword.
          exact hressem.
        have hmixed :
            row_mixed_acc_ok tp{hr} (W64.to_uint row_out{hr})
              (W64.to_uint j{hr}) (W64.to_uint col{hr})
          by split; [exact hdone | exact htodo].
        have hmixsem :
            row_mixed_sem tp{hr} mp0 vp0
              (W64.to_uint row{hr}) (W64.to_uint j{hr})
              (W64.to_uint col{hr})
          by split; [exact hsdone | exact hstodo].
        have hrows0 :
            rows_sem tp{hr} mp0 vp0 (W64.to_uint row{hr}).
        + rewrite /rows_sem.
          exact hrows.
        have hold :
            acc_word_ok
              (BArray8192.get32 tp{hr}
                (W64.to_uint row_out{hr} + W64.to_uint j{hr}))
              (W64.to_uint col{hr}).
        + apply htodo.
          smt().
        have hres : Fq.bw32 result 16.
        + rewrite /Fq.bw32.
          split; [exact hres0 | exact hres1].
        have hnew :
            acc_word_ok
              (BArray8192.get32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
               result)
              (W64.to_uint col{hr} + 1).
        + apply (acc_add_bound (W64.to_uint col{hr})
                   (BArray8192.get32 tp{hr}
                     (W64.to_uint row_out{hr} + W64.to_uint j{hr}))
                   result).
          + smt().
          + exact hold.
          exact hres.
        have hmixed' :
            row_mixed_acc_ok
              (BArray8192.set32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                 (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                  result))
              (W64.to_uint row_out{hr})
              (W64.to_uint j{hr} + 1) (W64.to_uint col{hr}).
        + apply (row_mixed_acc_step tp{hr}
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
        have hrows' :
            rows_sem
              (BArray8192.set32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                 (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                  result))
              mp0 vp0 (W64.to_uint row{hr}).
        + rewrite hrowout.
          apply rows_sem_set_current.
          + smt().
          + smt().
          exact hrows0.
        have hmixsem' :
            row_mixed_sem
              (BArray8192.set32 tp{hr}
                 (W64.to_uint row_out{hr} + W64.to_uint j{hr})
                 (BArray8192.get32 tp{hr}
                    (W64.to_uint row_out{hr} + W64.to_uint j{hr}) +
                  result))
              mp0 vp0 (W64.to_uint row{hr})
              (W64.to_uint j{hr} + 1) (W64.to_uint col{hr}).
        + rewrite hrowout.
          apply (row_mixed_sem_step tp{hr} mp0 vp0
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
        rewrite hjsucc hidx.
        split.
        + split; smt().
        split.
        + exact hrows'.
        split.
        + rewrite /row_mixed_acc_ok in hmixed'.
          move: hmixed' => [hdone' htodo'].
          split.
          + move=> j0 hj00 hj0lt.
            apply hdone'.
            smt().
          move=> j0 hj0lo hj0hi.
          apply htodo'.
          smt().
        rewrite /row_mixed_sem in hmixsem'.
        move: hmixsem' => [hsdone' hstodo'].
        split.
        + move=> j0 hj00 hj0lt.
          apply hsdone'.
          smt().
        move=> j0 hj0lo hj0hi.
        apply hstodo'.
        smt().
    wp.
    skip => /> &hr _ _ hrow0 hrowlt hrowout hrowmat
                  hcol0 hcolle hcoloff hrows hrowacc hrowsem
                  hguard.
    have hcollt : W64.to_uint col{hr} < 3.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /=.
      trivial.
    split.
    + split; first exact hcollt.
      split.
      + split.
        + move=> j0 hj00 hj0lt.
          smt().
        move=> j0 hj00 hj0lt.
        apply hrowacc.
        smt().
      split.
      + move=> j0 hj00 hj0lt.
        smt().
      move=> j0 hj00 hj0lt.
      apply hrowsem.
      smt().
    move=> j0 tp1 hjdone _ hj00 hj0le hrows1
            hdone htodo hsdone hstodo.
    have hjeq : W64.to_uint j0 = 256.
    + move: hjdone.
      rewrite W64.ultE W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    have hmixed :
        row_mixed_acc_ok tp1 (W64.to_uint row_out{hr}) 256
          (W64.to_uint col{hr}).
    + rewrite /row_mixed_acc_ok.
      split.
      + move=> k hk.
        apply hdone.
        rewrite hjeq.
        exact hk.
      move=> k hk.
      apply htodo.
      rewrite hjeq.
      exact hk.
    have hmixsem :
        row_mixed_sem tp1 mp0 vp0 (W64.to_uint row{hr}) 256
          (W64.to_uint col{hr}).
    + rewrite /row_mixed_sem.
      split.
      + move=> k hk.
        apply hsdone.
        rewrite hjeq.
        exact hk.
      move=> k hk.
      apply hstodo.
      rewrite hjeq.
      exact hk.
    have hnext :
        row_acc_ok tp1 (W64.to_uint row_out{hr})
          (W64.to_uint col{hr} + 1)
      by apply (row_mixed_acc_to_next tp1
                  (W64.to_uint row_out{hr}) (W64.to_uint col{hr})).
    have hsemnext :
        row_acc_sem tp1 mp0 vp0 (W64.to_uint row{hr})
          (W64.to_uint col{hr} + 1)
      by apply (row_mixed_sem_to_next tp1 mp0 vp0
                  (W64.to_uint row{hr}) (W64.to_uint col{hr})).
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
    rewrite hcolsucc hoffsucc hcoloff.
    split.
    + split; smt().
    split.
    + ring.
    split.
    + exact hnext.
    exact hsemnext.
  wp.
  while
    (mp = mp0 /\ vp = vp0 /\
     rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
     matrix6_bound16 mp0 /\ vector3_bound24 vp0 /\
     0 <= W64.to_uint row < 2 /\
     W64.to_uint row_out = 256 * W64.to_uint row /\
     W64.to_uint row_mat = 768 * W64.to_uint row /\
     0 <= W64.to_uint j <= 256 /\
     rows_sem tp mp0 vp0 (W64.to_uint row) /\
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
        rows_sem tp{hr} mp0 vp0 (W64.to_uint row{hr}).
    + rewrite /rows_sem.
      exact hrows.
    have hrows' :
        rows_sem
          (BArray8192.set32 tp{hr}
             (W64.to_uint row_out{hr} + W64.to_uint j{hr}) W32.zero)
          mp0 vp0 (W64.to_uint row{hr}).
    + rewrite hrowout.
      apply rows_sem_set_current.
      + smt().
      + smt().
      exact hrows0.
    have hzero' :
        row_zero_prefix
          (BArray8192.set32 tp{hr}
             (W64.to_uint row_out{hr} + W64.to_uint j{hr}) W32.zero)
          (W64.to_uint row_out{hr}) (W64.to_uint j{hr} + 1).
    + apply (row_zero_prefix_step tp{hr}
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
  have hrowlt : W64.to_uint row{hr} < 2.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
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
      row_acc_ok tp1 (W64.to_uint row_out{hr}) 0.
  + apply (row_zero_prefix_to_acc0 tp1
             (W64.to_uint row_out{hr})).
    exact hzero256.
  have hsem0 :
      row_acc_sem tp1 mp0 vp0 (W64.to_uint row{hr}) 0.
  + apply (row_zero_prefix_to_sem0 tp1 mp0 vp0
             (W64.to_uint row{hr})).
    rewrite -hrowout.
    exact hzero256.
  split.
  + split.
    + exact hacc0.
    exact hsem0.
  move=> col0 col_off0 tp2 hcoldone hcol00 hcol0le hcoloff
          hrows2 hrowacc hrowsem.
  have hcoleq : W64.to_uint col0 = 3.
  + move: hcoldone.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hrows0 :
      rows_sem tp2 mp0 vp0 (W64.to_uint row{hr}).
  + rewrite /rows_sem.
    exact hrows2.
  have hsem3 :
      row_acc_sem tp2 mp0 vp0 (W64.to_uint row{hr}) 3.
  + rewrite /row_acc_sem.
    move=> k hk.
    rewrite -hcoleq.
    apply hrowsem.
    exact hk.
  have hrowsnext :
      rows_sem tp2 mp0 vp0 (W64.to_uint row{hr} + 1).
  + apply rows_sem_extend.
    + smt().
    + exact hrows0.
    exact hsem3.
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
          hcoloff hcoleq.
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
+ rewrite /rows_sem.
  smt().
move=> row0 row_mat0 row_out0 tp1 hdone hrow0 hrowle
        hrowout hrowmat hrows.
have hnotlt : ! (W64.to_uint row0 < 2).
+ move: hdone.
  rewrite W64.ultE W64.of_uintK /=.
  trivial.
have hroweq : W64.to_uint row0 = 2 by smt().
have hrows2 : rows_sem tp1 mp0 vp0 2.
+ rewrite /rows_sem.
  move=> r j hr hj.
  apply hrows.
  + rewrite hroweq.
    exact hr.
  exact hj.
have hrepr : pointwise_rows_repr tp1 mp0 vp0.
+ apply (rows_sem2_to_repr tp1 mp0 vp0).
  exact hrows2.
rewrite /pointwise_rows_repr in hrepr.
exact hrepr.
qed.

lemma pointwise_rows_prefix_to_mode2_bound18 a mp vp :
  pointwise_rows_repr a mp vp =>
  prefix_bound8192 a 512 18 =>
  KeygenM23ArithmeticSpec.mode2_pointwise_repr_bound18 a mp vp.
proof.
rewrite /pointwise_rows_repr
        /KeygenM23ArithmeticSpec.mode2_pointwise_repr_bound18
        /KeygenM23ArithmeticSpec.wide_slice_repr_bound
        /KeygenM23ArithmeticSpec.wide_slice_bound
        /prefix_bound8192.
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

lemma polymat_pointwise_mode2_local_spec
    (tp0 : BArray8192.t)
    (mp0 : BArray32768.t)
    (vp0 : BArray8192.t) :
  hoare [Parent._polymat_pointwise_acc :
    tp = tp0 /\ mp = mp0 /\ vp = vp0 /\
    rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
    matrix6_bound16 mp0 /\ vector3_bound24 vp0
    ==>
    prefix_bound8192 res 512 18 /\
    KeygenM23MatrixSpec.word_tail_frame tp0 res 512 /\
    pointwise_rows_repr res mp0 vp0].
proof.
conseq
  (polymat_pointwise_mode2_bound18_frame tp0 mp0 vp0)
  (polymat_pointwise_mode2_semantics tp0 mp0 vp0) => />.
qed.

lemma polymat_pointwise_mode2_repr_bound18_frame
    (bp0 : BArray8192.t)
    (mp0 : BArray32768.t)
    (vp0 : BArray8192.t)
    (p0 p1 p2 : Rq.poly) :
  hoare [Parent._polymat_pointwise_acc :
    tp = bp0 /\ mp = mp0 /\ vp = vp0 /\
    rows = W64.of_int 2 /\ cols = W64.of_int 3 /\
    KeygenM23ArithmeticSpec.matrix_active_bound16 mp0 /\
    KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24 vp0 p0 p1 p2
    ==>
    KeygenM23ArithmeticSpec.mode2_pointwise_repr_bound18 res mp0 vp0 /\
    KeygenM23MatrixSpec.word_tail_frame bp0 res 512].
proof.
conseq (polymat_pointwise_mode2_local_spec bp0 mp0 vp0) => />.
+ move=> &hr _ _ hmatrix hrepr0 hbound0 hrepr1 hbound1
          hrepr2 hbound2.
  split.
  + apply (matrix_active_bound16_to_matrix6 mp{hr}).
    exact hmatrix.
  apply (mode2_ntt_repr_bound24_to_vector3 vp{hr} p0 p1 p2).
  rewrite /KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
          /KeygenM23ArithmeticSpec.wide_slice_repr_bound.
  split.
  + split; [exact hrepr0 | exact hbound0].
  split.
  + split; [exact hrepr1 | exact hbound1].
  split; [exact hrepr2 | exact hbound2].
move=> &hr _ _ _ _ _ _ _ _ _
        result hprefix hframe hrow0 hrow1.
have hpost :
    KeygenM23ArithmeticSpec.mode2_pointwise_repr_bound18
      result mp{hr} vp{hr}.
+ apply
    (pointwise_rows_prefix_to_mode2_bound18
      result mp{hr} vp{hr}).
  + rewrite /pointwise_rows_repr.
    split; [exact hrow0 | exact hrow1].
  exact hprefix.
rewrite /KeygenM23ArithmeticSpec.mode2_pointwise_repr_bound18
        /KeygenM23ArithmeticSpec.wide_slice_repr_bound in hpost.
exact hpost.
qed.

end TargetKeygenM23Pointwise.
