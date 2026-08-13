require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget.

theory VerifyCrtFreezeMode2PostFreeze.

module Verify = VerifyCoreTarget.M.

op mode2_rows : int = 2.
op mode2_row_words : int = 256.
op mode2_active_words : int = 512.

op coeff_tail_frame
    (before after : BArray8192.t) (start : int) : bool =
  forall i, start <= i < 2048 =>
    BArray8192.get32 after i = BArray8192.get32 before i.

op mode2_fromcrt_add_xor (high wprime : W32.t) : W32.t =
  (W32.zero - ((high `^` wprime) `&` W32.one)) `&`
  W32.of_int 64513.

op mode2_fromcrt_add_high (high : W32.t) : W32.t =
  (W32.zero - (high `&` W32.one)) `&` W32.of_int 64513.

op mode2_fromcrt_word
    (highp : BArray8192.t) (wprimep : BArray1024.t) (idx : int) : W32.t =
  if 0 <= idx < mode2_row_words then
    let high = BArray8192.get32 highp idx in
    high + mode2_fromcrt_add_xor high (BArray1024.get32 wprimep idx)
  else if mode2_row_words <= idx < mode2_active_words then
    let high = BArray8192.get32 highp idx in
    high + mode2_fromcrt_add_high high
  else BArray8192.get32 highp idx.

op freeze2q_word (a : W32.t) : W32.t =
  let x0 = sigextu64 a in
  let t0 = x0 * W64.of_int 33287 in
  let t1 = t0 `|>>` W8.of_int 32 in
  let t2 = t1 * W64.of_int 129026 in
  let x1 = x0 - t2 in
  let mask0 = (x1 `|>>` W8.of_int 31) `&` W64.of_int 258052 in
  let x2 = x1 + mask0 in
  let mask1 = (x2 - W64.of_int 129026) `|>>` W8.of_int 31 in
  let mask2 = truncateu32 mask1 in
  let mask3 = (mask2 + W32.of_int 1) * W32.of_int 129026 in
  let x3 = x2 - zeroextu64 mask3 in
  truncateu32 x3.

op fromcrt_prefix
    (outp highp : BArray8192.t) (wprimep : BArray1024.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray8192.get32 outp i = mode2_fromcrt_word highp wprimep i.

op freeze_input_prefix
    (outp inp : BArray8192.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray8192.get32 outp i = freeze2q_word (BArray8192.get32 inp i).

op crt_freeze_prefix
    (outp highp : BArray8192.t) (wprimep : BArray1024.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray8192.get32 outp i = freeze2q_word (mode2_fromcrt_word highp wprimep i).

lemma coeff_tail_frame_refl before start :
  coeff_tail_frame before before start.
proof. rewrite /coeff_tail_frame; trivial. qed.

lemma coeff_tail_frame_step before after n value :
  0 <= n < 2048 =>
  coeff_tail_frame before after n =>
  coeff_tail_frame before (BArray8192.set32 after n value) (n + 1).
proof.
move=> hn hframe.
rewrite /coeff_tail_frame => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
rewrite ifF 1:/#.
apply hframe; smt().
qed.

lemma coeff_tail_frame_trans before middle after start :
  coeff_tail_frame before middle start =>
  coeff_tail_frame middle after start =>
  coeff_tail_frame before after start.
proof.
move=> hleft hright.
rewrite /coeff_tail_frame => i hi.
rewrite hright 1:/#.
by apply hleft.
qed.

lemma fromcrt_prefix_zero outp highp wprimep :
  fromcrt_prefix outp highp wprimep 0.
proof. rewrite /fromcrt_prefix; smt(). qed.

lemma fromcrt_prefix_step outp highp wprimep n value :
  0 <= n < mode2_active_words =>
  value = mode2_fromcrt_word highp wprimep n =>
  fromcrt_prefix outp highp wprimep n =>
  fromcrt_prefix (BArray8192.set32 outp n value) highp wprimep (n + 1).
proof.
move=> hn hvalue hprefix.
rewrite /fromcrt_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ rewrite ifF 1:/#.
   apply hprefix; smt().
qed.

lemma freeze_input_prefix_zero outp inp :
  freeze_input_prefix outp inp 0.
proof. rewrite /freeze_input_prefix; smt(). qed.

lemma freeze_input_prefix_step outp inp n value :
  0 <= n < mode2_active_words =>
  value = freeze2q_word (BArray8192.get32 inp n) =>
  freeze_input_prefix outp inp n =>
  freeze_input_prefix (BArray8192.set32 outp n value) inp (n + 1).
proof.
move=> hn hvalue hprefix.
rewrite /freeze_input_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ rewrite ifF 1:/#.
   apply hprefix; smt().
qed.

lemma crt_freeze_prefix_of_prefixes mid out highp wprimep n :
  fromcrt_prefix mid highp wprimep n =>
  freeze_input_prefix out mid n =>
  crt_freeze_prefix out highp wprimep n.
proof.
move=> hfrom hfreeze.
rewrite /crt_freeze_prefix /freeze_input_prefix /fromcrt_prefix.
move=> i hi.
rewrite hfreeze 1:/#.
by rewrite hfrom 1:/#.
qed.

lemma freeze2q_word_correct (a0 : W32.t) :
  hoare [Verify.__freeze2q :
    a = a0
    ==>
    res = freeze2q_word a0].
proof.
proc.
auto => />.
qed.

lemma polyvec_freeze2q_mode2_word_exact (v0 : BArray8192.t) :
  hoare [Verify._polyvec_freeze2q :
    vp = v0 /\ count = W64.of_int mode2_active_words
    ==>
    freeze_input_prefix res v0 mode2_active_words /\
    coeff_tail_frame v0 res mode2_active_words].
proof.
proc.
while
  (count = W64.of_int mode2_active_words /\
   0 <= W64.to_uint i <= mode2_active_words /\
   freeze_input_prefix vp v0 (W64.to_uint i) /\
   coeff_tail_frame v0 vp (W64.to_uint i)).
+ inline Verify.__freeze2q.
  auto => />.
  move=> &hr hi0 hile hprefix hframe hguard.
  have hlt : W64.to_uint i{hr} < mode2_active_words.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /mode2_active_words /=.
    smt(W64.to_uint_cmp).
  have hnext :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have hirange : 0 <= W64.to_uint i{hr} < mode2_active_words.
  + split; first exact hi0.
    move=> _.
    exact hlt.
  have hstep : 0 <= W64.to_uint i{hr} + 1 <= mode2_active_words.
  + split.
    * smt().
    * move=> _.
      smt().
  have hcurrent :
      BArray8192.get32 vp{hr} (W64.to_uint i{hr}) =
      BArray8192.get32 v0 (W64.to_uint i{hr}).
  + have hframe' := hframe.
    rewrite /coeff_tail_frame in hframe'.
    apply hframe'; smt().
  move: hstep => [hstep0 hstep1].
  split.
  + rewrite hnext.
    split.
    * exact hstep0.
    * move=> _.
      exact hstep1.
  split.
  + rewrite hnext.
    apply (freeze_input_prefix_step _ _ (W64.to_uint i{hr})).
    * exact hirange.
    * rewrite hcurrent /freeze2q_word /=.
      trivial.
    * exact hprefix.
  + rewrite hnext.
    apply coeff_tail_frame_step.
    * smt().
    * exact hframe.
+ auto => />.
  split.
  + exact (freeze_input_prefix_zero v0 v0).
+ move=> i0 vp0 hdone hi0 hile hprefix hframe.
  have hieq : W64.to_uint i0 = mode2_active_words.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /mode2_active_words /=.
    smt(W64.to_uint_cmp).
  by rewrite -hieq.
qed.

lemma polyveck_poly_fromcrt_mode2_word_exact
    (z10 high0 : BArray8192.t) (wprime0 : BArray1024.t) :
  hoare [Verify._polyveck_poly_fromcrt :
    wp_0 = z10 /\ up = high0 /\ vp = wprime0 /\
    count = W64.of_int mode2_rows
    ==>
    fromcrt_prefix res high0 wprime0 mode2_active_words /\
    coeff_tail_frame z10 res mode2_active_words].
proof.
proc.
while
  (up = high0 /\ vp = wprime0 /\
   count = W64.of_int mode2_rows /\
   1 <= W64.to_uint k <= mode2_rows /\
   W64.to_uint off = mode2_row_words * W64.to_uint k /\
   fromcrt_prefix wp_0 high0 wprime0 (W64.to_uint off) /\
   coeff_tail_frame z10 wp_0 (W64.to_uint off)).
+ wp.
  while
    (up = high0 /\ vp = wprime0 /\
     count = W64.of_int mode2_rows /\
     W64.to_uint k = 1 /\
     W64.to_uint off = mode2_row_words /\
     0 <= W64.to_uint j <= mode2_row_words /\
     fromcrt_prefix wp_0 high0 wprime0
       (W64.to_uint off + W64.to_uint j) /\
     coeff_tail_frame z10 wp_0
       (W64.to_uint off + W64.to_uint j)).
  + auto => />.
    move=> &hr hk1 hoff256 hj0 hjle hprefix hframe hguard.
    have hjlt : W64.to_uint j{hr} < mode2_row_words.
    + move: hguard.
      rewrite W64.ultE W64.of_uintK /mode2_row_words /=.
      smt(W64.to_uint_cmp).
    have hidx :
        mode2_row_words <= mode2_row_words + W64.to_uint j{hr} <
        mode2_active_words.
    + rewrite /mode2_row_words /mode2_active_words /=.
      smt(W64.to_uint_cmp).
    have hnext :
        W64.to_uint (j{hr} + W64.one) = W64.to_uint j{hr} + 1.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      trivial.
    have hoffj :
        W64.to_uint (off{hr} + j{hr}) =
        mode2_row_words + W64.to_uint j{hr}.
    + rewrite W64.to_uintD_small 1:/# hoff256.
      trivial.
    have hbound :
        W64.to_uint off{hr} + W64.to_uint (j{hr} + W64.one) =
        (mode2_row_words + W64.to_uint j{hr}) + 1.
    + rewrite hoff256 hnext.
      ring.
    rewrite hoff256 in hprefix.
    rewrite hoff256 in hframe.
    split; first by rewrite hnext; smt(W64.to_uint_cmp).
    split.
    * rewrite hoffj hbound.
      apply (fromcrt_prefix_step _ _ _
        (mode2_row_words + W64.to_uint j{hr})).
      - rewrite /mode2_row_words /mode2_active_words /=.
         smt(W64.to_uint_cmp).
      - rewrite /mode2_fromcrt_word /mode2_fromcrt_add_high /=.
         rewrite ifF 1:/#.
         rewrite ifT 1:hidx.
         trivial.
      - exact hprefix.
    * rewrite hoffj hbound.
      apply coeff_tail_frame_step.
      - rewrite /mode2_row_words /mode2_active_words /=.
         smt(W64.to_uint_cmp).
      - exact hframe.
  wp.
  skip => &hr /=.
  move=> />.
  move=> hk0 hkle hoffeq hprefix hframe hguard.
  have hk1 : W64.to_uint k{hr} = 1.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /mode2_rows /=.
    smt(W64.to_uint_cmp).
  have hoff256 : W64.to_uint off{hr} = mode2_row_words.
  + rewrite hoffeq hk1 /mode2_row_words /=.
    trivial.
  split.
  + split; first exact hk1.
    exact hoff256.
  move=> j0 wp00 hdone _ _ hj0 hjle hprefix0 hframe0.
  have hjdone : W64.to_uint j0 = mode2_row_words.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /mode2_row_words /=.
    smt(W64.to_uint_cmp).
  have hkplus : W64.to_uint (k{hr} + W64.one) = mode2_rows.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1 hk1.
    rewrite /mode2_rows /=.
    trivial.
  have hoffplus :
      W64.to_uint (off{hr} + W64.of_int 256) = mode2_active_words.
  + rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
    rewrite hoff256 /mode2_row_words /mode2_active_words /=.
    trivial.
  have hsum :
      W64.to_uint off{hr} + W64.to_uint j0 = mode2_active_words.
  + rewrite hoff256 hjdone /mode2_row_words /mode2_active_words /=.
    trivial.
  split.
  + rewrite hkplus /mode2_rows /=.
    by auto.
  split.
  + rewrite hoffplus hkplus /mode2_rows /mode2_row_words
      /mode2_active_words /=.
    trivial.
  split.
  + rewrite hoffplus -hsum.
    exact hprefix0.
  + rewrite hoffplus -hsum.
    exact hframe0.
wp.
while
  (up = high0 /\ vp = wprime0 /\
   count = W64.of_int mode2_rows /\
   0 <= W64.to_uint j <= mode2_row_words /\
   fromcrt_prefix wp_0 high0 wprime0 (W64.to_uint j) /\
   coeff_tail_frame z10 wp_0 (W64.to_uint j)).
+ auto => />.
  move=> &hr hj0 hjle hprefix hframe hguard.
  have hjlt : W64.to_uint j{hr} < mode2_row_words.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /mode2_row_words /=.
    smt(W64.to_uint_cmp).
  have hnext :
      W64.to_uint (j{hr} + W64.one) = W64.to_uint j{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have hjrange : 0 <= W64.to_uint j{hr} < mode2_row_words by smt().
  split; first by rewrite hnext; smt(W64.to_uint_cmp).
  split.
  + rewrite hnext.
    apply (fromcrt_prefix_step _ _ _ (W64.to_uint j{hr})).
    * smt().
    * rewrite /mode2_fromcrt_word /mode2_fromcrt_add_xor /=.
      rewrite ifT 1:hjrange.
      trivial.
    * exact hprefix.
  + rewrite hnext.
    apply coeff_tail_frame_step; first by smt().
    exact hframe.
wp.
skip => &hr /=.
move=> />.
split.
+ exact (fromcrt_prefix_zero wp_0{hr} up{hr} vp{hr}).
+ move=> j0 wp00 hdone hj0 hjle hprefix hframe.
  have hjdone : W64.to_uint j0 = mode2_row_words.
  + move: hdone.
    rewrite W64.ultE W64.of_uintK /mode2_row_words /=.
    smt(W64.to_uint_cmp).
  have hjdone256 : W64.to_uint j0 = 256.
  + rewrite hjdone /mode2_row_words /=.
    trivial.
  split.
  + split.
    * rewrite -hjdone256.
      exact hprefix.
    * rewrite -hjdone256.
      exact hframe.
  + move=> k0 off0 wp01 hdone0 hk0 hkle hoffeq hprefix0 hframe0.
    have hkdone : W64.to_uint k0 = mode2_rows.
    + move: hdone0.
      rewrite W64.ultE W64.of_uintK /mode2_rows /=.
      smt(W64.to_uint_cmp).
    have hoffdone : W64.to_uint off0 = mode2_active_words.
    + rewrite hoffeq hkdone /mode2_row_words /mode2_rows
        /mode2_active_words /=.
      trivial.
    split.
    * by rewrite -hoffdone.
    * by rewrite -hoffdone.
qed.

module ActualVerifyCrtFreezeMode2 = {
  proc run (z1p : BArray8192.t, highp : BArray8192.t,
            wprimep : BArray1024.t) : BArray8192.t = {
    z1p <@ Verify._polyveck_poly_fromcrt (z1p, highp, wprimep,
                                          W64.of_int mode2_rows);
    z1p <@ Verify._polyvec_freeze2q (z1p, W64.of_int mode2_active_words);
    return z1p;
  }
}.

lemma verify_crt_freeze_mode2_word_exact
    (z10 high0 : BArray8192.t) (wprime0 : BArray1024.t) :
  hoare [ActualVerifyCrtFreezeMode2.run :
    z1p = z10 /\ highp = high0 /\ wprimep = wprime0
    ==>
    crt_freeze_prefix res high0 wprime0 mode2_active_words /\
    coeff_tail_frame z10 res mode2_active_words].
proof.
proc.
seq 1 :
  (exists mid,
     z1p = mid /\
     highp = high0 /\
     wprimep = wprime0 /\
     fromcrt_prefix mid high0 wprime0 mode2_active_words /\
     coeff_tail_frame z10 mid mode2_active_words).
+ call (polyveck_poly_fromcrt_mode2_word_exact z10 high0 wprime0).
  auto => />.
  move=> result hfrom hframe.
  exists result.
  by auto.
exlim z1p => mid0.
call (polyvec_freeze2q_mode2_word_exact mid0).
auto => />.
move=> &hr hfrom hframe result hfreeze hframe2.
split.
+ exact (crt_freeze_prefix_of_prefixes
    mid0 result highp{hr} wprimep{hr} mode2_active_words hfrom hfreeze).
+ exact (coeff_tail_frame_trans
    z10 mid0 result mode2_active_words hframe hframe2).
qed.

end VerifyCrtFreezeMode2PostFreeze.
