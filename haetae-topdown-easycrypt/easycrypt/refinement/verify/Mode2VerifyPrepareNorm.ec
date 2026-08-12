require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget.

theory Mode2VerifyPrepareNorm.

module Verify = VerifyCoreTarget.M.

op challenge_words : int = 256.
op low_words : int = 1024.
op mode2_hbz_offset : int = 6.
op mode2_hbz_alphabet : int = 13.
op mode2_verify_norm_words : int = 512.
op mode2_verify_norm_bound : int = 163265017.

op bitword (b : bool) : W32.t =
  if b then W32.one else W32.zero.

op sign_extend_byte (b : W8.t) : W32.t =
  ((zeroextu32 b) `<<` (W8.of_int 24)) `|>>` (W8.of_int 24).

op canonical_hbz_mode2 (hbz : BArray8192.t) : bool =
  forall i, 0 <= i < low_words =>
    -mode2_hbz_offset <= W32.to_sint (BArray8192.get32 hbz i) <
      mode2_hbz_alphabet - mode2_hbz_offset.

op canonical_signed_low (low : BArray8192.t) : bool =
  forall i, 0 <= i < low_words =>
    -128 <= W32.to_sint (BArray8192.get32 low i) < 128 /\
    BArray8192.get32 low i =
      sign_extend_byte (truncateu8 (BArray8192.get32 low i)).

op canonical_challenge (cp : BArray1024.t) : bool =
  forall i, 0 <= i < challenge_words =>
    0 <= W32.to_uint (BArray1024.get32 cp i) <= 1 /\
    BArray1024.get32 cp i =
      bitword (BArray1024.get32 cp i).[0].

op coeff_tail_frame
    (before after : BArray8192.t) (start : int) : bool =
  forall i, start <= i < 2048 =>
    BArray8192.get32 after i = BArray8192.get32 before i.

op verify_prepare_z1_word
    (highz lowz : BArray8192.t) (idx : int) : W32.t =
  ((BArray8192.get32 highz idx) `<<` (W8.of_int 8)) +
  BArray8192.get32 lowz idx.

op verify_prepare_wprime_word
    (highz lowz : BArray8192.t) (cp : BArray1024.t) (idx : int) : W32.t =
  (verify_prepare_z1_word highz lowz idx - BArray1024.get32 cp idx) `&`
  W32.one.

op verify_prepare_z1_prefix
    (outp highz lowz : BArray8192.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray8192.get32 outp i = verify_prepare_z1_word highz lowz i.

op verify_prepare_wprime_prefix
    (outp : BArray1024.t) (highz lowz : BArray8192.t)
    (cp : BArray1024.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray1024.get32 outp i = verify_prepare_wprime_word highz lowz cp i.

op wprime_tail_frame
    (before after : BArray1024.t) (start : int) : bool =
  forall i, start <= i < challenge_words =>
    BArray1024.get32 after i = BArray1024.get32 before i.

(* Exact word-level accumulator semantics only.  This file does not claim an
   integer no-wrap bridge for these W64 sums. *)
op verify_prepare_sqterm
    (highz lowz : BArray8192.t) (idx : int) : W64.t =
  let z = verify_prepare_z1_word highz lowz idx in
  (sigextu64 z) * (sigextu64 z).

op verify_prepare_total_prefix
    (highz lowz : BArray8192.t) (n : int) : W64.t =
  foldl
    (fun (acc : W64.t) (idx : int) => acc + verify_prepare_sqterm highz lowz idx)
    W64.zero (iota_ 0 n).

op verify_sqnorm2_term (ap : BArray8192.t) (idx : int) : W64.t =
  let a = BArray8192.get32 ap idx in
  (sigextu64 a) * (sigextu64 a).

op verify_sqnorm2_prefix (ap : BArray8192.t) (n : int) : W64.t =
  foldl
    (fun (acc : W64.t) (idx : int) => acc + verify_sqnorm2_term ap idx)
    W64.zero (iota_ 0 n).

op verify_norm_total_word (z2p : BArray8192.t) (z1norm : W64.t) : W64.t =
  z1norm + verify_sqnorm2_prefix z2p mode2_verify_norm_words.

op verify_norm_accepts_word (z2p : BArray8192.t) (z1norm : W64.t) : bool =
  ! (W64.of_int mode2_verify_norm_bound \ult verify_norm_total_word z2p z1norm).

lemma verify_prepare_z1_prefix_zero outp highz lowz :
  verify_prepare_z1_prefix outp highz lowz 0.
proof. rewrite /verify_prepare_z1_prefix; smt(). qed.

lemma verify_prepare_wprime_prefix_zero outp highz lowz cp :
  verify_prepare_wprime_prefix outp highz lowz cp 0.
proof. rewrite /verify_prepare_wprime_prefix; smt(). qed.

lemma wprime_tail_frame_refl wprime start :
  wprime_tail_frame wprime wprime start.
proof. rewrite /wprime_tail_frame; trivial. qed.

lemma coeff_tail_frame_set_before before after start idx value :
  0 <= idx < start =>
  coeff_tail_frame before after start =>
  coeff_tail_frame before (BArray8192.set32 after idx value) start.
proof.
move=> hidx hframe.
rewrite /coeff_tail_frame => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
rewrite ifF 1:/#.
apply hframe; exact hi.
qed.

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

lemma verify_prepare_z1_prefix_step outp highz lowz n :
  0 <= n < low_words =>
  verify_prepare_z1_prefix outp highz lowz n =>
  verify_prepare_z1_prefix
    (BArray8192.set32 outp n (verify_prepare_z1_word highz lowz n))
    highz lowz (n + 1).
proof.
move=> hn hp.
rewrite /verify_prepare_z1_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ rewrite ifF 1:/#.
   apply hp; smt().
qed.

lemma verify_prepare_wprime_prefix_step outp highz lowz cp n :
  0 <= n < challenge_words =>
  verify_prepare_wprime_prefix outp highz lowz cp n =>
  verify_prepare_wprime_prefix
    (BArray1024.set32 outp n (verify_prepare_wprime_word highz lowz cp n))
    highz lowz cp (n + 1).
proof.
move=> hn hp.
rewrite /verify_prepare_wprime_prefix => i hi.
rewrite BArray1024.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ rewrite ifF 1:/#.
   apply hp; smt().
qed.

lemma wprime_tail_frame_set_before before after start idx value :
  0 <= idx < start =>
  wprime_tail_frame before after start =>
  wprime_tail_frame before (BArray1024.set32 after idx value) start.
proof.
move=> hidx hframe.
rewrite /wprime_tail_frame => i hi.
rewrite BArray1024.get_set32E 1:/# 1:/#.
rewrite ifF 1:/#.
apply hframe; exact hi.
qed.

lemma wprime_tail_frame_step before after n value :
  0 <= n < challenge_words =>
  wprime_tail_frame before after n =>
  wprime_tail_frame before (BArray1024.set32 after n value) (n + 1).
proof.
move=> hn hframe.
rewrite /wprime_tail_frame => i hi.
rewrite BArray1024.get_set32E 1:/# 1:/#.
rewrite ifF 1:/#.
apply hframe; smt().
qed.

lemma verify_prepare_total_prefix_step highz lowz n :
  0 <= n =>
  verify_prepare_total_prefix highz lowz (n + 1) =
  verify_prepare_total_prefix highz lowz n + verify_prepare_sqterm highz lowz n.
proof.
move=> hn.
rewrite /verify_prepare_total_prefix (iotaSr 0 n) 1:hn.
rewrite foldl_rcons /=.
trivial.
qed.

lemma verify_sqnorm2_prefix_step ap n :
  0 <= n =>
  verify_sqnorm2_prefix ap (n + 1) =
  verify_sqnorm2_prefix ap n + verify_sqnorm2_term ap n.
proof.
move=> hn.
rewrite /verify_sqnorm2_prefix (iotaSr 0 n) 1:hn.
rewrite foldl_rcons /=.
trivial.
qed.

lemma verify_prepare_z1_wprime_mode2_word_exact
    (z10 highz0 lowz0 : BArray8192.t)
    (wprime0 cp0 : BArray1024.t) :
  hoare [Verify._verify_prepare_z1_wprime :
    z1p = z10 /\ wprimep = wprime0 /\ highzp = highz0 /\ lowzp = lowz0 /\
    cp = cp0 /\ lcount = W64.of_int low_words
    ==>
    verify_prepare_z1_prefix res.`1 highz0 lowz0 low_words /\
    coeff_tail_frame z10 res.`1 low_words /\
    verify_prepare_wprime_prefix res.`2 highz0 lowz0 cp0 challenge_words /\
    wprime_tail_frame wprime0 res.`2 challenge_words /\
    res.`3 = verify_prepare_total_prefix highz0 lowz0 low_words].
proof.
proc.
while
  (highzp = highz0 /\ lowzp = lowz0 /\ cp = cp0 /\
   lcount = W64.of_int low_words /\
   0 <= W64.to_uint i <= low_words /\
   verify_prepare_z1_prefix z1p highz0 lowz0 (W64.to_uint i) /\
   coeff_tail_frame z10 z1p (W64.to_uint i) /\
   verify_prepare_wprime_prefix
     wprimep highz0 lowz0 cp0 (min (W64.to_uint i) challenge_words) /\
   wprime_tail_frame wprime0 wprimep (min (W64.to_uint i) challenge_words) /\
   total = verify_prepare_total_prefix highz0 lowz0 (W64.to_uint i)).
+ auto => /> &hr hi0 hile hzprefix hzframe hwprefix hwframe hguard.
  have hilt : W64.to_uint i{hr} < low_words.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hi_next :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  have hsq :
      verify_prepare_total_prefix highz0 lowz0
        (W64.to_uint (i{hr} + W64.one)) =
      verify_prepare_total_prefix highz0 lowz0 (W64.to_uint i{hr}) +
      verify_prepare_sqterm highz0 lowz0 (W64.to_uint i{hr}).
  + rewrite hi_next.
    apply verify_prepare_total_prefix_step.
    smt(W64.to_uint_cmp).
  split.
  + move=> hbranch.
    have hch : W64.to_uint i{hr} < challenge_words.
    * move: hbranch.
      rewrite W64.ultE W64.of_uintK /challenge_words /=.
      smt(W64.to_uint_cmp).
    split; first by rewrite hi_next; smt(W64.to_uint_cmp).
    split.
    * rewrite hi_next.
      apply verify_prepare_z1_prefix_step; first by smt().
      exact hzprefix.
    split.
    * rewrite hi_next.
      apply coeff_tail_frame_step; first by smt().
      exact hzframe.
    split.
    * rewrite hi_next.
      have hmin_old :
          min (W64.to_uint i{hr}) challenge_words = W64.to_uint i{hr}
        by smt().
      have hmin_new :
          min (W64.to_uint i{hr} + 1) challenge_words = W64.to_uint i{hr} + 1
        by smt().
      rewrite hmin_new.
      apply verify_prepare_wprime_prefix_step; first by smt().
      move: hwprefix; by rewrite hmin_old.
    split.
    * rewrite hi_next.
      have hmin_old :
          min (W64.to_uint i{hr}) challenge_words = W64.to_uint i{hr}
        by smt().
      have hmin_new :
          min (W64.to_uint i{hr} + 1) challenge_words = W64.to_uint i{hr} + 1
        by smt().
      rewrite hmin_new.
      apply wprime_tail_frame_step; first by smt().
      move: hwframe; by rewrite hmin_old.
    * by rewrite hsq.
  + move=> hbranch.
    have hnch : challenge_words <= W64.to_uint i{hr}.
    * move: hbranch.
      rewrite W64.ultE W64.of_uintK /challenge_words /=.
      smt(W64.to_uint_cmp).
    split; first by rewrite hi_next; smt(W64.to_uint_cmp).
    split.
    * rewrite hi_next.
      apply verify_prepare_z1_prefix_step; first by smt().
      exact hzprefix.
    split.
    * rewrite hi_next.
      apply coeff_tail_frame_step; first by smt().
      exact hzframe.
    split.
    * rewrite hi_next.
      have hmin_old : min (W64.to_uint i{hr}) challenge_words = challenge_words
        by smt().
      have hmin_new :
          min (W64.to_uint i{hr} + 1) challenge_words = challenge_words
        by smt().
      rewrite hmin_new.
      move: hwprefix; by rewrite hmin_old.
    split.
    * rewrite hi_next.
      have hmin_old : min (W64.to_uint i{hr}) challenge_words = challenge_words
        by smt().
      have hmin_new :
          min (W64.to_uint i{hr} + 1) challenge_words = challenge_words
        by smt().
      rewrite hmin_new.
      move: hwframe; by rewrite hmin_old.
    * by rewrite hsq.
+ auto => />.
  split.
  + split.
    * exact (verify_prepare_z1_prefix_zero z10 highz0 lowz0).
    split.
    * rewrite /min.
      exact (verify_prepare_wprime_prefix_zero wprime0 highz0 lowz0 cp0).
    * by rewrite /verify_prepare_total_prefix iota0.
  + move=> i0 wprimep0 z1p0 hdone hi0 hile
           hzprefix hzframe hwprefix hwframe.
    have hieq : W64.to_uint i0 = low_words.
    + move: hdone.
      rewrite W64.ultE W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    have hmin : min (W64.to_uint i0) challenge_words = challenge_words.
    + rewrite hieq /low_words /challenge_words /=.
      trivial.
    smt().
qed.

(* (V-1), independently projected from the actual prepare helper.  The
   theorem is universal over decoded arrays, so in particular it applies at
   the canonical decoded x/v boundary without importing parser machinery. *)
lemma verify_prepare_z1_mode2_word_exact
    (z10 x0 v0 : BArray8192.t)
    (wprime0 c0 : BArray1024.t) :
  hoare [Verify._verify_prepare_z1_wprime :
    z1p = z10 /\ wprimep = wprime0 /\ highzp = x0 /\ lowzp = v0 /\
    cp = c0 /\ lcount = W64.of_int low_words
    ==>
    verify_prepare_z1_prefix res.`1 x0 v0 low_words /\
    coeff_tail_frame z10 res.`1 low_words].
proof.
conseq (verify_prepare_z1_wprime_mode2_word_exact z10 x0 v0 wprime0 c0) => //=.
qed.

(* (V-2), independently projected from the same actual helper. *)
lemma verify_prepare_wprime_mode2_word_exact
    (z10 x0 v0 : BArray8192.t)
    (wprime0 c0 : BArray1024.t) :
  hoare [Verify._verify_prepare_z1_wprime :
    z1p = z10 /\ wprimep = wprime0 /\ highzp = x0 /\ lowzp = v0 /\
    cp = c0 /\ lcount = W64.of_int low_words
    ==>
    verify_prepare_wprime_prefix res.`2 x0 v0 c0 challenge_words /\
    wprime_tail_frame wprime0 res.`2 challenge_words].
proof.
conseq (verify_prepare_z1_wprime_mode2_word_exact z10 x0 v0 wprime0 c0) => //=.
qed.

lemma polyvec_sqnorm2_mode2_word_accumulator (z20 : BArray8192.t) :
  hoare [Verify._polyvec_sqnorm2 :
    ap = z20 /\ count = W64.of_int mode2_verify_norm_words
    ==>
    res = verify_sqnorm2_prefix z20 mode2_verify_norm_words].
proof.
proc.
while
  (ap = z20 /\ count = W64.of_int mode2_verify_norm_words /\
   0 <= W64.to_uint i <= mode2_verify_norm_words /\
   total = verify_sqnorm2_prefix z20 (W64.to_uint i)).
+ auto => />.
  move=> &hr hi0 hile hguard.
  have hilt : W64.to_uint i{hr} < mode2_verify_norm_words.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hi_next :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  split; first by rewrite hi_next; smt(W64.to_uint_cmp).
  by rewrite hi_next verify_sqnorm2_prefix_step 1:/#.
+ auto => />.
  split.
  + by rewrite /verify_sqnorm2_prefix iota0.
  + move=> i0 hdone hi0 hile.
    have hieq : W64.to_uint i0 = mode2_verify_norm_words.
    + move: hdone.
      rewrite W64.ultE W64.of_uintK /=.
      smt(W64.to_uint_cmp).
    by rewrite hieq.
qed.

lemma sign_verify_norm_reject_mode2_word_exact
    (z20 : BArray8192.t) (z1norm0 : W64.t) :
  hoare [Verify._sign_verify_norm_reject :
    z2p = z20 /\ z1norm = z1norm0 /\
    kcount = W64.of_int mode2_verify_norm_words /\
    bound = W64.of_int mode2_verify_norm_bound
    ==>
    (res = W64.zero <=> verify_norm_accepts_word z20 z1norm0) /\
    (res = W64.one <=>
      W64.of_int mode2_verify_norm_bound \ult verify_norm_total_word z20 z1norm0)].
proof.
proc.
wp.
call (polyvec_sqnorm2_mode2_word_accumulator z20).
auto => />.
rewrite /verify_norm_accepts_word /verify_norm_total_word.
rewrite /protect_64 /=.
smt().
qed.

end Mode2VerifyPrepareNorm.
