require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget.

theory Mode2VerifyRecover.

module Verify = VerifyCoreTarget.M.

op mode2_verify_recover_count : int = 512.
op mode2_verify_recover_wprime_count : int = 256.
op mode2_verify_recover_half_alpha : int = 256.
op mode2_verify_recover_log_alpha : int = 9.
op mode2_verify_recover_bound : int = 252.
op mode2_verify_recover_alpha : int = 512.

op mode2_recover_w_word (high : W32.t) (hintw : W32.t) : W32.t =
  (let w0 = high in
   let w1 = w0 + W32.of_int mode2_verify_recover_half_alpha in
   let w2 = w1 `|>>` W8.of_int mode2_verify_recover_log_alpha in
   let edge0 = W32.of_int mode2_verify_recover_bound in
   let edge1 = edge0 - w2 in
   let edge2 = edge1 - W32.of_int 1 in
   let edge3 = edge2 `|>>` W8.of_int 31 in
   let sub0 = edge3 `&` W32.of_int mode2_verify_recover_bound in
   let w3 = w2 - sub0 in
   let w4 = w3 + hintw in
   let sub1 = w4 - W32.of_int mode2_verify_recover_bound in
   let sub2 = sub1 `|>>` W8.of_int 31 in
   let mask = W32.zero - W32.of_int 1 in
   let sub3 = (sub2 `^` mask) `&` W32.of_int mode2_verify_recover_bound in
   w4 - sub3).

op mode2_recover_add_word (i : int) (wprime : BArray1024.t) : W32.t =
  if 0 <= i < mode2_verify_recover_wprime_count
  then BArray1024.get32 wprime i
  else W32.zero.

op reduce32_2q_word (a : W32.t) : W32.t =
  (let x0 = sigextu64 a in
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
   let mask4 = (x3 - W64.of_int 64513) `|>>` W8.of_int 31 in
   let mask5 = truncateu32 mask4 in
   let mask6 = (mask5 + W32.of_int 1) * W32.of_int 129026 in
   let x4 = x3 - zeroextu64 mask6 in
   truncateu32 x4).

op mode2_recover_z2_raw_word
    (i : int) (high : W32.t) (hintw : W32.t) (wprime : BArray1024.t) : W32.t =
  (let w = mode2_recover_w_word high hintw in
   let z0 = w * W32.of_int mode2_verify_recover_alpha in
   let z1 = z0 - high in
   z1 + mode2_recover_add_word i wprime).

op mode2_recover_z2_word
    (i : int) (high : W32.t) (hintw : W32.t) (wprime : BArray1024.t) : W32.t =
  reduce32_2q_word (mode2_recover_z2_raw_word i high hintw wprime)
  `|>>` W8.of_int 1.

op recover_w_prefix (wout : BArray8192.t) (high : BArray8192.t)
    (hparr : BArray8192.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray8192.get32 wout i =
      mode2_recover_w_word
        (BArray8192.get32 high i)
        (BArray8192.get32 hparr i).

op recover_z2_prefix
    (z2 : BArray8192.t) (high : BArray8192.t) (hparr : BArray8192.t)
    (wprime : BArray1024.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray8192.get32 z2 i =
      mode2_recover_z2_word
        i
        (BArray8192.get32 high i)
        (BArray8192.get32 hparr i)
        wprime.

lemma recover_w_prefix_zero wout0 high0 hparr0 :
  recover_w_prefix wout0 high0 hparr0 0.
proof. rewrite /recover_w_prefix; smt(). qed.

lemma recover_z2_prefix_zero z20 high0 hparr0 wprime0 :
  recover_z2_prefix z20 high0 hparr0 wprime0 0.
proof. rewrite /recover_z2_prefix; smt(). qed.

lemma recover_w_prefix_step wout0 high0 hparr0 n value :
  0 <= n < 2048 =>
  value =
    mode2_recover_w_word
      (BArray8192.get32 high0 n)
      (BArray8192.get32 hparr0 n) =>
  recover_w_prefix wout0 high0 hparr0 n =>
  recover_w_prefix (BArray8192.set32 wout0 n value) high0 hparr0 (n + 1).
proof.
move=> hn hvalue hprefix.
rewrite /recover_w_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ rewrite ifF 1:/#.
   apply hprefix; smt().
qed.

lemma recover_z2_prefix_step z20 high0 hparr0 wprime0 n value :
  0 <= n < 2048 =>
  value =
    mode2_recover_z2_word
      n
      (BArray8192.get32 high0 n)
      (BArray8192.get32 hparr0 n)
      wprime0 =>
  recover_z2_prefix z20 high0 hparr0 wprime0 n =>
  recover_z2_prefix (BArray8192.set32 z20 n value) high0 hparr0 wprime0 (n + 1).
proof.
move=> hn hvalue hprefix.
rewrite /recover_z2_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ rewrite ifF 1:/#.
   apply hprefix; smt().
qed.

lemma reduce32_2q_word_correct (a0 : W32.t) :
  hoare [Verify.__reduce32_2q :
    a = a0
    ==>
    res = reduce32_2q_word a0].
proof.
proc.
auto => />.
qed.

lemma actual_sign_verify_recover_w_z2_mode2_word_semantics
    (wp0_0 z20 high0 hp0 : BArray8192.t) (wprime0 : BArray1024.t) :
  hoare [Verify._sign_verify_recover_w_z2 :
    wp_0 = wp0_0 /\
    z2p = z20 /\
    highp = high0 /\
    hp = hp0 /\
    wprimep = wprime0 /\
    count = W64.of_int mode2_verify_recover_count /\
    half_alpha = mode2_verify_recover_half_alpha /\
    log_alpha = mode2_verify_recover_log_alpha /\
    bound = mode2_verify_recover_bound /\
    alpha = mode2_verify_recover_alpha
    ==>
    recover_w_prefix res.`1 high0 hp0 mode2_verify_recover_count /\
    recover_z2_prefix res.`2 high0 hp0 wprime0 mode2_verify_recover_count].
proof.
proc.
while
  (highp = high0 /\
   hp = hp0 /\
   wprimep = wprime0 /\
   count = W64.of_int mode2_verify_recover_count /\
   half_alpha = mode2_verify_recover_half_alpha /\
   log_alpha = mode2_verify_recover_log_alpha /\
   bound = mode2_verify_recover_bound /\
   alpha = mode2_verify_recover_alpha /\
   0 <= W64.to_uint i <= mode2_verify_recover_count /\
   recover_w_prefix wp_0 high0 hp0 (W64.to_uint i) /\
   recover_z2_prefix z2p high0 hp0 wprime0 (W64.to_uint i)).
+ inline Verify.__reduce32_2q.
  auto => /> &hr hi0 hile hpw hpz hguard.
  have hlt : W64.to_uint i{hr} < mode2_verify_recover_count.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  have hnext :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt(W64.to_uint_cmp).
  split.
  + move=> hbranch.
    have hch : 0 <= W64.to_uint i{hr} < mode2_verify_recover_wprime_count.
    * split; first by smt(W64.to_uint_cmp).
      move: hbranch.
      rewrite W64.ultE W64.of_uintK
              /mode2_verify_recover_wprime_count /=.
      smt(W64.to_uint_cmp).
    split; first by rewrite hnext; smt().
    split.
    * rewrite hnext.
      apply (recover_w_prefix_step _ _ _ (W64.to_uint i{hr})).
      - smt().
      - rewrite /mode2_recover_w_word
                /mode2_verify_recover_half_alpha
                /mode2_verify_recover_log_alpha
                /mode2_verify_recover_bound /=.
        trivial.
      - exact hpw.
    * rewrite hnext.
      apply (recover_z2_prefix_step _ _ _ _ (W64.to_uint i{hr})).
      - smt().
      - rewrite /mode2_recover_z2_word /mode2_recover_z2_raw_word
                /mode2_recover_add_word /reduce32_2q_word
                /mode2_recover_w_word
                /mode2_verify_recover_wprime_count
                /mode2_verify_recover_half_alpha
                /mode2_verify_recover_log_alpha
                /mode2_verify_recover_bound
                /mode2_verify_recover_alpha /=.
        rewrite ifT 1:hch.
        trivial.
      - exact hpz.
  + move=> hbranch.
    have hnch : ! (0 <= W64.to_uint i{hr} < mode2_verify_recover_wprime_count).
    * move: hbranch.
      rewrite W64.ultE W64.of_uintK
              /mode2_verify_recover_wprime_count /=.
      smt(W64.to_uint_cmp).
    split; first by rewrite hnext; smt().
    split.
    * rewrite hnext.
      apply (recover_w_prefix_step _ _ _ (W64.to_uint i{hr})).
      - smt().
      - rewrite /mode2_recover_w_word
                /mode2_verify_recover_half_alpha
                /mode2_verify_recover_log_alpha
                /mode2_verify_recover_bound /=.
        trivial.
      - exact hpw.
    * rewrite hnext.
      apply (recover_z2_prefix_step _ _ _ _ (W64.to_uint i{hr})).
      - smt().
      - rewrite /mode2_recover_z2_word /mode2_recover_z2_raw_word
                /mode2_recover_add_word /reduce32_2q_word
                /mode2_recover_w_word
                /mode2_verify_recover_wprime_count
                /mode2_verify_recover_half_alpha
                /mode2_verify_recover_log_alpha
                /mode2_verify_recover_bound
                /mode2_verify_recover_alpha /=.
        rewrite ifF 1:hnch.
        trivial.
        trivial.
      - exact hpz.
auto => />.
split.
+ split.
  * exact (recover_w_prefix_zero wp0_0 high0 hp0).
  * exact (recover_z2_prefix_zero z20 high0 hp0 wprime0).
+ move=> i0 wp_00 z2p0 hdone hi hile hpw hpz.
  have hieq : W64.to_uint i0 = mode2_verify_recover_count by
    smt(W64.to_uint_cmp).
  rewrite -hieq.
  split.
  * exact hpw.
  * exact hpz.
qed.

(* (V-5), independently projected from the actual recover helper. *)
lemma actual_sign_verify_recover_w_mode2_word_semantics
    (wp0_0 z20 high0 hp0 : BArray8192.t) (wprime0 : BArray1024.t) :
  hoare [Verify._sign_verify_recover_w_z2 :
    wp_0 = wp0_0 /\ z2p = z20 /\ highp = high0 /\ hp = hp0 /\
    wprimep = wprime0 /\
    count = W64.of_int mode2_verify_recover_count /\
    half_alpha = mode2_verify_recover_half_alpha /\
    log_alpha = mode2_verify_recover_log_alpha /\
    bound = mode2_verify_recover_bound /\
    alpha = mode2_verify_recover_alpha
    ==>
    recover_w_prefix res.`1 high0 hp0 mode2_verify_recover_count].
proof.
conseq
  (actual_sign_verify_recover_w_z2_mode2_word_semantics
    wp0_0 z20 high0 hp0 wprime0) => //=.
qed.

(* (V-6), independently projected at exact machine-word level.  The
   word/integer parity-and-centering bridge remains an explicit downstream
   obligation and is not smuggled into this theorem's precondition. *)
lemma actual_sign_verify_recover_z2_mode2_word_semantics
    (wp0_0 z20 high0 hp0 : BArray8192.t) (wprime0 : BArray1024.t) :
  hoare [Verify._sign_verify_recover_w_z2 :
    wp_0 = wp0_0 /\ z2p = z20 /\ highp = high0 /\ hp = hp0 /\
    wprimep = wprime0 /\
    count = W64.of_int mode2_verify_recover_count /\
    half_alpha = mode2_verify_recover_half_alpha /\
    log_alpha = mode2_verify_recover_log_alpha /\
    bound = mode2_verify_recover_bound /\
    alpha = mode2_verify_recover_alpha
    ==>
    recover_z2_prefix res.`2 high0 hp0 wprime0
      mode2_verify_recover_count].
proof.
conseq
  (actual_sign_verify_recover_w_z2_mode2_word_semantics
    wp0_0 z20 high0 hp0 wprime0) => //=.
qed.

end Mode2VerifyRecover.
