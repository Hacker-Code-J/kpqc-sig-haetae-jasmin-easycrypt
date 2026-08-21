require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget Mode2VerifyPrepareNorm.

theory VerifyChallengeM23SamplerStructurePostFreeze.

module Verify = VerifyCoreTarget.M.

op mode2_tau : int = 58.
op challenge_words : int = Mode2VerifyPrepareNorm.challenge_words.

op zero_challenge_prefix (cp : BArray1024.t) (n : int) : bool =
  forall i, 0 <= i < n => BArray1024.get32 cp i = W32.of_int 0.

op challenge_shuffle_update
    (cp : BArray1024.t) (i bidx : int) : BArray1024.t =
  BArray1024.set32
    (BArray1024.set32 cp i (BArray1024.get32 cp bidx))
    bidx (W32.of_int 1).

lemma zero_word_canonical :
  0 <= W32.to_uint (W32.of_int 0) <= 1 /\
  W32.of_int 0 =
    Mode2VerifyPrepareNorm.bitword (W32.of_int 0).[0].
proof.
rewrite W32.to_uint0 /Mode2VerifyPrepareNorm.bitword W32.zerowE /=.
smt().
qed.

lemma one_word_canonical :
  0 <= W32.to_uint (W32.of_int 1) <= 1 /\
  W32.of_int 1 =
    Mode2VerifyPrepareNorm.bitword (W32.of_int 1).[0].
proof.
rewrite W32.to_uint1 /Mode2VerifyPrepareNorm.bitword /= W32.nth_one.
smt().
qed.

lemma zero_challenge_prefix_zero cp :
  zero_challenge_prefix cp 0.
proof. rewrite /zero_challenge_prefix; smt(). qed.

lemma zero_challenge_prefix_step cp n :
  0 <= n < challenge_words =>
  zero_challenge_prefix cp n =>
  zero_challenge_prefix (BArray1024.set32 cp n (W32.of_int 0)) (n + 1).
proof.
move=> hn hzero.
rewrite /zero_challenge_prefix => i hi.
rewrite BArray1024.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ by rewrite ifF 1:/#; apply hzero; smt().
qed.

lemma zero_challenge_prefix_canonical cp :
  zero_challenge_prefix cp challenge_words =>
  Mode2VerifyPrepareNorm.canonical_challenge cp.
proof.
move=> hzero.
rewrite /Mode2VerifyPrepareNorm.canonical_challenge => i hi.
rewrite hzero 1:hi.
exact zero_word_canonical.
qed.

lemma canonical_challenge_shuffle_update
    (cp : BArray1024.t) (i bidx : int) :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  0 <= i < challenge_words =>
  0 <= bidx <= i =>
  Mode2VerifyPrepareNorm.canonical_challenge
    (challenge_shuffle_update cp i bidx).
proof.
move=> hcanon hi hbidx.
rewrite /Mode2VerifyPrepareNorm.canonical_challenge
        /challenge_shuffle_update => j hj.
rewrite !BArray1024.get_set32E 1:/# 1:/# 1:/# 1:/#.
case (j = bidx) => hjbidx.
+ subst j.
   rewrite ifT 1:/#.
   exact one_word_canonical.
+ rewrite ifF 1:/#.
   case (j = i) => hji.
   + subst j.
     rewrite ifT 1:/#.
     have hsrc := hcanon bidx _.
     * smt().
     exact hsrc.
   + rewrite ifF 1:/#.
     exact (hcanon j hj).
qed.

lemma poly_challenge_m23_init_zero_prefix
    (cp0 : BArray1024.t) :
  hoare [Verify._poly_challenge_m23_init :
    cp = cp0 ==>
    zero_challenge_prefix res challenge_words].
proof.
proc.
while
  (0 <= W64.to_uint i <= challenge_words /\
   zero_challenge_prefix cp (W64.to_uint i)).
+ auto => /> &hr hi0 hile hprefix hguard.
  have hilt : W64.to_uint i{hr} < challenge_words.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK
            /challenge_words /Mode2VerifyPrepareNorm.challenge_words /=.
    smt(W64.to_uint_cmp).
  have hnext :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    trivial.
  split; first by rewrite hnext; smt(W64.to_uint_cmp).
  rewrite hnext.
  apply zero_challenge_prefix_step; first by smt(W64.to_uint_cmp).
  exact hprefix.
+ auto => />.
  split.
  + exact (zero_challenge_prefix_zero cp0).
  + move=> cp1 i0 hdone hi0 hile hprefix.
    rewrite /zero_challenge_prefix => j hj.
    apply hprefix.
    smt(W64.to_uint_cmp).
qed.

lemma poly_challenge_m23_init_canonical
    (cp0 : BArray1024.t) :
  hoare [Verify._poly_challenge_m23_init :
    cp = cp0 ==>
    Mode2VerifyPrepareNorm.canonical_challenge res].
proof.
conseq (poly_challenge_m23_init_zero_prefix cp0) => //=.
move=> &hr _ result hzero.
exact (zero_challenge_prefix_canonical result hzero).
qed.

(* Structural partial correctness only: absorb and squeeze are deliberately
   opaque here.  This proves the actual tau-58 shuffle can return only a
   canonical 0/1 challenge; it does not claim sampler termination or identify
   the squeezed stream with the paper challenge hash. *)
lemma verify_challenge_m23_tau58_canonical :
  hoare [Verify.__verify_challenge_m23 :
    tau = W64.of_int mode2_tau ==>
    Mode2VerifyPrepareNorm.canonical_challenge res].
proof.
proc.
while
  (tau = W64.of_int mode2_tau /\
   Mode2VerifyPrepareNorm.canonical_challenge cp /\
   W64.to_uint i <= challenge_words /\
   W64.to_uint pos <= 136).
+ seq 1 :
    (tau = W64.of_int mode2_tau /\
     Mode2VerifyPrepareNorm.canonical_challenge cp /\
     W64.to_uint i < challenge_words /\
     W64.to_uint pos < 136).
  + if.
    + wp.
      call (_ : true ==> true); first by auto.
      auto => />.
      rewrite /protect_ptr.
      smt(W64.to_uint_cmp).
    + auto => />.
      move=> &hr hcanonical hi hpos hloop hnot.
      move: hnot; rewrite W64.uleE W64.of_uintK /=.
      smt(W64.to_uint_cmp).
  + wp.
    auto => />.
    move=> &hr hcanonical hi hpos.
    split.
    + move=> hacc.
      split.
      * rewrite /protect_64 in hacc.
        rewrite /protect_64.
        change
          (Mode2VerifyPrepareNorm.canonical_challenge
            (challenge_shuffle_update
              cp{hr} (W64.to_uint i{hr})
              (W64.to_uint
                (zeroextu64
                  (zeroextu32
                    (BArray136.get8 bp{hr} (W64.to_uint pos{hr}))))))).
        apply canonical_challenge_shuffle_update.
        - exact hcanonical.
        - smt(W64.to_uint_cmp).
        - move: hacc.
          rewrite W64.ultE W64.to_uintD_small 1:/# W64.to_uint1.
          smt(W64.to_uint_cmp).
      * split.
        - rewrite W64.to_uintD_small 1:/# W64.to_uint1.
          smt(W64.to_uint_cmp).
        - rewrite W64.to_uintD_small 1:/# W64.to_uint1.
          smt(W64.to_uint_cmp).
    + move=> _.
      rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      smt(W64.to_uint_cmp).
+ wp.
  exlim cp => cp0.
  call (poly_challenge_m23_init_canonical cp0).
  wp.
  call (_ : true ==> true); first by auto.
  call (_ : true ==> true); first by auto.
  auto => />.
qed.

end VerifyChallengeM23SamplerStructurePostFreeze.
