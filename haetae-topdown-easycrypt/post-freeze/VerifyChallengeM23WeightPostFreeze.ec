require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyCoreTarget Mode2VerifyPrepareNorm
               VerifyChallengeM23SamplerStructurePostFreeze.

theory VerifyChallengeM23WeightPostFreeze.

module Verify = VerifyCoreTarget.M.

op challenge_words : int =
  VerifyChallengeM23SamplerStructurePostFreeze.challenge_words.
op mode2_tau : int =
  VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau.
op mode2_start : int = challenge_words - mode2_tau.

op challenge_shuffle_update
    (cp : BArray1024.t) (i bidx : int) : BArray1024.t =
  VerifyChallengeM23SamplerStructurePostFreeze.challenge_shuffle_update
    cp i bidx.

op challenge_prefix_weight (cp : BArray1024.t) (n : int) : int =
  foldl
    (fun total i => total + W32.to_uint (BArray1024.get32 cp i))
    0 (iota_ 0 n).

op challenge_weight (cp : BArray1024.t) : int =
  challenge_prefix_weight cp challenge_words.

op challenge_tail_zero (cp : BArray1024.t) (start : int) : bool =
  forall i, start <= i < challenge_words =>
    BArray1024.get32 cp i = W32.of_int 0.

lemma challenge_prefix_weight0 cp :
  challenge_prefix_weight cp 0 = 0.
proof. by rewrite /challenge_prefix_weight iota0. qed.

lemma challenge_prefix_weight_step cp n :
  0 <= n =>
  challenge_prefix_weight cp (n + 1) =
  challenge_prefix_weight cp n +
    W32.to_uint (BArray1024.get32 cp n).
proof.
move=> hn.
by rewrite /challenge_prefix_weight iotaSr 1:hn foldl_rcons.
qed.

lemma challenge_prefix_weight_ext cp1 cp2 n :
  0 <= n =>
  (forall i, 0 <= i < n =>
    BArray1024.get32 cp1 i = BArray1024.get32 cp2 i) =>
  challenge_prefix_weight cp1 n = challenge_prefix_weight cp2 n.
proof.
move=> hn.
elim: n hn => [|n hn ih].
+ move=> _; by rewrite !challenge_prefix_weight0.
+ move=> heq.
  rewrite !challenge_prefix_weight_step 1..2:/#.
  rewrite (ih _).
  + move=> i hi.
    apply heq.
    smt().
  + by rewrite heq 1:/#.
qed.

lemma challenge_prefix_weight_set_outside cp n idx value :
  0 <= n <= idx =>
  0 <= idx < challenge_words =>
  challenge_prefix_weight (BArray1024.set32 cp idx value) n =
  challenge_prefix_weight cp n.
proof.
move=> hn hidx.
apply challenge_prefix_weight_ext; first by smt().
move=> i hi.
have hget :
    BArray1024.get32 (BArray1024.set32 cp idx value) i =
    if idx = i then value else BArray1024.get32 cp i.
+ change
    (BArray1024.get32d (BArray1024.set32d cp (4 * idx) value) (4 * i) =
     if idx = i then value else BArray1024.get32d cp (4 * i)).
  by rewrite BArray1024.get_set32E 1:/# 1:/#.
by rewrite hget ifF 1:/#.
qed.

lemma challenge_prefix_weight_set_inside cp n idx value :
  0 <= idx < n <= challenge_words =>
  challenge_prefix_weight (BArray1024.set32 cp idx value) n =
  challenge_prefix_weight cp n -
    W32.to_uint (BArray1024.get32 cp idx) + W32.to_uint value.
proof.
elim/natind: n => [n hn|n hn ih].
+ smt().
+ move=> hidxn.
  rewrite !challenge_prefix_weight_step 1..2:/#.
  case: (idx = n) => heq.
  + subst idx.
    rewrite challenge_prefix_weight_set_outside 1:/# 1:/#.
    rewrite BArray1024.get_set32E 1:/# 1:/# /=.
    ring.
  + rewrite (ih _).
    * smt().
    rewrite BArray1024.get_set32E 1:/# 1:/# ifF 1:/#.
    ring.
qed.

lemma zero_prefix_weight cp n :
  0 <= n <= challenge_words =>
  VerifyChallengeM23SamplerStructurePostFreeze.zero_challenge_prefix cp n =>
  challenge_prefix_weight cp n = 0.
proof.
elim/natind: n => [n hn|n hn ih].
+ smt().
+ move=> hbound hzero.
  rewrite challenge_prefix_weight_step 1:/#.
  rewrite (ih _).
  + smt().
  + move=> i hi.
    apply hzero.
    smt().
  rewrite hzero 1:/# W32.to_uint0.
  trivial.
qed.

lemma zero_prefix_tail_zero cp start :
  0 <= start <= challenge_words =>
  VerifyChallengeM23SamplerStructurePostFreeze.zero_challenge_prefix
    cp challenge_words =>
  challenge_tail_zero cp start.
proof.
move=> hstart hzero i hi.
apply hzero.
smt().
qed.

lemma challenge_shuffle_update_canonical cp i bidx :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  0 <= i < challenge_words =>
  0 <= bidx <= i =>
  Mode2VerifyPrepareNorm.canonical_challenge
    (challenge_shuffle_update cp i bidx).
proof.
move=> hcanonical hi hbidx.
apply
  VerifyChallengeM23SamplerStructurePostFreeze.canonical_challenge_shuffle_update.
+ exact hcanonical.
+ exact hi.
+ exact hbidx.
qed.

lemma challenge_shuffle_update_tail_zero cp i bidx :
  0 <= bidx <= i < challenge_words =>
  challenge_tail_zero cp i =>
  challenge_tail_zero
    (challenge_shuffle_update cp i bidx)
    (i + 1).
proof.
move=> hbidx htail.
rewrite /challenge_tail_zero in htail.
rewrite /challenge_tail_zero => j hj.
rewrite /challenge_shuffle_update
        /VerifyChallengeM23SamplerStructurePostFreeze.challenge_shuffle_update.
rewrite !BArray1024.get_set32E 1:/# 1:/# 1:/# 1:/#.
rewrite !ifF; smt().
qed.

lemma challenge_shuffle_update_weight_step cp i bidx :
  0 <= bidx <= i < challenge_words =>
  challenge_tail_zero cp i =>
  challenge_prefix_weight
    (challenge_shuffle_update cp i bidx)
    (i + 1) =
  challenge_prefix_weight cp i + 1.
proof.
move=> hbidx htail.
rewrite /challenge_tail_zero in htail.
have hcpi : BArray1024.get32 cp i = W32.zero.
+ apply htail; smt().
pose old := BArray1024.get32 cp bidx.
pose cp1 := BArray1024.set32 cp i old.
have hcp1b : BArray1024.get32 cp1 bidx = old.
+ rewrite /cp1 /old BArray1024.get_set32E 1:/# 1:/#.
  case: (i = bidx) => //=.
have hw0 : challenge_prefix_weight cp (i + 1) =
    challenge_prefix_weight cp i.
+ rewrite challenge_prefix_weight_step 1:/# hcpi W32.to_uint0.
  ring.
have hw1 : challenge_prefix_weight cp1 (i + 1) =
    challenge_prefix_weight cp i + W32.to_uint old.
+ rewrite /cp1 challenge_prefix_weight_set_inside 1:/#.
  rewrite hw0 hcpi W32.to_uint0 /old.
  ring.
rewrite /challenge_shuffle_update
        /VerifyChallengeM23SamplerStructurePostFreeze.challenge_shuffle_update.
rewrite challenge_prefix_weight_set_inside 1:/#.
rewrite hcp1b W32.to_uint1 hw1.
ring.
qed.

(* This is partial correctness: the sampler's rejection loop may request
   additional XOF blocks.  On every terminating tau-58 execution, the actual
   generated challenge is canonical and has exactly 58 one-words. *)
lemma verify_challenge_m23_tau58_canonical_weight :
  hoare [Verify.__verify_challenge_m23 :
    tau = W64.of_int mode2_tau ==>
    Mode2VerifyPrepareNorm.canonical_challenge res /\
    challenge_weight res = mode2_tau].
proof.
proc.
while
  (tau = W64.of_int mode2_tau /\
   Mode2VerifyPrepareNorm.canonical_challenge cp /\
   mode2_start <= W64.to_uint i <= challenge_words /\
   W64.to_uint pos <= 136 /\
   challenge_tail_zero cp (W64.to_uint i) /\
   challenge_prefix_weight cp (W64.to_uint i) =
     W64.to_uint i - mode2_start).
+ seq 1 :
    (tau = W64.of_int mode2_tau /\
     Mode2VerifyPrepareNorm.canonical_challenge cp /\
     mode2_start <= W64.to_uint i < challenge_words /\
     W64.to_uint pos < 136 /\
     challenge_tail_zero cp (W64.to_uint i) /\
     challenge_prefix_weight cp (W64.to_uint i) =
       W64.to_uint i - mode2_start).
  + if.
    + wp.
      call (_ : true ==> true); first by auto.
      auto => />.
      rewrite /protect_ptr.
      smt(W64.to_uint_cmp).
    + auto => />.
      move=> &hr hcanonical hlo hhi hpos htail hweight hloop hnot.
      move: hloop hnot.
      rewrite W64.ultE W64.uleE !W64.of_uintK
              /challenge_words /Mode2VerifyPrepareNorm.challenge_words /=.
      smt(W64.to_uint_cmp).
  + wp.
    auto => />.
    move=> &hr hcanonical hlo hhi hpos htail hweight.
    split.
    + move=> hacc.
      rewrite /protect_64 in hacc.
      rewrite /protect_64.
      have hbidx :
          0 <=
            W64.to_uint
              (zeroextu64
                (zeroextu32
                  (BArray136.get8 bp{hr} (W64.to_uint pos{hr})))) <=
            W64.to_uint i{hr}.
      * move: hacc.
        rewrite W64.ultE W64.to_uintD_small 1:/# W64.to_uint1.
        smt(W64.to_uint_cmp).
      split.
      * change
          (Mode2VerifyPrepareNorm.canonical_challenge
            (challenge_shuffle_update
              cp{hr} (W64.to_uint i{hr})
              (W64.to_uint
                (zeroextu64
                  (zeroextu32
                    (BArray136.get8 bp{hr} (W64.to_uint pos{hr}))))))).
        apply challenge_shuffle_update_canonical.
        - exact hcanonical.
        - smt(W64.to_uint_cmp).
        - exact hbidx.
      * split.
        - split.
          + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
            smt(W64.to_uint_cmp).
          + move=> _.
            rewrite W64.to_uintD_small 1:/# W64.to_uint1.
            smt(W64.to_uint_cmp).
        - split.
          + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
            smt(W64.to_uint_cmp).
          + split.
            * change
                (challenge_tail_zero
                  (challenge_shuffle_update
                    cp{hr} (W64.to_uint i{hr})
                    (W64.to_uint
                      (zeroextu64
                        (zeroextu32
                          (BArray136.get8
                            bp{hr} (W64.to_uint pos{hr}))))))
                  (W64.to_uint (i{hr} + W64.one))).
              rewrite W64.to_uintD_small 1:/# W64.to_uint1.
              apply challenge_shuffle_update_tail_zero.
              - smt(W64.to_uint_cmp).
              - exact htail.
            * change
                (challenge_prefix_weight
                  (challenge_shuffle_update
                    cp{hr} (W64.to_uint i{hr})
                    (W64.to_uint
                      (zeroextu64
                        (zeroextu32
                          (BArray136.get8
                            bp{hr} (W64.to_uint pos{hr}))))))
                  (W64.to_uint (i{hr} + W64.one)) =
                 W64.to_uint (i{hr} + W64.one) - mode2_start).
              rewrite W64.to_uintD_small 1:/# W64.to_uint1.
              rewrite challenge_shuffle_update_weight_step 1:/# 1:htail.
              rewrite hweight.
              ring.
    + move=> _.
      rewrite W64.to_uintD_small 1:/# W64.to_uint1.
      smt(W64.to_uint_cmp).
+ wp.
  exlim cp => cp0.
  call
    (VerifyChallengeM23SamplerStructurePostFreeze.poly_challenge_m23_init_zero_prefix
      cp0).
  wp.
  call (_ : true ==> true); first by auto.
  call (_ : true ==> true); first by auto.
  auto => />.
  rewrite /protect_ptr.
  move=> _ result hzero.
  split.
  + split.
    * apply
        VerifyChallengeM23SamplerStructurePostFreeze.zero_challenge_prefix_canonical.
      exact hzero.
    * split.
      - apply zero_prefix_tail_zero.
        + rewrite W64.of_uintK /mode2_tau /mode2_start /challenge_words
                  /VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau
                  /VerifyChallengeM23SamplerStructurePostFreeze.challenge_words
                  /Mode2VerifyPrepareNorm.challenge_words /=.
          smt().
        + exact hzero.
      - have hw :
            challenge_prefix_weight result
              (W64.to_uint (W64.of_int (256 - mode2_tau))) = 0.
        + apply zero_prefix_weight.
          - rewrite W64.of_uintK /mode2_tau /challenge_words
                    /VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau
                    /VerifyChallengeM23SamplerStructurePostFreeze.challenge_words
                    /Mode2VerifyPrepareNorm.challenge_words /=.
            smt().
          - move=> j hj.
            apply hzero.
            move: hj.
            rewrite W64.of_uintK /mode2_tau
                    /VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau
                    /VerifyChallengeM23SamplerStructurePostFreeze.challenge_words
                    /Mode2VerifyPrepareNorm.challenge_words /=.
            smt().
        rewrite hw W64.of_uintK /mode2_tau /mode2_start /challenge_words
                /VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau
                /VerifyChallengeM23SamplerStructurePostFreeze.challenge_words
                /Mode2VerifyPrepareNorm.challenge_words /=.
        trivial.
  + move=> cp1 i0 pos0 hexit hcanonical hlo hhi hpos htail hweight.
    have hieq : W64.to_uint i0 = challenge_words.
    * move: hexit hhi.
      rewrite W64.ultE W64.of_uintK /challenge_words
              /VerifyChallengeM23SamplerStructurePostFreeze.challenge_words
              /Mode2VerifyPrepareNorm.challenge_words /=.
      smt(W64.to_uint_cmp).
    rewrite /challenge_weight -hieq hweight.
    move: hieq.
    rewrite /mode2_start /mode2_tau /challenge_words
            /VerifyChallengeM23SamplerStructurePostFreeze.mode2_tau
            /VerifyChallengeM23SamplerStructurePostFreeze.challenge_words
            /Mode2VerifyPrepareNorm.challenge_words /=.
    smt().

qed.

end VerifyChallengeM23WeightPostFreeze.
