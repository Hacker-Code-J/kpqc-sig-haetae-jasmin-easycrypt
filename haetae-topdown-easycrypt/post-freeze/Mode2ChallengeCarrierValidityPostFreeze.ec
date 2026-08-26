require import AllCore FSet.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2VerifyPrepareNorm
               VerifyChallengeM23UniformSubsetPostFreeze
               VerifyChallengeM23UniformSamplerBridgePostFreeze
               VerifyChallengeM23WeightPostFreeze
               VerifyActualChallengeSupportPostFreeze
               Mode2ChallengeROMAdapterPostFreeze.

theory Mode2ChallengeCarrierValidityPostFreeze.

(* This is an algebraic carrier-validity layer only.  It lifts the already
   proved canonical/weight facts to the concrete Mode-2 carrier surface, but
   it does not add any termination, XOF, SHAKE, or distributional claim. *)

op support_prefix =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.support_prefix.
op challenge_of_barray =
  VerifyActualChallengeSupportPostFreeze.challenge_of_barray.
op challenge_support_size =
  VerifyActualChallengeSupportPostFreeze.challenge_support_size.
op challenge_prefix_weight =
  VerifyChallengeM23WeightPostFreeze.challenge_prefix_weight.
op challenge_weight =
  VerifyChallengeM23WeightPostFreeze.challenge_weight.
op challenge_words =
  VerifyChallengeM23WeightPostFreeze.challenge_words.
op mode2_challenge_words =
  Mode2ChallengeROMAdapterPostFreeze.mode2_challenge_words.
op mode2_tau =
  Mode2ChallengeROMAdapterPostFreeze.mode2_tau.
op valid_mode2_support =
  Mode2ChallengeROMAdapterPostFreeze.valid_mode2_support.
op valid_mode2_carrier_challenge =
  Mode2ChallengeROMAdapterPostFreeze.valid_mode2_carrier_challenge.

lemma support_prefix0 cp :
  support_prefix cp 0 = FSet.fset0.
proof.
apply/FSet.fsetP => i.
rewrite VerifyChallengeM23UniformSubsetPostFreeze.support_prefix_mem
        FSet.in_fset0.
smt().
qed.

lemma support_prefix_notin_current cp n :
  0 <= n =>
  n \notin support_prefix cp n.
proof.
move=> hn.
apply/negP.
rewrite VerifyChallengeM23UniformSubsetPostFreeze.support_prefix_mem.
smt().
qed.

lemma support_prefix_succ cp n :
  0 <= n =>
  support_prefix cp (n + 1) =
  if BArray1024.get32 cp n = W32.one
  then support_prefix cp n `|` FSet.fset1 n
  else support_prefix cp n.
proof.
move=> hn.
apply/FSet.fsetP => j.
rewrite VerifyChallengeM23UniformSubsetPostFreeze.support_prefix_mem.
case (BArray1024.get32 cp n = W32.one) => hone.
+ rewrite FSet.in_fsetU1
          VerifyChallengeM23UniformSubsetPostFreeze.support_prefix_mem.
  case: (j = n) => [-> | hjn]; smt().
+ rewrite VerifyChallengeM23UniformSubsetPostFreeze.support_prefix_mem.
  case: (j = n) => [-> | hjn]; smt().
qed.

lemma support_prefix_card_step cp n :
  0 <= n < challenge_words =>
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  FSet.card (support_prefix cp (n + 1)) =
  FSet.card (support_prefix cp n) +
  W32.to_uint (BArray1024.get32 cp n).
proof.
move=> [hn0 hn1] hcanon.
rewrite (support_prefix_succ cp n hn0).
have hnotin : n \notin support_prefix cp n.
+ exact (support_prefix_notin_current cp n hn0).
have hbound : 0 <= n < Mode2VerifyPrepareNorm.challenge_words.
+ rewrite /challenge_words.
   smt().
have hword := hcanon n hbound.
move: hword => [[hlo hhi] _].
case (BArray1024.get32 cp n = W32.one) => hone.
+ rewrite FSet.fcardU1 hnotin hone W32.to_uint1.
   ring.
+ have hzero : W32.to_uint (BArray1024.get32 cp n) = 0 by
     smt(W32.to_uint_eq W32.to_uint1).
   rewrite hzero.
   ring.
qed.

lemma canonical_support_prefix_weight cp n :
  0 <= n <= challenge_words =>
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  FSet.card (support_prefix cp n) = challenge_prefix_weight cp n.
proof.
elim/natind: n => [n hn|n hn ih].
+ move=> [hn0 _] _.
   have -> : n = 0 by smt().
   have hleft : FSet.card (support_prefix cp 0) = 0.
   + apply/FSet.fcard_eq0.
     exact (support_prefix0 cp).
   have hright :=
     VerifyChallengeM23WeightPostFreeze.challenge_prefix_weight0 cp.
   smt().
+ move=> hbound hcanon.
   rewrite support_prefix_card_step 1:/# 1:hcanon.
   rewrite ih 1:/# 1:hcanon.
   have hstep :=
     VerifyChallengeM23WeightPostFreeze.challenge_prefix_weight_step
       cp n hn.
   smt().
qed.

lemma support_prefix_full_subset cp :
  support_prefix cp mode2_challenge_words \subset
  FSet.rangeset 0 mode2_challenge_words.
proof.
move=> i hi.
move/VerifyChallengeM23UniformSubsetPostFreeze.support_prefix_mem: hi
  => [hir _].
rewrite FSet.mem_rangeset.
exact hir.
qed.

lemma canonical_support_prefix_cardinality cp :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  FSet.card (support_prefix cp mode2_challenge_words) =
  challenge_support_size (challenge_of_barray cp).
proof.
move=> hcanon.
have hprefix :=
  canonical_support_prefix_weight cp mode2_challenge_words _ hcanon.
+ rewrite /mode2_challenge_words /challenge_words.
   smt().
have hsize :=
  VerifyActualChallengeSupportPostFreeze.canonical_challenge_support_size_eq_weight
    cp hcanon.
rewrite /challenge_weight in hsize.
rewrite /VerifyChallengeM23WeightPostFreeze.challenge_weight in hsize.
rewrite hprefix.
rewrite /mode2_challenge_words /challenge_words in hsize.
apply eq_sym.
exact hsize.
qed.

lemma canonical_weight_implies_valid_mode2_support_prefix cp :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  challenge_weight cp = mode2_tau =>
  valid_mode2_support (support_prefix cp mode2_challenge_words).
proof.
move=> hcanon hweight.
rewrite /valid_mode2_support
        /Mode2ChallengeROMAdapterPostFreeze.valid_mode2_support
        /VerifyChallengeM23UniformSamplerBridgePostFreeze.valid_subset.
split.
+ exact (support_prefix_full_subset cp).
+ rewrite canonical_support_prefix_cardinality 1:hcanon.
   have hsize :=
     VerifyActualChallengeSupportPostFreeze.canonical_challenge_support_size_eq_weight
       cp hcanon.
   smt().
qed.

lemma canonical_weight_implies_valid_mode2_carrier cp :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  challenge_weight cp = mode2_tau =>
  valid_mode2_carrier_challenge (challenge_of_barray cp).
proof.
move=> hcanon hweight.
exists (support_prefix cp mode2_challenge_words).
split.
+ exact
     (canonical_weight_implies_valid_mode2_support_prefix cp hcanon hweight).
+ exact
     (Mode2ChallengeROMAdapterPostFreeze.canonical_challenge_of_barrayE
        cp hcanon).
qed.

end Mode2ChallengeCarrierValidityPostFreeze.
