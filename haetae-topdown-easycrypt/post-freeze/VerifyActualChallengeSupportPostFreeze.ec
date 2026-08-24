require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 Mode2VerifyPrepareNorm RawVerifyApiTarget
               RawApiVerifyMuTrace
               VerifyChallengeM23WeightPostFreeze
               VerifyActualAcceptChallengeWeightPostFreeze
               VerifyActualChallengeAlgebraBridgePostFreeze
               HAETAE_Params HAETAE_Algebra.

import VerifyActualAcceptChallengeWeightPostFreeze.

theory VerifyActualChallengeSupportPostFreeze.

(* Partial correctness only: these results expose an algebraic support-size
   fact for accepting traces. They do not prove termination,
   HAETAE_Algebra.challenge_sparse, SHAKE properties, or any paper-level
   equality between the observed machine challenges and challenge_from_seed /
   challenge_hash{,_full,_packed}. *)

module Raw = RawVerifyApiTarget.M.
module FullMode2MuTrace = RawApiVerifyMuTrace.VerifyFullMode2MuTrace.
module InternalMode2MuTrace = RawApiVerifyMuTrace.VerifyInternalMode2MuTrace.
module RawApiMuTrace = RawApiVerifyMuTrace.VerifyRawApiMuTrace.
module CryptolabMuTrace = RawApiVerifyMuTrace.VerifyCryptolabMuTrace.

op challenge_of_barray =
  VerifyActualChallengeAlgebraBridgePostFreeze.challenge_of_barray.
op mode2_tau : int = HAETAE_Params.mode_tau HAETAE_Params.Mode2.
op challenge_words : int = Mode2VerifyPrepareNorm.challenge_words.
op challenge_weight = VerifyChallengeM23WeightPostFreeze.challenge_weight.

op challenge_support_size (ch : HAETAE_Algebra.challenge) : int =
  count (fun x => x <> 0) ch.

lemma challenge_support_size_perm_eq
    (lhs rhs : HAETAE_Algebra.challenge) :
  perm_eq lhs rhs =>
  challenge_support_size lhs = challenge_support_size rhs.
proof.
move=> hperm.
rewrite /challenge_support_size.
move/perm_eqP: hperm => hcount.
exact (hcount (fun x => x <> 0)).
qed.

op mode2_cardinality_wf (ch : HAETAE_Algebra.challenge) : bool =
  HAETAE_Algebra.challenge_wf ch /\
  challenge_support_size ch = mode2_tau.

op accepted_observed_mode2_cardinality_challenges
    (reject : W64.t) (parsed_cp cprime : BArray1024.t) : bool =
  reject = W64.zero =>
  mode2_cardinality_wf (challenge_of_barray parsed_cp) /\
  mode2_cardinality_wf (challenge_of_barray cprime) /\
  challenge_of_barray parsed_cp = challenge_of_barray cprime.

lemma foldl_int_add_sumz (xs : int list) (z : int) :
  foldl Int.(+) z xs = z + sumz xs.
proof.
elim: xs z => [|x xs ih] z.
+ by rewrite /sumz.
+ rewrite /sumz /= ih.
  ring.
qed.

lemma foldl_map_int_add_sumz
    (f : 'a -> int) (xs : 'a list) :
  foldl (fun z x => z + f x) 0 xs = sumz (map f xs).
proof.
rewrite -(foldl_map Int.(+) f 0 xs).
rewrite foldl_int_add_sumz.
ring.
qed.

lemma count_nonzero_eq_sumz_01 (xs : int list) :
  all (fun x => 0 <= x <= 1) xs =>
  count (fun x => x <> 0) xs = sumz xs.
proof.
elim: xs => [|x xs ih].
+ trivial.
+ rewrite /sumz /=.
  move=> [hx hxs].
  rewrite ih 1:hxs.
  case (x = 0) => hx0; smt().
qed.

lemma canonical_challenge_of_barray_all_01 cp :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  all (fun x => 0 <= x <= 1) (challenge_of_barray cp).
proof.
move=> hcanon.
rewrite /challenge_of_barray
        /VerifyActualChallengeAlgebraBridgePostFreeze.challenge_of_barray.
apply/List.allP => x /mkseqP [i [hi ->]].
move: (hcanon i hi) => [hrange _].
exact hrange.
qed.

lemma challenge_weight_eq_sumz_of_barray cp :
  challenge_weight cp = sumz (challenge_of_barray cp).
proof.
rewrite /challenge_weight
        /VerifyChallengeM23WeightPostFreeze.challenge_weight
        /VerifyChallengeM23WeightPostFreeze.challenge_prefix_weight
        /challenge_of_barray
        /VerifyActualChallengeAlgebraBridgePostFreeze.challenge_of_barray
        /mkseq.
exact
  (foldl_map_int_add_sumz
    (fun i => W32.to_uint (BArray1024.get32 cp i))
    (iota_ 0 challenge_words)).
qed.

lemma canonical_challenge_support_size_eq_weight cp :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  challenge_support_size (challenge_of_barray cp) = challenge_weight cp.
proof.
move=> hcanon.
rewrite /challenge_support_size.
rewrite count_nonzero_eq_sumz_01.
+ exact (canonical_challenge_of_barray_all_01 cp hcanon).
+ by rewrite -challenge_weight_eq_sumz_of_barray.
qed.

lemma canonical_machine_weight_implies_mode2_cardinality_wf
    (cp : BArray1024.t) :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  challenge_weight cp = mode2_tau =>
  mode2_cardinality_wf (challenge_of_barray cp).
proof.
move=> hcanon hweight.
rewrite /mode2_cardinality_wf.
split.
+ exact (VerifyActualChallengeAlgebraBridgePostFreeze.canonical_challenge_implies_challenge_wf cp hcanon).
+ rewrite canonical_challenge_support_size_eq_weight 1:hcanon.
  exact hweight.
qed.

lemma accepted_observed_canonical_weight_implies_mode2_cardinality
    (reject : W64.t) (parsed_cp cprime : BArray1024.t) :
  accepted_observed_canonical_weight_challenges reject parsed_cp cprime =>
  accepted_observed_mode2_cardinality_challenges reject parsed_cp cprime.
proof.
move=> haccept hzero.
move: (haccept hzero) => [hcp [hcprime [heq [hwcp hwcprime]]]].
split.
+ exact
     (canonical_machine_weight_implies_mode2_cardinality_wf
       parsed_cp hcp hwcp).
+ split.
   + exact
       (canonical_machine_weight_implies_mode2_cardinality_wf
         cprime hcprime hwcprime).
   + exact
       (VerifyActualChallengeAlgebraBridgePostFreeze.challenge_of_barray_eq
         parsed_cp cprime heq).
qed.

lemma verify_full_mode2_mu_trace_accept_mode2_cardinality_challenges :
  hoare [FullMode2MuTrace.run :
    true
    ==>
    accepted_observed_mode2_cardinality_challenges
      res FullMode2MuTrace.observed_cp FullMode2MuTrace.observed_cprime].
proof.
conseq verify_full_mode2_mu_trace_accept_canonical_weight_challenges => //=.
move=> result observed_cp observed_cprime haccept.
exact
  (accepted_observed_canonical_weight_implies_mode2_cardinality
    result observed_cp observed_cprime haccept).
qed.

lemma verify_internal_mode2_mu_trace_accept_mode2_cardinality_challenges :
  hoare [InternalMode2MuTrace.run :
    true
    ==>
    accepted_observed_mode2_cardinality_challenges
      res InternalMode2MuTrace.observed_cp
      InternalMode2MuTrace.observed_cprime].
proof.
conseq verify_internal_mode2_mu_trace_accept_canonical_weight_challenges => //=.
move=> result observed_cp observed_cprime haccept.
exact
  (accepted_observed_canonical_weight_implies_mode2_cardinality
    result observed_cp observed_cprime haccept).
qed.

lemma verify_raw_api_mu_trace_accept_mode2_cardinality_challenges :
  hoare [RawApiMuTrace.run :
    true
    ==>
    accepted_observed_mode2_cardinality_challenges
      res RawApiMuTrace.observed_cp RawApiMuTrace.observed_cprime].
proof.
conseq verify_raw_api_mu_trace_accept_canonical_weight_challenges => //=.
move=> result observed_cp observed_cprime haccept.
exact
  (accepted_observed_canonical_weight_implies_mode2_cardinality
    result observed_cp observed_cprime haccept).
qed.

lemma verify_cryptolab_mu_trace_accept_mode2_cardinality_challenges :
  hoare [CryptolabMuTrace.run :
    true
    ==>
    accepted_observed_mode2_cardinality_challenges
      res CryptolabMuTrace.observed_cp CryptolabMuTrace.observed_cprime].
proof.
conseq verify_cryptolab_mu_trace_accept_canonical_weight_challenges => //=.
move=> result observed_cp observed_cprime haccept.
exact
  (accepted_observed_canonical_weight_implies_mode2_cardinality
    result observed_cp observed_cprime haccept).
qed.

lemma actual_verify_full_mode2_accept_observed_mode2_cardinality_challenges :
  equiv [Raw._verify_full_mode2 ~ FullMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_cardinality_challenges
      res{1} FullMode2MuTrace.observed_cp{2}
      FullMode2MuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_full_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_full_mode2_mu_trace_accept_mode2_cardinality_challenges => //=.
qed.

lemma actual_verify_internal_mode2_accept_observed_mode2_cardinality_challenges :
  equiv [Raw.sign_verify_internal_mode2_jazz ~ InternalMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_cardinality_challenges
      res{1} InternalMode2MuTrace.observed_cp{2}
      InternalMode2MuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_internal_mode2_exact_mu_trace
  (_ : true ==> true)
  verify_internal_mode2_mu_trace_accept_mode2_cardinality_challenges => //=.
qed.

lemma actual_verify_raw_api_accept_observed_mode2_cardinality_challenges :
  equiv [Raw._api_verify_mode2_raw ~ RawApiMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_cardinality_challenges
      res{1} RawApiMuTrace.observed_cp{2}
      RawApiMuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_raw_api_exact_mu_trace
  (_ : true ==> true)
  verify_raw_api_mu_trace_accept_mode2_cardinality_challenges => //=.
qed.

lemma actual_verify_cryptolab_accept_observed_mode2_cardinality_challenges :
  equiv [Raw.cryptolab_haetae_mode2_verify_internal ~ CryptolabMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_mode2_cardinality_challenges
      res{1} CryptolabMuTrace.observed_cp{2}
      CryptolabMuTrace.observed_cprime{2}].
proof.
conseq RawApiVerifyMuTrace.verify_cryptolab_exact_mu_trace
  (_ : true ==> true)
  verify_cryptolab_mu_trace_accept_mode2_cardinality_challenges => //=.
qed.

end VerifyActualChallengeSupportPostFreeze.
