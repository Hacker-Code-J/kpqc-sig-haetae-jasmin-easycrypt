require import AllCore List.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8 BArray32 BArray40 BArray1024 BArray1152
               BArray2752 BArray2948 BArray8192 BArray32768
               Mode2VerifyPrepareNorm Mode2VerifyTailChallenge
               RawVerifyApiTarget
               RawApiVerifyMuTrace
               VerifyActualFullFunctionalRawPostFreeze
               VerifyActualFullAcceptApiRawPostFreeze
               HAETAE_Params HAETAE_Algebra.

theory VerifyActualChallengeAlgebraBridgePostFreeze.

module Flat =
  VerifyActualFullFunctionalRawPostFreeze.VerifyFullMode2FlatTrace.
module Tail = RawApiVerifyMuTrace.VerifyTailMuTrace.
module Raw = RawVerifyApiTarget.M.
module ApiFlat =
  VerifyActualFullAcceptApiRawPostFreeze.VerifyCryptolabFlatTrace.

op challenge_of_barray
    (cp : BArray1024.t) : HAETAE_Algebra.challenge =
  mkseq
    (fun i => W32.to_uint (BArray1024.get32 cp i))
    Mode2VerifyPrepareNorm.challenge_words.

op bytes_of_barray32 (bp : BArray32.t) : HAETAE_Algebra.byte list =
  mkseq (fun i => W8.to_uint (BArray32.get8 bp i)) 32.

op mode2_highbits_bytes
    (bp : BArray1152.t) : HAETAE_Algebra.byte list =
  mkseq
    (fun i => W8.to_uint (BArray1152.get8 bp i))
    Mode2VerifyTailChallenge.mode2_tail_highlen.

lemma bytes_of_barray32_size (bp : BArray32.t) :
  size (bytes_of_barray32 bp) = 32.
proof. by rewrite /bytes_of_barray32 size_mkseq. qed.

lemma bytes_of_barray32_coeff (bp : BArray32.t) (i : int) :
  0 <= i < 32 =>
  nth 0 (bytes_of_barray32 bp) i = W8.to_uint (BArray32.get8 bp i).
proof. by move=> hi; rewrite /bytes_of_barray32 nth_mkseq 1:hi. qed.

lemma mode2_highbits_bytes_size (bp : BArray1152.t) :
  size (mode2_highbits_bytes bp) =
    Mode2VerifyTailChallenge.mode2_tail_highlen.
proof. by rewrite /mode2_highbits_bytes size_mkseq. qed.

lemma mode2_highbits_bytes_coeff (bp : BArray1152.t) (i : int) :
  0 <= i < Mode2VerifyTailChallenge.mode2_tail_highlen =>
  nth 0 (mode2_highbits_bytes bp) i =
    W8.to_uint (BArray1152.get8 bp i).
proof. by move=> hi; rewrite /mode2_highbits_bytes nth_mkseq 1:hi. qed.

lemma challenge_of_barray_size (cp : BArray1024.t) :
  size (challenge_of_barray cp) = HAETAE_Params.n.
proof.
by rewrite /challenge_of_barray size_mkseq
           /Mode2VerifyPrepareNorm.challenge_words /HAETAE_Params.n.
qed.

lemma challenge_of_barray_coeff
    (cp : BArray1024.t) (i : int) :
  0 <= i < Mode2VerifyPrepareNorm.challenge_words =>
  nth 0 (challenge_of_barray cp) i =
    W32.to_uint (BArray1024.get32 cp i).
proof.
move=> hi.
rewrite /challenge_of_barray nth_mkseq 1:hi.
trivial.
qed.

lemma canonical_challenge_implies_challenge_wf
    (cp : BArray1024.t) :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  HAETAE_Algebra.challenge_wf (challenge_of_barray cp).
proof.
move=> hcanonical.
rewrite /HAETAE_Algebra.challenge_wf.
split.
+ rewrite /HAETAE_Algebra.poly_wf challenge_of_barray_size.
  trivial.
+ apply/List.allP => x hx.
  move: hx => /mkseqP [i [hi ->]].
  move: (hcanonical i hi) => [[hlo hhi] _].
  rewrite /HAETAE_Algebra.challenge_coeff_ok.
  smt().
qed.

lemma challenge_of_barray_word_eq
    (lhs rhs : BArray1024.t) :
  (forall i,
    0 <= i < Mode2VerifyPrepareNorm.challenge_words =>
    BArray1024.get32 lhs i = BArray1024.get32 rhs i) =>
  challenge_of_barray lhs = challenge_of_barray rhs.
proof.
move=> hwords.
apply/(eq_from_nth 0).
+ by rewrite !challenge_of_barray_size.
move=> i hi.
rewrite challenge_of_barray_size in hi.
rewrite /challenge_of_barray !nth_mkseq 1:/# 1:/#.
simplify.
have hi' : 0 <= i < Mode2VerifyPrepareNorm.challenge_words.
+ by move: hi; rewrite /Mode2VerifyPrepareNorm.challenge_words
                      /HAETAE_Params.n.
by rewrite (hwords i hi').
qed.

lemma challenge_of_barray_eq
    (lhs rhs : BArray1024.t) :
  lhs = rhs =>
  challenge_of_barray lhs = challenge_of_barray rhs.
proof. by move=> ->. qed.

lemma accepted_concrete_result_paper_challenges
    (vkp0 : BArray2752.t)
    (outmat : BArray32768.t)
    (parsed_cp : BArray1024.t)
    (parsed_low parsed_high parsed_h : BArray8192.t)
    (parsed_bad : BArray8.t)
    (out high : BArray8192.t)
    (outw : BArray1024.t) (total : W64.t)
    (w z2 : BArray8192.t) (norm_reject reject : W64.t)
    (observed_cp observed_cprime : BArray1024.t) :
  VerifyActualFullAcceptApiRawPostFreeze.accepted_full_trace_concrete_result
    vkp0 outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out high outw total w z2 norm_reject reject observed_cp observed_cprime =>
  HAETAE_Algebra.challenge_wf (challenge_of_barray observed_cp) /\
  HAETAE_Algebra.challenge_wf (challenge_of_barray observed_cprime) /\
  challenge_of_barray observed_cp = challenge_of_barray observed_cprime /\
  challenge_of_barray parsed_cp = challenge_of_barray observed_cprime.
proof.
rewrite
  /VerifyActualFullAcceptApiRawPostFreeze.accepted_full_trace_concrete_result.
move=> [_ [hparsed [hcp [hcprime [hequal _]]]]].
split.
+ exact (canonical_challenge_implies_challenge_wf observed_cp hcp).
split.
+ exact (canonical_challenge_implies_challenge_wf observed_cprime hcprime).
split.
+ exact (challenge_of_barray_eq observed_cp observed_cprime hequal).
rewrite -hparsed.
exact (challenge_of_barray_eq observed_cp observed_cprime hequal).
qed.

lemma verify_full_mode2_flat_trace_accept_paper_challenges
    (sig0 : BArray2948.t)
    (vkp0 : BArray2752.t) (vku0 : int)
    (desc0 : BArray40.t) :
  hoare [Flat.run :
    sigp = sig0 /\ siglen = W64.of_int 1474 /\
    vkp = vkp0 /\ vku = vku0 /\ descp = desc0
    ==>
    res.`14 = W64.zero =>
    HAETAE_Algebra.challenge_wf
      (challenge_of_barray Tail.observed_cp) /\
    HAETAE_Algebra.challenge_wf
      (challenge_of_barray Tail.observed_cprime) /\
    challenge_of_barray Tail.observed_cp =
      challenge_of_barray Tail.observed_cprime /\
    challenge_of_barray res.`2 =
      challenge_of_barray Tail.observed_cprime].
proof.
conseq
  (VerifyActualFullAcceptApiRawPostFreeze.verify_full_mode2_flat_trace_accept_concrete
    sig0 vkp0 vku0 desc0).
+ auto.
move=> &m _ result observed_cp observed_cprime hresult hzero.
exact
  (accepted_concrete_result_paper_challenges
    vkp0 result.`1 result.`2 result.`3 result.`4 result.`5 result.`6
    result.`7 result.`8 result.`9 result.`10 result.`11 result.`12
    result.`13 result.`14 observed_cp observed_cprime
    (hresult hzero)).
qed.

lemma verify_cryptolab_flat_trace_accept_paper_challenges :
  hoare [ApiFlat.run :
    true
    ==>
    res = W64.zero =>
    HAETAE_Algebra.challenge_wf
      (challenge_of_barray ApiFlat.observed_cp) /\
    HAETAE_Algebra.challenge_wf
      (challenge_of_barray ApiFlat.observed_cprime) /\
    challenge_of_barray ApiFlat.observed_cp =
      challenge_of_barray ApiFlat.observed_cprime /\
    challenge_of_barray ApiFlat.out_cp =
      challenge_of_barray ApiFlat.observed_cprime].
proof.
conseq
  (VerifyActualFullAcceptApiRawPostFreeze.verify_cryptolab_flat_trace_accept_exact).
+ auto.
move=> &m _ result observed_cp observed_cprime observed_vk out_bad out_cp
  out_h out_high out_highbits out_low out_mat out_norm_reject out_reject
  out_total out_w out_wprime out_z1 out_z2 hresult hzero.
exact
  (accepted_concrete_result_paper_challenges
    observed_vk out_mat out_cp out_low out_high out_h out_bad
    out_z1 out_highbits out_wprime out_total out_w out_z2
    out_norm_reject out_reject observed_cp observed_cprime
    (hresult hzero)).
qed.

lemma actual_verify_cryptolab_accept_paper_challenges :
  equiv [Raw.cryptolab_haetae_mode2_verify_internal ~ ApiFlat.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero =>
      HAETAE_Algebra.challenge_wf
        (challenge_of_barray ApiFlat.observed_cp{2}) /\
      HAETAE_Algebra.challenge_wf
        (challenge_of_barray ApiFlat.observed_cprime{2}) /\
      challenge_of_barray ApiFlat.observed_cp{2} =
        challenge_of_barray ApiFlat.observed_cprime{2} /\
      challenge_of_barray ApiFlat.out_cp{2} =
        challenge_of_barray ApiFlat.observed_cprime{2})].
proof.
conseq VerifyActualFullAcceptApiRawPostFreeze.verify_cryptolab_exact_flat_trace
  (_ : true ==> true)
  verify_cryptolab_flat_trace_accept_paper_challenges => //=.
qed.

op mode2_challenge_full_source_relation
    (actual : BArray1024.t)
    (highbits : HAETAE_Algebra.polyveck)
    (lowbits : HAETAE_Algebra.poly) (mu : HAETAE_Algebra.crh) : bool =
  challenge_of_barray actual =
    HAETAE_Algebra.challenge_hash_full
      HAETAE_Params.Mode2 highbits lowbits mu.

lemma mode2_challenge_full_source_target_wf
    (actual : BArray1024.t)
    (highbits : HAETAE_Algebra.polyveck)
    (lowbits : HAETAE_Algebra.poly) (mu : HAETAE_Algebra.crh) :
  mode2_challenge_full_source_relation actual highbits lowbits mu =>
  HAETAE_Algebra.challenge_wf (challenge_of_barray actual).
proof.
rewrite /mode2_challenge_full_source_relation => ->.
exact
  (HAETAE_Algebra.challenge_hash_full_wf
    HAETAE_Params.Mode2 highbits lowbits mu).
qed.

lemma accepted_challenge_eq_full_source
    (parsed observed_cprime : BArray1024.t)
    (highbits : HAETAE_Algebra.polyveck)
    (lowbits : HAETAE_Algebra.poly) (mu : HAETAE_Algebra.crh) :
  challenge_of_barray parsed = challenge_of_barray observed_cprime =>
  mode2_challenge_full_source_relation
    observed_cprime highbits lowbits mu =>
  challenge_of_barray parsed =
    HAETAE_Algebra.challenge_hash_full
      HAETAE_Params.Mode2 highbits lowbits mu /\
  HAETAE_Algebra.challenge_wf
    (HAETAE_Algebra.challenge_hash_full
      HAETAE_Params.Mode2 highbits lowbits mu).
proof.
rewrite /mode2_challenge_full_source_relation.
move=> hparsed hactual.
split.
+ by rewrite hparsed hactual.
+ exact
    (HAETAE_Algebra.challenge_hash_full_wf
      HAETAE_Params.Mode2 highbits lowbits mu).
qed.

op mode2_challenge_packed_relation
    (actual : BArray1024.t)
    (highp : BArray1152.t) (lsbp mup : BArray32.t) : bool =
  challenge_of_barray actual =
    HAETAE_Algebra.challenge_hash_packed
      HAETAE_Params.Mode2
      (mode2_highbits_bytes highp)
      (bytes_of_barray32 lsbp)
      (bytes_of_barray32 mup).

(* Exact remaining implementation leaf: establish this relation for
   Tail.observed_cprime, Tail.observed_highp, Tail.observed_lsbp, and
   Tail.observed_mu after __verify_challenge_m23.  The current checked tail
   proofs expose those values but stop before the squeeze/sampler semantics. *)

lemma mode2_challenge_packed_target_wf
    (actual : BArray1024.t)
    (highp : BArray1152.t) (lsbp mup : BArray32.t) :
  mode2_challenge_packed_relation actual highp lsbp mup =>
  HAETAE_Algebra.challenge_wf (challenge_of_barray actual).
proof.
rewrite /mode2_challenge_packed_relation => ->.
exact
  (HAETAE_Algebra.challenge_hash_packed_wf
    HAETAE_Params.Mode2
    (mode2_highbits_bytes highp)
    (bytes_of_barray32 lsbp)
    (bytes_of_barray32 mup)).
qed.

lemma accepted_challenge_eq_packed_source
    (parsed observed_cprime : BArray1024.t)
    (highp : BArray1152.t) (lsbp mup : BArray32.t) :
  challenge_of_barray parsed = challenge_of_barray observed_cprime =>
  mode2_challenge_packed_relation observed_cprime highp lsbp mup =>
  challenge_of_barray parsed =
    HAETAE_Algebra.challenge_hash_packed
      HAETAE_Params.Mode2
      (mode2_highbits_bytes highp)
      (bytes_of_barray32 lsbp)
      (bytes_of_barray32 mup) /\
  HAETAE_Algebra.challenge_wf
    (HAETAE_Algebra.challenge_hash_packed
      HAETAE_Params.Mode2
      (mode2_highbits_bytes highp)
      (bytes_of_barray32 lsbp)
      (bytes_of_barray32 mup)).
proof.
rewrite /mode2_challenge_packed_relation.
move=> hparsed hactual.
split.
+ by rewrite hparsed hactual.
+ exact
    (HAETAE_Algebra.challenge_hash_packed_wf
      HAETAE_Params.Mode2
      (mode2_highbits_bytes highp)
      (bytes_of_barray32 lsbp)
      (bytes_of_barray32 mup)).
qed.

lemma paper_challenge_hash_ignores_highbits
    (md : HAETAE_Params.mode)
    (left_high right_high : HAETAE_Algebra.polyveck)
    (lowbits : HAETAE_Algebra.poly) (mu : HAETAE_Algebra.crh) :
  HAETAE_Algebra.challenge_hash md left_high lowbits mu =
  HAETAE_Algebra.challenge_hash md right_high lowbits mu.
proof. by rewrite /HAETAE_Algebra.challenge_hash. qed.

lemma paper_challenge_hash_uses_reduced_source
    (md : HAETAE_Params.mode)
    (highbits : HAETAE_Algebra.polyveck)
    (lowbits : HAETAE_Algebra.poly) (mu : HAETAE_Algebra.crh) :
  HAETAE_Algebra.challenge_hash md highbits lowbits mu =
  HAETAE_Algebra.challenge_from_seed md
    (HAETAE_Algebra.encode_poly lowbits ++ mu).
proof. by rewrite /HAETAE_Algebra.challenge_hash. qed.

lemma paper_challenge_hash_full_uses_full_source
    (md : HAETAE_Params.mode)
    (highbits : HAETAE_Algebra.polyveck)
    (lowbits : HAETAE_Algebra.poly) (mu : HAETAE_Algebra.crh) :
  HAETAE_Algebra.challenge_hash_full md highbits lowbits mu =
  HAETAE_Algebra.challenge_from_seed md
    (HAETAE_Algebra.challenge_source highbits lowbits mu).
proof. by rewrite /HAETAE_Algebra.challenge_hash_full. qed.

lemma paper_challenge_hash_packed_uses_actual_order
    (md : HAETAE_Params.mode)
    (highbits_bytes lowbits_bytes mu_bytes : HAETAE_Algebra.byte list) :
  HAETAE_Algebra.challenge_hash_packed
    md highbits_bytes lowbits_bytes mu_bytes =
  HAETAE_Algebra.challenge_from_seed md
    (highbits_bytes ++ lowbits_bytes ++ mu_bytes).
proof. by rewrite /HAETAE_Algebra.challenge_hash_packed. qed.

end VerifyActualChallengeAlgebraBridgePostFreeze.
