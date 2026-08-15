require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 Mode2VerifyTailChallenge RawApiVerifyMuTrace
               RawVerifyApiTarget
               VerifyActualAcceptMismatchRawPostFreeze.

theory VerifyActualAcceptChallengeEqualityRawPostFreeze.

module Raw = RawVerifyApiTarget.M.
module FullM23MuTrace = RawApiVerifyMuTrace.VerifyFullM23MuTrace.
module FullMode2MuTrace = RawApiVerifyMuTrace.VerifyFullMode2MuTrace.
module InternalMode2MuTrace = RawApiVerifyMuTrace.VerifyInternalMode2MuTrace.
module RawApiMuTrace = RawApiVerifyMuTrace.VerifyRawApiMuTrace.
module CryptolabMuTrace = RawApiVerifyMuTrace.VerifyCryptolabMuTrace.

lemma w64_modulus_value :
  W64.modulus = 18446744073709551616.
proof. trivial. qed.

lemma pow2_63_value :
  2 ^ 63 = 9223372036854775808.
proof. trivial. qed.

lemma w64_or_eq_zero (x y : W64.t) :
  x `|` y = W64.zero <=> x = W64.zero /\ y = W64.zero.
proof.
split.
+ move=> hxy.
  have hxle := W64.ule_orw x y.
  have hyle : y \ule x `|` y.
  + by rewrite W64.orwC; apply W64.ule_orw.
  rewrite W64.uleE hxy W64.to_uint0 in hxle.
  rewrite W64.uleE hxy W64.to_uint0 in hyle.
  split; rewrite W64.to_uint_eq W64.to_uint0;
    have [hx0 _] := W64.to_uint_cmp x;
    have [hy0 _] := W64.to_uint_cmp y;
    smt().
+ move=> [-> ->].
  by rewrite W64.orw0.
qed.

lemma w64_to_uint_zero_sub_nonzero (x : W64.t) :
  x <> W64.zero =>
  W64.to_uint (W64.zero - x) = W64.modulus - W64.to_uint x.
proof.
move=> hx_nz.
have [hu_ge hu_ltmod] := W64.to_uint_cmp x.
have hu_pos : 0 < W64.to_uint x by
  smt(W64.to_uint_eq W64.to_uint0).
rewrite W64.WRingA.sub0r W64.to_uintNE.
apply pmod_small.
split.
+ rewrite subz_ge0.
  exact (ltzW (W64.to_uint x) W64.modulus hu_ltmod).
+ rewrite -(ltz_add2r (-W64.modulus)
    (W64.modulus - W64.to_uint x) W64.modulus).
  have -> :
      W64.modulus - W64.to_uint x + -W64.modulus =
      - W64.to_uint x by ring.
  have -> : W64.modulus + -W64.modulus = 0 by ring.
  rewrite oppz_lt0.
  move=> _.
  exact hu_pos.
qed.

lemma poly_mismatch_result_word_zero_implies_acc_zero (acc : W64.t) :
  Mode2VerifyTailChallenge.poly_mismatch_result_word acc = W64.zero =>
  acc = W64.zero.
proof.
rewrite /Mode2VerifyTailChallenge.poly_mismatch_result_word.
move=> hresult.
have hquot :
    W64.to_uint (acc `|` (W64.zero - acc)) %/ 2 ^ 63 = 0.
+ move: hresult.
  rewrite W64.to_uint_eq W64.shr_div_le 1:/# W64.to_uint0 /=.
  trivial.
have horange :
    0 <= W64.to_uint (acc `|` (W64.zero - acc)) < 2 ^ 63.
+ have hpow : 0 < 2 ^ 63 by smt(gt0_pow2).
  rewrite divz_eq0 1:hpow.
  exact hquot.
have hacc_le :
    W64.to_uint acc <=
    W64.to_uint (acc `|` (W64.zero - acc)).
+ have h := W64.ule_orw acc (W64.zero - acc).
  by rewrite W64.uleE in h.
have [hor_ge hor_lt] := horange.
case (acc = W64.zero) => hacc0.
+ trivial.
  + have hu_pos : 0 < W64.to_uint acc.
  + have hu_cmp := W64.to_uint_cmp acc.
    have hu_nz : W64.to_uint acc <> 0 by
      smt(W64.to_uint_eq W64.to_uint0).
    smt().
  have hu_lt : W64.to_uint acc < 2 ^ 63.
  + smt().
  have hneg_le :
      W64.to_uint (W64.zero - acc) <=
      W64.to_uint (acc `|` (W64.zero - acc)).
  + have h := W64.ule_orw (W64.zero - acc) acc.
    rewrite W64.orwC W64.uleE in h.
    exact h.
  rewrite (w64_to_uint_zero_sub_nonzero acc hacc0) in hneg_le.
  have hneg_ge :
      2 ^ 63 <= W64.modulus - W64.to_uint acc.
  + move: hu_lt.
    rewrite w64_modulus_value pow2_63_value.
    smt().
  have hor_ge_half :
      2 ^ 63 <= W64.to_uint (acc `|` (W64.zero - acc)).
  + exact (lez_trans
      (W64.modulus - W64.to_uint acc) (2 ^ 63)
      (W64.to_uint (acc `|` (W64.zero - acc))) hneg_ge hneg_le).
  have hbad := lez_lt_asym
    (2 ^ 63) (W64.to_uint (acc `|` (W64.zero - acc))).
  smt().
qed.

lemma poly_mismatch_result_word_eq_zero (acc : W64.t) :
  Mode2VerifyTailChallenge.poly_mismatch_result_word acc = W64.zero <=>
  acc = W64.zero.
proof.
split.
+ exact (poly_mismatch_result_word_zero_implies_acc_zero acc).
+ move=> ->.
  rewrite /Mode2VerifyTailChallenge.poly_mismatch_result_word.
  apply W64.to_uint_eq.
  rewrite W64.shr_div_le 1:/# W64.to_uint0 /=.
  trivial.
qed.

lemma poly_mismatch_acc_prefix_succ_zero
    (ap bp : BArray1024.t) (n : int) :
  0 <= n =>
  Mode2VerifyTailChallenge.poly_mismatch_acc_prefix ap bp (n + 1) =
    W64.zero =>
  Mode2VerifyTailChallenge.poly_mismatch_acc_prefix ap bp n = W64.zero /\
  Mode2VerifyTailChallenge.poly_mismatch_term ap bp n = W64.zero.
proof.
move=> hn.
rewrite Mode2VerifyTailChallenge.poly_mismatch_acc_prefix_step 1:hn.
rewrite w64_or_eq_zero.
trivial.
qed.

lemma poly_mismatch_acc_prefix_zero_terms
    (ap bp : BArray1024.t) (n : int) :
  0 <= n =>
  Mode2VerifyTailChallenge.poly_mismatch_acc_prefix ap bp n = W64.zero =>
  forall i, 0 <= i < n =>
    Mode2VerifyTailChallenge.poly_mismatch_term ap bp i = W64.zero.
proof.
move=> hn.
elim/intind: n hn => [|n hn ih].
+ move=> _ i hi.
  smt().
+ move=> hacc i hi.
  move: hacc.
  rewrite Mode2VerifyTailChallenge.poly_mismatch_acc_prefix_step 1:hn.
  rewrite w64_or_eq_zero.
  move=> [hprefix hterm].
  case (i < n) => hin.
  + apply (ih hprefix i).
    smt().
  have -> : i = n by smt().
  exact hterm.
qed.

lemma w32_xor_eq_zero (x y : W32.t) :
  x `^` y = W32.zero <=> x = y.
proof.
split.
+ move=> hxor.
  apply W32.wordP => i hi.
  move: hxor.
  rewrite W32.wordP => hbits.
  have hbit := hbits i hi.
  rewrite W32.xorwE W32.zerowE in hbit.
  move: hbit.
  by case (x.[i]); case (y.[i]).
+ move=> ->.
  exact (W32.xorwK y).
qed.

lemma poly_mismatch_term_eq_zero
    (ap bp : BArray1024.t) (i : int) :
  Mode2VerifyTailChallenge.poly_mismatch_term ap bp i = W64.zero <=>
  BArray1024.get32 ap i = BArray1024.get32 bp i.
proof.
rewrite /Mode2VerifyTailChallenge.poly_mismatch_term.
split.
+ move=> hterm.
  apply/w32_xor_eq_zero.
  rewrite W32.to_uint_eq W32.to_uint0.
  move: hterm.
  rewrite W64.to_uint_eq W2u32.to_uint_zeroextu64 W64.to_uint0.
  trivial.
+ move=> heq.
  rewrite heq W32.xorwK.
  by simplify.
qed.

lemma poly_mismatch_result_zero_words_equal
    (ap bp : BArray1024.t) (n : int) :
  0 <= n =>
  Mode2VerifyTailChallenge.poly_mismatch_result_word
    (Mode2VerifyTailChallenge.poly_mismatch_acc_prefix ap bp n) =
    W64.zero =>
  forall i, 0 <= i < n =>
    BArray1024.get32 ap i = BArray1024.get32 bp i.
proof.
move=> hn hresult i hi.
apply/poly_mismatch_term_eq_zero.
apply (poly_mismatch_acc_prefix_zero_terms ap bp n hn).
+ by move: hresult; rewrite poly_mismatch_result_word_eq_zero.
+ exact hi.
qed.

op accepted_observed_challenges_equal
    (reject : W64.t) (parsed_cp cprime : BArray1024.t) : bool =
  reject = W64.zero =>
  forall i,
    0 <= i < Mode2VerifyTailChallenge.mode2_challenge_words =>
    BArray1024.get32 parsed_cp i = BArray1024.get32 cprime i.

lemma accepted_observed_mismatch_word_zero_implies_challenges_equal
    (reject : W64.t) (parsed_cp cprime : BArray1024.t) :
  VerifyActualAcceptMismatchRawPostFreeze.accepted_observed_mismatch_word_zero
    reject parsed_cp cprime =>
  accepted_observed_challenges_equal reject parsed_cp cprime.
proof.
rewrite
  /VerifyActualAcceptMismatchRawPostFreeze.accepted_observed_mismatch_word_zero
  /accepted_observed_challenges_equal.
move=> hmismatch hreject i hi.
apply
  (poly_mismatch_result_zero_words_equal parsed_cp cprime
    Mode2VerifyTailChallenge.mode2_challenge_words).
+ by rewrite /Mode2VerifyTailChallenge.mode2_challenge_words.
+ apply hmismatch.
  exact hreject.
+ exact hi.
qed.

lemma verify_full_m23_mu_trace_accept_challenges_equal :
  hoare [FullM23MuTrace.run :
    true
    ==>
    accepted_observed_challenges_equal
      res FullM23MuTrace.observed_cp FullM23MuTrace.observed_cprime].
proof.
have hold := VerifyActualAcceptMismatchRawPostFreeze.verify_full_m23_mu_trace_accept_mismatch_word_zero.
conseq hold => //=.
exact accepted_observed_mismatch_word_zero_implies_challenges_equal.
qed.

lemma actual_verify_full_m23_accept_observed_challenges_equal :
  equiv [Raw._verify_full_m23 ~ FullM23MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp, k_i, l_i, m_i, sigbytes_i,
      vkbytes_i, highbits_len_i, tau_i, b2sq_i, hb_count_i, hb_m_i,
      hb_offset_i, h_count_i, h_m_i, h_offset_i, base_hb_i, base_h_i,
      payload_limit_i}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_challenges_equal
      res{1} FullM23MuTrace.observed_cp{2}
      FullM23MuTrace.observed_cprime{2}].
proof.
conseq VerifyActualAcceptMismatchRawPostFreeze.actual_verify_full_m23_accept_observed_mismatch_word_zero => //=.
move=> &1 &2 _ result_left result_right observed_cp observed_cprime
  [hframe hmismatch].
split.
+ exact hframe.
+ apply
    (accepted_observed_mismatch_word_zero_implies_challenges_equal
      result_left observed_cp observed_cprime).
  exact hmismatch.
qed.

lemma verify_full_mode2_mu_trace_accept_challenges_equal :
  hoare [FullMode2MuTrace.run :
    true
    ==>
    accepted_observed_challenges_equal
      res FullMode2MuTrace.observed_cp FullMode2MuTrace.observed_cprime].
proof.
have hold := VerifyActualAcceptMismatchRawPostFreeze.verify_full_mode2_mu_trace_accept_mismatch_word_zero.
conseq hold => //=.
exact accepted_observed_mismatch_word_zero_implies_challenges_equal.
qed.

lemma verify_internal_mode2_mu_trace_accept_challenges_equal :
  hoare [InternalMode2MuTrace.run :
    true
    ==>
    accepted_observed_challenges_equal
      res InternalMode2MuTrace.observed_cp
      InternalMode2MuTrace.observed_cprime].
proof.
have hold := VerifyActualAcceptMismatchRawPostFreeze.verify_internal_mode2_mu_trace_accept_mismatch_word_zero.
conseq hold => //=.
exact accepted_observed_mismatch_word_zero_implies_challenges_equal.
qed.

lemma verify_raw_api_mu_trace_accept_challenges_equal :
  hoare [RawApiMuTrace.run :
    true
    ==>
    accepted_observed_challenges_equal
      res RawApiMuTrace.observed_cp RawApiMuTrace.observed_cprime].
proof.
have hold := VerifyActualAcceptMismatchRawPostFreeze.verify_raw_api_mu_trace_accept_mismatch_word_zero.
conseq hold => //=.
exact accepted_observed_mismatch_word_zero_implies_challenges_equal.
qed.

lemma verify_cryptolab_mu_trace_accept_challenges_equal :
  hoare [CryptolabMuTrace.run :
    true
    ==>
    accepted_observed_challenges_equal
      res CryptolabMuTrace.observed_cp CryptolabMuTrace.observed_cprime].
proof.
have hold := VerifyActualAcceptMismatchRawPostFreeze.verify_cryptolab_mu_trace_accept_mismatch_word_zero.
conseq hold => //=.
exact accepted_observed_mismatch_word_zero_implies_challenges_equal.
qed.

lemma actual_verify_full_mode2_accept_observed_challenges_equal :
  equiv [Raw._verify_full_mode2 ~ FullMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_challenges_equal
      res{1} FullMode2MuTrace.observed_cp{2}
      FullMode2MuTrace.observed_cprime{2}].
proof.
conseq VerifyActualAcceptMismatchRawPostFreeze.actual_verify_full_mode2_accept_observed_mismatch_word_zero => //=.
move=> &1 &2 _ result_left result_right observed_cp observed_cprime
  [hframe hmismatch].
split.
+ exact hframe.
+ apply
    (accepted_observed_mismatch_word_zero_implies_challenges_equal
      result_left observed_cp observed_cprime).
  exact hmismatch.
qed.

lemma actual_verify_internal_mode2_accept_observed_challenges_equal :
  equiv [Raw.sign_verify_internal_mode2_jazz ~ InternalMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_challenges_equal
      res{1} InternalMode2MuTrace.observed_cp{2}
      InternalMode2MuTrace.observed_cprime{2}].
proof.
conseq VerifyActualAcceptMismatchRawPostFreeze.actual_verify_internal_mode2_accept_observed_mismatch_word_zero => //=.
move=> &1 &2 _ result_left result_right observed_cp observed_cprime
  [hframe hmismatch].
split.
+ exact hframe.
+ apply
    (accepted_observed_mismatch_word_zero_implies_challenges_equal
      result_left observed_cp observed_cprime).
  exact hmismatch.
qed.

lemma actual_verify_raw_api_accept_observed_challenges_equal :
  equiv [Raw._api_verify_mode2_raw ~ RawApiMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_challenges_equal
      res{1} RawApiMuTrace.observed_cp{2}
      RawApiMuTrace.observed_cprime{2}].
proof.
conseq VerifyActualAcceptMismatchRawPostFreeze.actual_verify_raw_api_accept_observed_mismatch_word_zero => //=.
move=> &1 &2 _ result_left result_right observed_cp observed_cprime
  [hframe hmismatch].
split.
+ exact hframe.
+ apply
    (accepted_observed_mismatch_word_zero_implies_challenges_equal
      result_left observed_cp observed_cprime).
  exact hmismatch.
qed.

lemma actual_verify_cryptolab_accept_observed_challenges_equal :
  equiv [Raw.cryptolab_haetae_mode2_verify_internal ~ CryptolabMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    accepted_observed_challenges_equal
      res{1} CryptolabMuTrace.observed_cp{2}
      CryptolabMuTrace.observed_cprime{2}].
proof.
conseq VerifyActualAcceptMismatchRawPostFreeze.actual_verify_cryptolab_accept_observed_mismatch_word_zero => //=.
move=> &1 &2 _ result_left result_right observed_cp observed_cprime
  [hframe hmismatch].
split.
+ exact hframe.
+ apply
    (accepted_observed_mismatch_word_zero_implies_challenges_equal
      result_left observed_cp observed_cprime).
  exact hmismatch.
qed.

end VerifyActualAcceptChallengeEqualityRawPostFreeze.
