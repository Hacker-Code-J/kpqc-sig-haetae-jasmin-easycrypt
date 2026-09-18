require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import SamplerTarget FixedPointSpec SamplerConstants ReferenceConstants.
import SLH64.

lemma smulh48_correct (aa bb : W64.t) :
  hoare [SamplerTarget.M.__smulh48 : a = aa /\ b = bb
    ==> res = smulh48_word aa bb].
proof. proc; wp; skip; auto => />; rewrite /smulh48_word /=. qed.

lemma smulh48_jazz_correct (aa bb : W64.t) :
  hoare [SamplerTarget.M.smulh48_jazz : a = aa /\ b = bb
    ==> res = smulh48_word aa bb].
proof.
  proc; call (smulh48_correct aa bb); wp; skip; auto => />.
qed.

lemma smulh48_lossless : islossless SamplerTarget.M.__smulh48.
proof. proc; wp; skip; auto. qed.

lemma smulh48_jazz_lossless : islossless SamplerTarget.M.smulh48_jazz.
proof. proc; call smulh48_lossless; wp; skip; auto. qed.

lemma approx_exp_correct (xx : W64.t) :
  hoare [SamplerTarget.M._approx_exp : x = xx
    ==> res = approx_exp_word xx].
proof.
  proc.
  do 10!(wp; ecall (smulh48_correct result x)).
  wp; skip; auto => />; rewrite /approx_exp_word.
qed.

lemma approx_exp_jazz_correct (xx : W64.t) :
  hoare [SamplerTarget.M.approx_exp_jazz : x = xx
    ==> res = approx_exp_word xx].
proof. proc; call (approx_exp_correct xx); wp; skip; auto => />. qed.

lemma approx_exp_lossless : islossless SamplerTarget.M._approx_exp.
proof. proc; do 10!(wp; call smulh48_lossless); wp; skip; auto. qed.

lemma approx_exp_jazz_lossless : islossless SamplerTarget.M.approx_exp_jazz.
proof. proc; call approx_exp_lossless; wp; skip; auto. qed.

(* Arithmetic facts connecting the extracted operations to integer rounding. *)
lemma w64_sign_bit (a : W64.t) :
  a.[63] = (9223372036854775808 <= W64.to_uint a).
proof.
  rewrite W64.get_to_uint /=.
  have /= ha := W64.to_uint_cmp a.
  case (9223372036854775808 <= W64.to_uint a) => hs.
  + have -> : W64.to_uint a %/ 9223372036854775808 = 1.
    + rewrite divz_eqP //; smt().
    trivial.
  have -> : W64.to_uint a %/ 9223372036854775808 = 0.
  + rewrite divz_eqP //; smt().
  trivial.
qed.

lemma w64_sign_mask (a : W64.t) :
  a `|>>>` 63 =
    if 9223372036854775808 <= W64.to_uint a then W64.onew else W64.zero.
proof.
  apply W64.wordP => i hi.
  rewrite W64.sarE W64.initE hi /=.
  have -> : min 63 (i + 63) = 63 by smt().
  rewrite w64_sign_bit.
  case (9223372036854775808 <= W64.to_uint a) => hs /=; smt().
qed.

lemma w64_nonzero_carry (r : W64.t) :
  (r `|` (W64.zero - r)) `>>>` 63 =
    W64.of_int (b2i (W64.to_uint r <> 0)).
proof.
  apply W64.to_uint_eq.
  rewrite W64.to_uint_shr //=.
  case (W64.to_uint r = 0) => hz.
  + have -> : r = W64.zero by rewrite W64.to_uint_eq W64.to_uint0 hz.
    by rewrite W64.WRingA.oppr0 W64.orw0 !W64.to_uint0 /b2i /=.
  rewrite /b2i /=.
  have /= hr := W64.to_uint_cmp r.
  have /= ho := W64.to_uint_cmp (r `|` (W64.zero - r)).
  have h1 := W64.ule_orw r (W64.zero - r).
  have h2 := W64.ule_orw (W64.zero - r) r.
  rewrite W64.uleE /= in h1.
  rewrite W64.uleE W64.orwC in h2.
  rewrite W64.WRingA.sub0r W64.to_uintNE modz_small 1:/# /= in h2.
  rewrite divz_eqP //; smt().
qed.

lemma w64_sign_product_mask (a b : W64.t) :
  ((a `|>>>` 63) `&` b) =
    W64.of_int (b2i (9223372036854775808 <= W64.to_uint a) * W64.to_uint b).
proof.
  rewrite w64_sign_mask.
  case (9223372036854775808 <= W64.to_uint a) => hs;
    rewrite /b2i /= ?W64.and1w ?W64.and0w ?W64.to_uintK //.
qed.

lemma radix64_div48 (p c : int) :
  (p - 18446744073709551616 * c) %/ 281474976710656 =
    (p %/ 18446744073709551616 - c) * 65536 +
    p %% 18446744073709551616 %/ 281474976710656.
proof.
  have hp := divz_eq p 18446744073709551616.
  have -> : p - 18446744073709551616 * c =
    ((p %/ 18446744073709551616 - c) * 65536) * 281474976710656 +
      p %% 18446744073709551616 by smt().
  by rewrite divzMDl.
qed.

lemma radix64_mod48 (p c : int) :
  (p - 18446744073709551616 * c) %% 281474976710656 =
    (p %% 18446744073709551616) %% 281474976710656.
proof.
  have hp := divz_eq p 18446744073709551616.
  have -> : p - 18446744073709551616 * c =
    ((p %/ 18446744073709551616 - c) * 65536) * 281474976710656 +
      p %% 18446744073709551616 by smt().
  by rewrite modzMDl.
qed.

lemma w64_signed_product (a b : W64.t) :
  W64.to_sint a * W64.to_uint b =
    W64.to_uint a * W64.to_uint b - 18446744073709551616 *
      (b2i (9223372036854775808 <= W64.to_uint a) * W64.to_uint b).
proof.
  rewrite W64.to_sintE /W64.smod /b2i /=.
  case (9223372036854775808 <= W64.to_uint a) => hs /=; try done; ring.
qed.

lemma w64_merge_product (a b : W64.t) :
  ((W64.mulhi a b - ((a `|>>>` 63) `&` b)) `<<<` 16) `|`
      ((a * b) `>>>` 48) =
  W64.of_int ((W64.to_sint a * W64.to_uint b) %/ 281474976710656).
proof.
  rewrite W64.orw_disjoint.
  + rewrite W64.andwC; apply W64.shrw_shlw_disjoint; trivial.
  rewrite w64_sign_product_mask /W64.mulhi -W64.of_intS W64.shlMP //=.
  rewrite W64.mulE /W64.ulift2 W64.shrDP //=.
  by rewrite w64_signed_product radix64_div48.
qed.


(* All-input integer refinement and the explicit signed-fit corollary. *)
lemma smulh48_word_is_ceil (a b : W64.t) :
  smulh48_word a b = W64.of_int (smulh48_ceil a b).
proof.
  rewrite /smulh48_word W64.muluE /= w64_nonzero_carry w64_merge_product.
  have -> : 281474976710655 = 2^48 - 1 by trivial.
  rewrite W64.to_uint_and_mod // W64.to_uintM /=.
  by rewrite /smulh48_ceil /= !w64_signed_product radix64_mod48.
qed.

lemma smulh48_ceil_bounds (a b : W64.t) :
  (smulh48_ceil a b - 1) * 281474976710656 < W64.to_sint a * W64.to_uint b /\
  W64.to_sint a * W64.to_uint b <= smulh48_ceil a b * 281474976710656.
proof.
  pose p := W64.to_sint a * W64.to_uint b.
  have hp := divz_eq p 281474976710656.
  have /= hr := modz_cmp p 281474976710656.
  rewrite /smulh48_ceil -/p /b2i.
  case (p %% 281474976710656 <> 0) => hz /=; smt().
qed.

lemma smulh48_integer_correct (aa bb : W64.t) :
  hoare [SamplerTarget.M.__smulh48 : a = aa /\ b = bb
    ==> res = W64.of_int (smulh48_ceil aa bb)].
proof.
  conseq (smulh48_correct aa bb) => />.
  by move=> &hr; rewrite smulh48_word_is_ceil.
qed.

lemma smulh48_jazz_integer_correct (aa bb : W64.t) :
  hoare [SamplerTarget.M.smulh48_jazz : a = aa /\ b = bb
    ==> res = W64.of_int (smulh48_ceil aa bb)].
proof.
  conseq (smulh48_jazz_correct aa bb) => />.
  by move=> &hr; rewrite smulh48_word_is_ceil.
qed.

lemma smulh48_jazz_signed_correct (aa bb : W64.t) :
  -9223372036854775808 <= smulh48_ceil aa bb <= 9223372036854775807 =>
  hoare [SamplerTarget.M.smulh48_jazz : a = aa /\ b = bb
    ==> W64.to_sint res = smulh48_ceil aa bb].
proof.
  move=> hfit.
  conseq (smulh48_jazz_integer_correct aa bb) => />.
  move=> &hr -> ->; apply W64.to_sintK_small; exact hfit.
qed.

lemma smulh48_signed_correct (aa bb : W64.t) :
  -9223372036854775808 <= smulh48_ceil aa bb <= 9223372036854775807 =>
  hoare [SamplerTarget.M.__smulh48 : a = aa /\ b = bb
    ==> W64.to_sint res = smulh48_ceil aa bb].
proof.
  move=> hfit.
  conseq (smulh48_integer_correct aa bb) => />.
  move=> &hr -> ->; apply W64.to_sintK_small; exact hfit.
qed.

(* Total functional correctness: termination and the integer result together. *)
lemma smulh48_total_correct (aa bb : W64.t) :
  phoare [SamplerTarget.M.__smulh48 : a = aa /\ b = bb
    ==> res = W64.of_int (smulh48_ceil aa bb)] = 1%r.
proof. by conseq smulh48_lossless (smulh48_integer_correct aa bb). qed.

lemma smulh48_jazz_total_correct (aa bb : W64.t) :
  phoare [SamplerTarget.M.smulh48_jazz : a = aa /\ b = bb
    ==> res = W64.of_int (smulh48_ceil aa bb)] = 1%r.
proof. by conseq smulh48_jazz_lossless (smulh48_jazz_integer_correct aa bb). qed.

lemma approx_exp_total_correct (xx : W64.t) :
  phoare [SamplerTarget.M._approx_exp : x = xx
    ==> res = approx_exp_word xx] = 1%r.
proof. by conseq approx_exp_lossless (approx_exp_correct xx). qed.

lemma approx_exp_jazz_total_correct (xx : W64.t) :
  phoare [SamplerTarget.M.approx_exp_jazz : x = xx
    ==> res = approx_exp_word xx] = 1%r.
proof. by conseq approx_exp_jazz_lossless (approx_exp_jazz_correct xx). qed.

(* The Horner sequence below is generated independently from HAETAE-1.2.0 C.
   Its multiplication parameter is now the mathematical rounding operation. *)
lemma approx_exp_integer_reference (xx : W64.t) :
  approx_exp_word xx = reference_approx_exp
    (fun a b => W64.of_int (smulh48_ceil a b)) xx.
proof.
  rewrite approx_exp_matches_reference /reference_approx_exp /=.
  by rewrite !smulh48_word_is_ceil.
qed.

lemma approx_exp_jazz_reference_correct (xx : W64.t) :
  phoare [SamplerTarget.M.approx_exp_jazz : x = xx
    ==> res = reference_approx_exp
      (fun a b => W64.of_int (smulh48_ceil a b)) xx] = 1%r.
proof.
  conseq (approx_exp_jazz_total_correct xx) => />.
  by rewrite approx_exp_integer_reference.
qed.
