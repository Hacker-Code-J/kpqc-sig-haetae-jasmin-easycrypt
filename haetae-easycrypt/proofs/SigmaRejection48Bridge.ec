require import AllCore IntDiv List Distr DInterval.
from Jasmin require import JModel_x86.
require import BArray26 SamplerTarget SigmaSpec SigmaCorrectness SigmaRoundingCorrectness
  SigmaExpInputBounds FixedPointSpec Rejection48Spec Rejection48Correctness.

(* Only the six rejection bytes are replaced. The CDT and noise inputs are
   held fixed; no property of a concrete SHAKE stream is assumed. *)
op [opaque] sigma_rejection48_patch (p : BArray26.t) (u : int) : BArray26.t =
  BArray26.init (fun i => if 11 <= i < 17
    then W64.of_int u \bits8 (i - 11) else BArray26.get8 p i).

op [opaque] sigma_rejection48_rounded (p : BArray26.t) : W64.t = (sigma76_spec p).`1.
op [opaque] sigma_rejection48_threshold (p : BArray26.t) : W64.t =
  approx_exp_word (sigma_exp_argument p).

lemma sigma_rejection48_patch_byte p u i : 0 <= i < 26 =>
  BArray26.get8 (sigma_rejection48_patch p u) i =
    if 11 <= i < 17 then W64.of_int u \bits8 (i - 11) else BArray26.get8 p i.
proof. by move=> hi; rewrite /sigma_rejection48_patch BArray26.initiE. qed.

lemma sigma_rejection48_patch_outside p u i :
  0 <= i < 26 => (i < 11 \/ 17 <= i) =>
  BArray26.get8 (sigma_rejection48_patch p u) i = BArray26.get8 p i.
proof. move=> hi hout; rewrite sigma_rejection48_patch_byte 1:hi; smt(). qed.

lemma sigma_rejection48_patch_inside p u i : 0 <= i < 6 =>
  BArray26.get8 (sigma_rejection48_patch p u) (11 + i) = W64.of_int u \bits8 i.
proof.
  move=> hi; rewrite sigma_rejection48_patch_byte 1:/#.
  have -> : 11 <= 11 + i < 17 by smt().
  by rewrite /=.
qed.

lemma sigma_rejection48_patch_cdt_low p u :
  cdt_lo_input (sigma_rejection48_patch p u) = cdt_lo_input p.
proof.
  by rewrite /cdt_lo_input /le8_word /le6_word /le3_word /byte_word
    !sigma_rejection48_patch_outside.
qed.

lemma sigma_rejection48_patch_cdt_high p u :
  cdt_hi_input (sigma_rejection48_patch p u) = cdt_hi_input p.
proof.
  by rewrite /cdt_hi_input /le3_word /byte_word !sigma_rejection48_patch_outside.
qed.

lemma sigma_rejection48_patch_noise_low p u :
  le6_word (sigma_rejection48_patch p u) 17 = le6_word p 17.
proof. by rewrite /le6_word /le3_word /byte_word !sigma_rejection48_patch_outside. qed.

lemma sigma_rejection48_patch_noise_high p u :
  le3_word (sigma_rejection48_patch p u) 23 = le3_word p 23.
proof. by rewrite /le3_word /byte_word !sigma_rejection48_patch_outside. qed.

lemma sigma_rejection48_patch_rounded p u :
  sigma_rejection48_rounded (sigma_rejection48_patch p u) = sigma_rejection48_rounded p.
proof.
  by rewrite /sigma_rejection48_rounded /sigma76_spec
    sigma_rejection48_patch_cdt_low sigma_rejection48_patch_cdt_high
    /sigma_from_cdt /= sigma_rejection48_patch_noise_low sigma_rejection48_patch_noise_high.
qed.

lemma sigma_rejection48_patch_argument p u :
  sigma_exp_argument (sigma_rejection48_patch p u) = sigma_exp_argument p.
proof.
  by rewrite /sigma_exp_argument sigma_rejection48_patch_cdt_low
    sigma_rejection48_patch_cdt_high /sigma_exp_from_cdt
    sigma_rejection48_patch_noise_low sigma_rejection48_patch_noise_high.
qed.

lemma sigma_rejection48_patch_threshold p u :
  sigma_rejection48_threshold (sigma_rejection48_patch p u) = sigma_rejection48_threshold p.
proof. by rewrite /sigma_rejection48_threshold sigma_rejection48_patch_argument. qed.

lemma sigma_rejection48_assemble (w : W64.t) :
  (((((zeroextu64 (w \bits8 0) `|` (zeroextu64 (w \bits8 1) `<<<` 8)) `|`
    (zeroextu64 (w \bits8 2) `<<<` 16)) `|` (zeroextu64 (w \bits8 3) `<<<` 24)) `|`
    (zeroextu64 (w \bits8 4) `<<<` 32)) `|` (zeroextu64 (w \bits8 5) `<<<` 40)) =
      w `&` W64.masklsb 48.
proof.
  apply W64.wordP => i hi.
  rewrite !W64.orwE !W64.shlwE !W8u8.zeroextu64_bit W64.andwE W64.masklsbE /=.
  smt(W8u8.bits8iE).
qed.

lemma sigma_rejection48_patch_decode p u : 0 <= u < 281474976710656 =>
  le6_word (sigma_rejection48_patch p u) 11 = W64.of_int u.
proof.
  move=> hu.
  rewrite /le6_word /le3_word /byte_word !sigma_rejection48_patch_byte //=.
  rewrite sigma_rejection48_assemble.
  apply (sigma_mask_id (W64.of_int u) 48); first trivial.
  rewrite W64.to_uint_small 1:/# /=; smt().
qed.

lemma sigma_rejection48_spec_acceptance p :
  (sigma76_spec p).`4 = rejection48_word (le6_word p 11)
    (sigma_rejection48_threshold p) (sigma_rejection48_rounded p).
proof.
  by rewrite /sigma_rejection48_threshold /sigma_rejection48_rounded
    /sigma_exp_argument /sigma_exp_from_cdt /sigma_square_exp_argument
    /sigma76_spec /sigma_from_cdt /rejection48_word /=.
qed.

lemma sigma_rejection48_patched_acceptance p u : 0 <= u < 281474976710656 =>
  (sigma76_spec (sigma_rejection48_patch p u)).`4 =
    rejection48_word (W64.of_int u) (sigma_rejection48_threshold p) (sigma_rejection48_rounded p).
proof.
  move=> hu; by rewrite sigma_rejection48_spec_acceptance
    sigma_rejection48_patch_threshold sigma_rejection48_patch_rounded
    (sigma_rejection48_patch_decode p u hu).
qed.

module SigmaRejection48Experiment = {
  proc sample(p : BArray26.t) : bool = {
    var u : int;
    var patched : BArray26.t;
    var result : W64.t * W64.t * W64.t * W64.t;
    u <$ rejection48_uniform;
    patched <- sigma_rejection48_patch p u;
    result <@ SamplerTarget.M.__sample_gauss_sigma76_regs(patched);
    return result.`4 = W64.one;
  }
}.

module SigmaRejection48Word = {
  proc sample(p : BArray26.t) : bool = {
    var u : int;
    u <$ rejection48_uniform;
    return rejection48_word (W64.of_int u) (sigma_rejection48_threshold p)
      (sigma_rejection48_rounded p) = W64.one;
  }
}.

lemma sigma_rejection48_actual_equiv :
  equiv [SigmaRejection48Experiment.sample ~ SigmaRejection48Word.sample : ={p} ==> ={res}].
proof.
  proc; wp.
  ecall{1} (sigma76_regs_total_correct (sigma_rejection48_patch p{1} u{1})).
  wp; rnd; skip.
  move=> &1 &2 hp; rewrite hp /=.
  move=> u hu.
  have hurange : 0 <= u < 281474976710656 by
    move: hu; rewrite /rejection48_uniform DInterval.supp_dinter; smt().
  rewrite hu /=.
  move=> result ->.
  by rewrite (sigma_rejection48_patched_acceptance p{2} u hurange).
qed.

lemma sigma_rejection48_word_law p0 &m :
  Pr[SigmaRejection48Word.sample(p0) @ &m : res] =
    mu rejection48_uniform (fun u => rejection48_word (W64.of_int u)
      (sigma_rejection48_threshold p0) (sigma_rejection48_rounded p0) = W64.one).
proof.
  byphoare (_ : p = p0 ==> res) => //.
  proc; rnd; skip; auto => />.
qed.

lemma sigma_rejection48_actual_word_law p0 &m :
  Pr[SigmaRejection48Experiment.sample(p0) @ &m : res] =
    mu rejection48_uniform (fun u => rejection48_word (W64.of_int u)
      (sigma_rejection48_threshold p0) (sigma_rejection48_rounded p0) = W64.one).
proof.
  rewrite -(sigma_rejection48_word_law p0 &m).
  by byequiv sigma_rejection48_actual_equiv.
qed.

lemma sigma_rejection48_actual_probability p0 &m :
  W64.to_uint (sigma_rejection48_threshold p0) < 9223372036854775808 =>
  Pr[SigmaRejection48Experiment.sample(p0) @ &m : res] =
    rejection48_probability (W64.to_uint (sigma_rejection48_threshold p0))
      (sigma_rejection48_rounded p0).
proof.
  move=> he; rewrite sigma_rejection48_actual_word_law.
  have he0 := W64.to_uint_cmp (sigma_rejection48_threshold p0).
  have h := rejection48_word_probability (W64.to_uint (sigma_rejection48_threshold p0))
    (sigma_rejection48_rounded p0) _; first smt().
  by move: h; rewrite W64.to_uintK.
qed.

lemma sigma_rejection48_actual_ll : islossless SigmaRejection48Experiment.sample.
proof.
  proc; wp; call sigma76_regs_lossless; wp; rnd; skip; auto => />.
  rewrite /rejection48_uniform; apply DInterval.dinter_ll; trivial.
qed.
