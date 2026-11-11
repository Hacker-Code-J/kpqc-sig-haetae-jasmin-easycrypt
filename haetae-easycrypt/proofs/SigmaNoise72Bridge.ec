require import AllCore IntDiv List Distr DInterval RealSeries.
from Jasmin require import JModel_x86.
require import BArray26 SigmaSpec SigmaRawSpec SigmaRoundingCorrectness
  Rejection48Spec Rejection48Correctness SigmaRejection48Bridge
  SigmaExpAcceptanceCorrectness SigmaRawNoiseSpec.

(* Replace precisely the nine noise bytes.  The CDT and rejection bytes
   remain the caller's input; uniformity belongs to the experiment below. *)
op [opaque] sigma_noise72_patch (p : BArray26.t) (y : int) : BArray26.t =
  BArray26.init (fun i =>
    if 17 <= i < 23 then W64.of_int y \bits8 (i-17)
    else if 23 <= i < 26 then W64.of_int (y %/ sr_scale) \bits8 (i-23)
    else BArray26.get8 p i).

lemma sigma_noise72_patch_byte p y i : 0 <= i < 26 =>
  BArray26.get8 (sigma_noise72_patch p y) i =
    if 17 <= i < 23 then W64.of_int y \bits8 (i-17)
    else if 23 <= i < 26 then W64.of_int (y %/ sr_scale) \bits8 (i-23)
    else BArray26.get8 p i.
proof. by move=> hi; rewrite /sigma_noise72_patch BArray26.initiE. qed.

lemma sigma_noise72_patch_outside p y i : 0 <= i < 17 =>
  BArray26.get8 (sigma_noise72_patch p y) i = BArray26.get8 p i.
proof. move=> hi; rewrite sigma_noise72_patch_byte 1:/#; smt(). qed.

lemma sigma_noise72_patch_cdt_low p y :
  cdt_lo_input (sigma_noise72_patch p y) = cdt_lo_input p.
proof.
  by rewrite /cdt_lo_input /le8_word /le6_word /le3_word /byte_word
    !sigma_noise72_patch_outside.
qed.

lemma sigma_noise72_patch_cdt_high p y :
  cdt_hi_input (sigma_noise72_patch p y) = cdt_hi_input p.
proof.
  by rewrite /cdt_hi_input /le3_word /byte_word !sigma_noise72_patch_outside.
qed.

lemma sigma_noise72_patch_cdt p y :
  sr_cdt (sigma_noise72_patch p y) = sr_cdt p.
proof.
  by rewrite /sr_cdt sigma_noise72_patch_cdt_low sigma_noise72_patch_cdt_high.
qed.

lemma sigma_noise72_patch_rejection p y :
  le6_word (sigma_noise72_patch p y) 11 = le6_word p 11.
proof.
  by rewrite /le6_word /le3_word /byte_word !sigma_noise72_patch_outside.
qed.

lemma sigma_noise72_assemble3 (w : W64.t) :
  (zeroextu64 (w \bits8 0) `|` (zeroextu64 (w \bits8 1) `<<<` 8)) `|`
    (zeroextu64 (w \bits8 2) `<<<` 16) = w `&` W64.masklsb 24.
proof.
  apply W64.wordP => i hi.
  rewrite !W64.orwE !W64.shlwE !W8u8.zeroextu64_bit W64.andwE W64.masklsbE /=.
  smt(W8u8.bits8iE).
qed.

lemma sigma_noise72_patch_low p y :
  W64.to_uint (le6_word (sigma_noise72_patch p y) 17) = y %% sr_scale.
proof.
  rewrite /le6_word /le3_word /byte_word !sigma_noise72_patch_byte //=.
  rewrite sigma_rejection48_assemble W64.to_uint_and_mod //= W64.of_uintK.
  rewrite /sr_scale modz_dvd //=.
qed.

lemma sigma_noise72_patch_high p y : 0 <= y < sr_noise_modulus =>
  W64.to_uint (le3_word (sigma_noise72_patch p y) 23) = y %/ sr_scale.
proof.
  move=> hy.
  have hq : 0 <= y %/ sr_scale < 16777216.
  + have hd := divz_eq y sr_scale.
    have hm := modz_cmp y sr_scale.
    move: hy hd hm; rewrite /sr_scale /sr_noise_modulus; smt().
  rewrite /le3_word /byte_word !sigma_noise72_patch_byte //=.
  rewrite sigma_noise72_assemble3 W64.to_uint_and_mod //=.
  rewrite W64.to_uint_small 1:/# modz_small 1:hq.
  trivial.
qed.

lemma sigma_noise72_patch_decode p y : 0 <= y < sr_noise_modulus =>
  sr_noise (sigma_noise72_patch p y) = y.
proof.
  move=> hy; rewrite /sr_noise sigma_noise72_patch_low sigma_noise72_patch_high 1:hy.
  have h := divz_eq y sr_scale; smt().
qed.

lemma sigma_noise72_support y : y \in sr_noise_uniform =>
  0 <= y < sr_noise_modulus.
proof. by rewrite sr_noise_uniform_support /sr_noise_modulus. qed.

lemma sigma_noise72_uniform_decode p y : y \in sr_noise_uniform =>
  sr_noise (sigma_noise72_patch p y) = y /\
  sr_cdt (sigma_noise72_patch p y) = sr_cdt p.
proof.
  move=> hy; split; last exact (sigma_noise72_patch_cdt p y).
  exact (sigma_noise72_patch_decode p y (sigma_noise72_support y hy)).
qed.

lemma sigma_noise72_patch_mismatch p y : 0 <= y < sr_noise_modulus =>
  sr_zero_mismatch (sigma_noise72_patch p y) = sr_noise_mismatch (sr_cdt p) y.
proof.
  move=> hy; by rewrite /sr_zero_mismatch /sr_noise_mismatch
    sigma_noise72_patch_cdt sigma_noise72_patch_decode 1:hy.
qed.

lemma sigma_noise72_mismatch_probability p :
  mu sr_noise_uniform (fun y => sr_zero_mismatch (sigma_noise72_patch p y)) =
    if sr_cdt p = 0 then 32767%r / 4722366482869645213696%r else 0%r.
proof.
  rewrite -(sr_noise_mismatch_probability (sr_cdt p)).
  apply mu_eq_support => y hy.
  exact (sigma_noise72_patch_mismatch p y (sigma_noise72_support y hy)).
qed.

module SigmaNoise72Experiment = {
  proc sample(p : BArray26.t) : bool = {
    var y : int;
    var accepted : bool;
    y <$ sr_noise_uniform;
    accepted <@ SigmaRejection48Experiment.sample(sigma_noise72_patch p y);
    return accepted;
  }
}.

module SigmaNoise72Word = {
  proc sample(p : BArray26.t) : bool = {
    var y : int;
    var accepted : bool;
    y <$ sr_noise_uniform;
    accepted <@ SigmaRejection48Word.sample(sigma_noise72_patch p y);
    return accepted;
  }
}.

lemma sigma_noise72_actual_equiv :
  equiv [SigmaNoise72Experiment.sample ~ SigmaNoise72Word.sample : ={p} ==> ={res}].
proof.
  proc; call sigma_rejection48_actual_equiv.
  rnd; skip; auto => />.
qed.

lemma sigma_noise72_word_law p0 &m :
  Pr[SigmaNoise72Word.sample(p0) @ &m : res] =
    E sr_noise_uniform (fun y =>
      mu rejection48_uniform (fun u => rejection48_word (W64.of_int u)
        (sigma_rejection48_threshold (sigma_noise72_patch p0 y))
        (sigma_rejection48_rounded (sigma_noise72_patch p0 y)) = W64.one)).
proof.
  byphoare (_ : p = p0 ==> res) => //.
  proc; inline SigmaRejection48Word.sample; wp.
  rndsem* 0.
  rnd (fun (pu : BArray26.t * int) => rejection48_word (W64.of_int pu.`2)
    (sigma_rejection48_threshold pu.`1) (sigma_rejection48_rounded pu.`1) = W64.one).
  skip; auto => />.
  rewrite dletE /E.
  apply RealSeries.eq_sum => y /=.
  rewrite dmapE /(\o) /=; ring.
qed.

lemma sigma_noise72_actual_word_law p0 &m :
  Pr[SigmaNoise72Experiment.sample(p0) @ &m : res] =
    E sr_noise_uniform (fun y =>
      mu rejection48_uniform (fun u => rejection48_word (W64.of_int u)
        (sigma_rejection48_threshold (sigma_noise72_patch p0 y))
        (sigma_rejection48_rounded (sigma_noise72_patch p0 y)) = W64.one)).
proof.
  rewrite -(sigma_noise72_word_law p0 &m).
  by byequiv sigma_noise72_actual_equiv.
qed.

lemma sigma_noise72_actual_probability p0 &m :
  Pr[SigmaNoise72Experiment.sample(p0) @ &m : res] =
    E sr_noise_uniform (fun y =>
      rejection48_probability
        (W64.to_uint (sigma_rejection48_threshold (sigma_noise72_patch p0 y)))
        (sigma_rejection48_rounded (sigma_noise72_patch p0 y))).
proof.
  rewrite sigma_noise72_actual_word_law.
  apply eq_exp => y _.
  have hfit := sigma_exp_threshold_fit (sigma_noise72_patch p0 y).
  have h := rejection48_word_probability
    (W64.to_uint (sigma_rejection48_threshold (sigma_noise72_patch p0 y)))
    (sigma_rejection48_rounded (sigma_noise72_patch p0 y)) hfit.
  by move: h; rewrite W64.to_uintK.
qed.

lemma sigma_noise72_actual_ll : islossless SigmaNoise72Experiment.sample.
proof.
  proc; call sigma_rejection48_actual_ll; rnd; skip; auto => />.
  exact sr_noise_uniform_ll.
qed.
