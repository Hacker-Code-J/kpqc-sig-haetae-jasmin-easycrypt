require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import BArray26 SamplerTarget SigmaSpec SigmaCorrectness
  SigmaRoundingCorrectness SigmaRawSpec SigmaRejection48Bridge SigmaNoise72Bridge
  SigmaCDT83Patch CDTDistributionBridge GaussianRetryInputs.

(* Only the low three bits of byte ten belong to the 83-bit CDT input. *)
op [opaque] gub_canonical (p : BArray26.t) : BArray26.t =
  BArray26.set8 p 10 (BArray26.get8 p 10 `&` W8.of_int 7).

lemma gub_canonical_byte p i : 0 <= i < 26 =>
  BArray26.get8 (gub_canonical p) i =
    if i = 10 then BArray26.get8 p 10 `&` W8.of_int 7 else BArray26.get8 p i.
proof. move=> hi; rewrite /gub_canonical BArray26.get_set_if; smt(). qed.

lemma gub_canonical_outside p i : 0 <= i < 26 => i <> 10 =>
  BArray26.get8 (gub_canonical p) i = BArray26.get8 p i.
proof. by move=> hi hn; rewrite gub_canonical_byte 1:hi hn. qed.

lemma gub_canonical_byte10 p :
  BArray26.get8 (gub_canonical p) 10 = BArray26.get8 p 10 `&` W8.of_int 7.
proof. by rewrite gub_canonical_byte. qed.

lemma gub_canonical_byte10_range p :
  0 <= W8.to_uint (BArray26.get8 (gub_canonical p) 10) < 8.
proof.
  rewrite gub_canonical_byte10 (W8.to_uint_and_mod 3) //=.
  exact (modz_cmp (W8.to_uint (BArray26.get8 p 10)) 8).
qed.

lemma gub_canonical_idempotent p : gub_canonical (gub_canonical p) = gub_canonical p.
proof.
  apply BArray26.ext_eq => i hi.
  rewrite !gub_canonical_byte //=.
  case (i = 10) => hi10 /=; last trivial.
  by rewrite -W8.andwA W8.andwK.
qed.

lemma gub_mask19_highbyte (a b c : W8.t) :
  ((zeroextu64 a `|` (zeroextu64 b `<<<` 8)) `|`
    (zeroextu64 (c `&` W8.of_int 7) `<<<` 16)) `&` W64.of_int 524287 =
  ((zeroextu64 a `|` (zeroextu64 b `<<<` 8)) `|`
    (zeroextu64 c `<<<` 16)) `&` W64.of_int 524287.
proof.
  have h7 : W8.of_int 7 = W8.masklsb 3 by trivial.
  have h19 : W64.of_int 524287 = W64.masklsb 19 by trivial.
  rewrite h7 h19; apply W64.wordP => i hi.
  rewrite !W64.andwE !W64.orwE !W64.shlwE !W8u8.zeroextu64_bit
    W8.andwE !W64.masklsbE W8.masklsbE /=.
  smt().
qed.

lemma gub_cdt_low p : cdt_lo_input (gub_canonical p) = cdt_lo_input p.
proof.
  by rewrite /cdt_lo_input /le8_word /le6_word /le3_word /byte_word
    !gub_canonical_outside.
qed.

lemma gub_cdt_high p : cdt_hi_input (gub_canonical p) = cdt_hi_input p.
proof.
  rewrite /cdt_hi_input /le3_word /byte_word !gub_canonical_byte //=.
  by rewrite gub_mask19_highbyte.
qed.

lemma gub_rejection p : le6_word (gub_canonical p) 11 = le6_word p 11.
proof. by rewrite /le6_word /le3_word /byte_word !gub_canonical_outside. qed.

lemma gub_noise_low p : le6_word (gub_canonical p) 17 = le6_word p 17.
proof. by rewrite /le6_word /le3_word /byte_word !gub_canonical_outside. qed.

lemma gub_noise_high p : le3_word (gub_canonical p) 23 = le3_word p 23.
proof. by rewrite /le3_word /byte_word !gub_canonical_outside. qed.

lemma gub_sigma_from_cdt p x :
  sigma_from_cdt (gub_canonical p) x = sigma_from_cdt p x.
proof. by rewrite /sigma_from_cdt gub_rejection gub_noise_low gub_noise_high. qed.

lemma gub_sigma76_spec p : sigma76_spec (gub_canonical p) = sigma76_spec p.
proof. by rewrite /sigma76_spec gub_cdt_low gub_cdt_high gub_sigma_from_cdt. qed.

lemma gub_sigma76_regs_total (p : BArray26.t) :
  phoare [SamplerTarget.M.__sample_gauss_sigma76_regs : randp = gub_canonical p ==>
    res = sigma76_spec p] = 1%r.
proof.
  by conseq (sigma76_regs_total_correct (gub_canonical p)) => />;
    rewrite gub_sigma76_spec.
qed.

(* Each little-endian field determines all bytes it contains. *)
lemma gub_le3_byte p offset i : 0 <= i < 3 =>
  le3_word p offset \bits8 i = BArray26.get8 p (offset+i).
proof.
  move=> hi; apply W8.wordP => j hj.
  rewrite W8u8.bits8iE 1:hj /le3_word /byte_word
    !W64.orwE !W64.shlwE !W8u8.zeroextu64_bit /=.
  smt().
qed.

lemma gub_le6_byte p offset i : 0 <= i < 6 =>
  le6_word p offset \bits8 i = BArray26.get8 p (offset+i).
proof.
  move=> hi; apply W8.wordP => j hj.
  rewrite W8u8.bits8iE 1:hj /le6_word /le3_word /byte_word
    !W64.orwE !W64.shlwE !W8u8.zeroextu64_bit /=.
  smt().
qed.

lemma gub_le8_byte p offset i : 0 <= i < 8 =>
  le8_word p offset \bits8 i = BArray26.get8 p (offset+i).
proof.
  move=> hi; apply W8.wordP => j hj.
  rewrite W8u8.bits8iE 1:hj /le8_word /le6_word /le3_word /byte_word
    !W64.orwE !W64.shlwE !W8u8.zeroextu64_bit /=.
  smt().
qed.

lemma gub_fields_injective (p q : BArray26.t) :
  cdt_lo_input p = cdt_lo_input q =>
  le3_word p 8 = le3_word q 8 =>
  le6_word p 11 = le6_word q 11 =>
  le6_word p 17 = le6_word q 17 =>
  le3_word p 23 = le3_word q 23 => p = q.
proof.
  move=> h0 h8 h11 h17 h23; rewrite /cdt_lo_input in h0.
  apply BArray26.ext_eq => i hi.
  case (i < 8) => hfirst.
  + have /= h := congr1 (fun (w : W64.t) => w \bits8 i) _ _ h0.
    by move: h; rewrite !gub_le8_byte 1..2:/# /=.
  case (i < 11) => hsecond.
  + have /= h := congr1 (fun (w : W64.t) => w \bits8 (i-8)) _ _ h8.
    move: h; rewrite !gub_le3_byte 1..2:/# /=; smt().
  case (i < 17) => hthird.
  + have /= h := congr1 (fun (w : W64.t) => w \bits8 (i-11)) _ _ h11.
    move: h; rewrite !gub_le6_byte 1..2:/# /=; smt().
  case (i < 23) => hfourth.
  + have /= h := congr1 (fun (w : W64.t) => w \bits8 (i-17)) _ _ h17.
    move: h; rewrite !gub_le6_byte 1..2:/# /=; smt().
  have /= h := congr1 (fun (w : W64.t) => w \bits8 (i-23)) _ _ h23.
  move: h; rewrite !gub_le3_byte 1..2:/# /=; smt().
qed.

lemma gub_cdt_word p :
  le3_word (gub_canonical p) 8 = le3_word p 8 `&` W64.masklsb 19.
proof.
  rewrite /le3_word /byte_word !gub_canonical_byte //=.
  have h7 : W8.of_int 7 = W8.masklsb 3 by trivial.
  rewrite h7; apply W64.wordP => i hi.
  rewrite !W64.andwE !W64.orwE !W64.shlwE !W8u8.zeroextu64_bit
    W8.andwE W64.masklsbE W8.masklsbE /=.
  smt().
qed.

lemma gub_cdt_high_range p : 0 <= W32.to_uint (cdt_hi_input p) < 524288.
proof.
  have hm := modz_cmp (W64.to_uint (le3_word p 8)) 524288.
  rewrite /cdt_hi_input W2u32.to_uint_truncateu32
    (W64.to_uint_and_mod 19) //= modz_small; smt().
qed.

lemma gub_cdt_high_word p :
  W64.of_int (W32.to_uint (cdt_hi_input p)) = le3_word (gub_canonical p) 8.
proof.
  have hm := modz_cmp (W64.to_uint (le3_word p 8)) 524288.
  have hw : 0 <= W64.to_uint (le3_word p 8 `&` W64.masklsb 19) < 524288.
  + by rewrite (W64.to_uint_and_mod 19) //=.
  rewrite gub_cdt_word /cdt_hi_input W2u32.to_uint_truncateu32 /=.
  by rewrite modz_small 1:/# W64.to_uintK.
qed.

op gub_decoded_cdt (p : BArray26.t) : int =
  W64.to_uint (cdt_lo_input p) + 18446744073709551616 * W32.to_uint (cdt_hi_input p).

lemma gub_decoded_cdt_range p : 0 <= gub_decoded_cdt p < cdt83_modulus.
proof.
  have /= hlo := W64.to_uint_cmp (cdt_lo_input p).
  have hhi := gub_cdt_high_range p.
  rewrite /gub_decoded_cdt /cdt83_modulus /=; smt().
qed.

lemma gub_decoded_cdt_split p :
  gub_decoded_cdt p %% 18446744073709551616 = W64.to_uint (cdt_lo_input p) /\
  gub_decoded_cdt p %/ 18446744073709551616 = W32.to_uint (cdt_hi_input p).
proof.
  have /= hlo := W64.to_uint_cmp (cdt_lo_input p).
  have hd := divz_eq (gub_decoded_cdt p) 18446744073709551616.
  have hm := modz_cmp (gub_decoded_cdt p) 18446744073709551616.
  rewrite /gub_decoded_cdt in hd.
  rewrite /gub_decoded_cdt in hm.
  rewrite /gub_decoded_cdt; smt().
qed.

lemma gub_decoded_noise p :
  0 <= sr_noise p < sr_noise_modulus /\
  sr_noise p %% sr_scale = W64.to_uint (le6_word p 17) /\
  sr_noise p %/ sr_scale = W64.to_uint (le3_word p 23).
proof.
  have hlo := sigma_le6_bound p 17.
  have hhi := sigma_le3_bound p 23.
  have hd := divz_eq (sr_noise p) sr_scale.
  have hm := modz_cmp (sr_noise p) sr_scale.
  rewrite /sr_noise /sr_scale in hd.
  rewrite /sr_noise /sr_scale in hm.
  rewrite /sr_noise /sr_scale /sr_noise_modulus; smt().
qed.

lemma gub_candidate_reconstruct (p base : BArray26.t) :
  gub_canonical p = gr_candidate_patch base
    (W64.to_uint (cdt_lo_input p) + 18446744073709551616 * W32.to_uint (cdt_hi_input p))
    (sr_noise p) (W64.to_uint (le6_word p 11)).
proof.
  rewrite -/(gub_decoded_cdt p); apply eq_sym.
  have hu := gub_decoded_cdt_range p.
  have [hulo huhi] := gub_decoded_cdt_split p.
  have [hy [hylo hyhi]] := gub_decoded_noise p.
  have hv := sigma_le6_bound p 11.
  apply gub_fields_injective.
  + rewrite /gr_candidate_patch sigma_rejection48_patch_cdt_low
      sigma_noise72_patch_cdt_low sj_cdt83_patch_low gub_cdt_low.
    apply W64.to_uint_eq; by rewrite W64.of_uintK /= hulo.
  + have hkeep : le3_word (gr_candidate_patch base (gub_decoded_cdt p)
        (sr_noise p) (W64.to_uint (le6_word p 11))) 8 =
        le3_word (sj_cdt83_patch base (gub_decoded_cdt p)) 8.
    - rewrite /gr_candidate_patch /le3_word /byte_word
        !sigma_rejection48_patch_byte //=.
      by rewrite !sigma_noise72_patch_byte //=.
    by rewrite hkeep (sj_cdt83_patch_high_word base (gub_decoded_cdt p) hu)
      huhi gub_cdt_high_word.
  + by rewrite /gr_candidate_patch (sigma_rejection48_patch_decode _ _ hv)
      W64.to_uintK gub_rejection.
  + rewrite /gr_candidate_patch sigma_rejection48_patch_noise_low gub_noise_low.
    apply W64.to_uint_eq; by rewrite sigma_noise72_patch_low hylo.
  rewrite /gr_candidate_patch sigma_rejection48_patch_noise_high gub_noise_high.
  apply W64.to_uint_eq; by rewrite sigma_noise72_patch_high 1:hy hyhi.
qed.
