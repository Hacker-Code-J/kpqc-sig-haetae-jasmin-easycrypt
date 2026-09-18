require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import SamplerTarget FixedPointSpec FixedPointCorrectness SigmaSpec CDTTermination CDTCorrectness.
import SLH64.

lemma mul48_correct (aa bb : W64.t) :
  hoare [SamplerTarget.M.__mul48 : a = aa /\ b = bb
    ==> res = mul48_word aa bb].
proof. proc; wp; skip; auto => />; rewrite /mul48_word /=. qed.

lemma square_regs_correct (a b : W64.t) :
  hoare [SamplerTarget.M.__fixpoint_square_regs : x0 = a /\ x1 = b
    ==> res = square_word a b].
proof.
  proc.
  wp; ecall (mul48_correct x0 x1).
  wp; ecall (mul48_correct x0 x0).
  wp; skip; auto => />; rewrite /square_word /=.
qed.

lemma square_array_correct (r x : BArray16.t) :
  hoare [SamplerTarget.M._fixpoint_square : rp = r /\ xp = x
    ==> let s = square_word (BArray16.get64 x 0) (BArray16.get64 x 1) in
        res = BArray16.set64 (BArray16.set64 r 0 s.`1) 1 s.`2].
proof.
  proc; wp; ecall (square_regs_correct x0 x1).
  wp; skip; auto => />.
qed.

lemma mul48_lossless : islossless SamplerTarget.M.__mul48.
proof. proc; wp; skip; auto. qed.

lemma square_regs_lossless : islossless SamplerTarget.M.__fixpoint_square_regs.
proof. proc; wp; call mul48_lossless; wp; call mul48_lossless; wp; skip; auto. qed.

lemma square_array_lossless : islossless SamplerTarget.M._fixpoint_square.
proof. proc; wp; call square_regs_lossless; wp; skip; auto. qed.

(* A modular composition rule: the only premise is the separate CDT leaf
   contract. It will be discharged by the proved threshold-count theorem. *)
lemma sigma76_from_cdt_contract (p : BArray26.t) (sample : W64.t) :
  hoare [SamplerTarget.M._sample_gauss83 :
    rand_lo = cdt_lo_input p /\ rand_hi = cdt_hi_input p ==> res = sample] =>
  hoare [SamplerTarget.M.__sample_gauss_sigma76_regs : randp = p
    ==> res = sigma_from_cdt p sample].
proof.
  move=> hcdt.
  proc.
  wp; ecall (approx_exp_correct exp_in).
  wp; ecall (square_array_correct sqrp yp).
  wp; call hcdt.
  wp; skip; auto => />.
qed.

lemma sigma76_array_from_cdt_contract
    (r : BArray8.t) (s : BArray16.t) (a : BArray4.t)
    (p : BArray26.t) (sample : W64.t) :
  hoare [SamplerTarget.M._sample_gauss83 :
    rand_lo = cdt_lo_input p /\ rand_hi = cdt_hi_input p ==> res = sample] =>
  hoare [SamplerTarget.M._sample_gauss_sigma76 :
    rp = r /\ sqrp = s /\ acceptedp = a /\ randp = p ==>
    let v = sigma_from_cdt p sample in
    res = (BArray8.set64 r 0 v.`1,
           BArray16.set64 (BArray16.set64 s 0 v.`2) 1 v.`3,
           BArray4.set32 a 0 (truncateu32 v.`4))].
proof.
  move=> hcdt; proc; wp; call (sigma76_from_cdt_contract p sample hcdt).
  wp; skip; auto => />.
qed.

lemma sigma76_jazz_from_cdt_contract
    (r : BArray8.t) (s : BArray16.t) (a : BArray4.t)
    (p : BArray26.t) (sample : W64.t) :
  hoare [SamplerTarget.M._sample_gauss83 :
    rand_lo = cdt_lo_input p /\ rand_hi = cdt_hi_input p ==> res = sample] =>
  hoare [SamplerTarget.M.sample_gauss_sigma76_jazz :
    rp = r /\ sqrp = s /\ acceptedp = a /\ randp = p ==>
    let v = sigma_from_cdt p sample in
    res = (BArray8.set64 r 0 v.`1,
           BArray16.set64 (BArray16.set64 s 0 v.`2) 1 v.`3,
           BArray4.set32 a 0 (truncateu32 v.`4))].
proof.
  move=> hcdt; proc.
  call (sigma76_array_from_cdt_contract r s a p sample hcdt).
  wp; skip; auto => />.
qed.

lemma sigma76_regs_lossless : islossless SamplerTarget.M.__sample_gauss_sigma76_regs.
proof.
  proc; wp; call approx_exp_lossless.
  wp; call square_array_lossless.
  wp; call CDTTermination.sample_gauss83_ll.
  wp; skip; auto.
qed.

lemma sigma76_array_lossless : islossless SamplerTarget.M._sample_gauss_sigma76.
proof. proc; wp; call sigma76_regs_lossless; wp; skip; auto. qed.

lemma sigma76_jazz_lossless : islossless SamplerTarget.M.sample_gauss_sigma76_jazz.
proof. proc; wp; call sigma76_array_lossless; wp; skip; auto. qed.

op sigma76_spec (p : BArray26.t) : W64.t * W64.t * W64.t * W64.t =
  sigma_from_cdt p
    (W64.of_int (cdt_count (cdt_lo_input p) (cdt_hi_input p) 166)).

lemma sigma76_regs_correct (p : BArray26.t) :
  hoare [SamplerTarget.M.__sample_gauss_sigma76_regs : randp = p
    ==> res = sigma76_spec p].
proof.
  by conseq (sigma76_from_cdt_contract p
    (W64.of_int (cdt_count (cdt_lo_input p) (cdt_hi_input p) 166))
    (CDTCorrectness.sample_gauss83_word_correct (cdt_lo_input p) (cdt_hi_input p)))
    => />; rewrite /sigma76_spec.
qed.

lemma sigma76_regs_total_correct (p : BArray26.t) :
  phoare [SamplerTarget.M.__sample_gauss_sigma76_regs : randp = p
    ==> res = sigma76_spec p] = 1%r.
proof. by conseq sigma76_regs_lossless (sigma76_regs_correct p). qed.

lemma sigma76_array_correct
    (r : BArray8.t) (s : BArray16.t) (a : BArray4.t) (p : BArray26.t) :
  hoare [SamplerTarget.M._sample_gauss_sigma76 :
    rp = r /\ sqrp = s /\ acceptedp = a /\ randp = p ==>
    let v = sigma76_spec p in
    res = (BArray8.set64 r 0 v.`1,
           BArray16.set64 (BArray16.set64 s 0 v.`2) 1 v.`3,
           BArray4.set32 a 0 (truncateu32 v.`4))].
proof.
  by conseq (sigma76_array_from_cdt_contract r s a p
    (W64.of_int (cdt_count (cdt_lo_input p) (cdt_hi_input p) 166))
    (CDTCorrectness.sample_gauss83_word_correct (cdt_lo_input p) (cdt_hi_input p)))
    => />; rewrite /sigma76_spec.
qed.

lemma sigma76_jazz_correct
    (r : BArray8.t) (s : BArray16.t) (a : BArray4.t) (p : BArray26.t) :
  hoare [SamplerTarget.M.sample_gauss_sigma76_jazz :
    rp = r /\ sqrp = s /\ acceptedp = a /\ randp = p ==>
    let v = sigma76_spec p in
    res = (BArray8.set64 r 0 v.`1,
           BArray16.set64 (BArray16.set64 s 0 v.`2) 1 v.`3,
           BArray4.set32 a 0 (truncateu32 v.`4))].
proof.
  by conseq (sigma76_jazz_from_cdt_contract r s a p
    (W64.of_int (cdt_count (cdt_lo_input p) (cdt_hi_input p) 166))
    (CDTCorrectness.sample_gauss83_word_correct (cdt_lo_input p) (cdt_hi_input p)))
    => />; rewrite /sigma76_spec.
qed.

lemma sigma76_jazz_total_correct
    (r : BArray8.t) (s : BArray16.t) (a : BArray4.t) (p : BArray26.t) :
  phoare [SamplerTarget.M.sample_gauss_sigma76_jazz :
    rp = r /\ sqrp = s /\ acceptedp = a /\ randp = p ==>
    let v = sigma76_spec p in
    res = (BArray8.set64 r 0 v.`1,
           BArray16.set64 (BArray16.set64 s 0 v.`2) 1 v.`3,
           BArray4.set32 a 0 (truncateu32 v.`4))] = 1%r.
proof. by conseq sigma76_jazz_lossless (sigma76_jazz_correct r s a p). qed.
