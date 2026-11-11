require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import SamplerTarget GaussianConsumerSpec SigmaCorrectness FixedPointCorrectness.
import SLH64.

lemma gauss_mask_bit (w : W64.t) :
  0 <= W64.to_uint (w `&` W64.one) <= 1.
proof.
  have -> : W64.one = W64.of_int (2^1 - 1) by done.
  rewrite W64.to_uint_and_mod 1:// /=.
  smt(modz_cmp).
qed.

(* This bound depends only on the final mask in the actual procedure, and
   therefore does not assume the desired correctness of its CDT call. *)
lemma gauss_sigma_accept_bit :
  hoare [SamplerTarget.M.__sample_gauss_sigma76_regs : true
    ==> 0 <= W64.to_uint res.`4 <= 1].
proof.
  proc.
  wp; call (_ : true ==> true); first by auto.
  wp; call (_ : true ==> true); first by auto.
  wp; call (_ : true ==> true); first by auto.
  wp; skip; auto => />.
  move=> &hr result result0; smt(gauss_mask_bit).
qed.

lemma gauss_frame_set (before after : BArray4096.t) (n i : int) (v : W64.t) :
  gauss_output_frame before after n => i < n =>
  gauss_output_frame before (BArray4096.set64 after i v) n.
proof.
  move=> hframe hi; rewrite /gauss_output_frame => j hj.
  rewrite BArray4096.get_set64E_neq 1:/#.
  exact (hframe j hj).
qed.

lemma gauss_count_get (p : BArray8.t) (n : W64.t) :
  BArray8.get64 (BArray8.set64 p 0 n) 0 = n.
proof. by rewrite BArray8.get_set64E_eq. qed.

lemma gauss_counter_add (c a : W64.t) :
  W64.to_uint c <= 512 => 0 <= W64.to_uint a <= 1 =>
  W64.to_uint (c + a) = W64.to_uint c + W64.to_uint a.
proof.
  move=> hc ha; rewrite W64.to_uintD_small 1:/#; trivial.
qed.

lemma gauss_bytes_subtract (b : W64.t) :
  26 <= W64.to_uint b =>
  W64.to_uint (b - W64.of_int 26) = W64.to_uint b - 26.
proof.
  move=> hb; rewrite W64.to_uintB.
  + by rewrite W64.uleE W64.of_uintK /=.
  by rewrite W64.of_uintK /=.
qed.

lemma sample_gauss_count_bound (n b : int) (r : BArray4096.t) :
  hoare [SamplerTarget.M._sample_gauss :
    gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192 /\ rp = r
    ==>
    0 <= W64.to_uint (BArray8.get64 res.`3 0) <= n /\
    26 * W64.to_uint (BArray8.get64 res.`3 0) <= b /\
    gauss_output_frame r res.`1 n].
proof.
  proc; wp.
  while (coefcnt = scoefcnt /\ len = slen /\
    0 <= W64.to_uint scoefcnt <= W64.to_uint slen /\
    W64.to_uint slen <= n /\ n <= 512 /\
    0 <= W64.to_uint sbytecnt <= b /\ b <= 8192 /\
    W64.to_uint sbytecnt + 26 * W64.to_uint scoefcnt <= b /\
    gauss_output_frame r srp n).
  + wp; sp 1; if.
    - by auto => />; smt().
    wp; call gauss_sigma_accept_bit.
    while (true).
    - by auto.
    auto => />.
    move=> &hr hc0 hcl hln hn hb0 hbb hb hbnd hframe hloop hbytes k hk result ha0 ha1.
    rewrite W64.ultE in hloop.
    rewrite W64.ultE W64.of_uintK /= in hbytes.
    rewrite /protect_64 gauss_counter_add 1:/# 1:/#
      gauss_bytes_subtract 1:/#.
    rewrite /protect_ptr.
    have hnew := gauss_frame_set r srp{hr} n
      (W64.to_uint scoefcnt{hr}) result.`1 hframe.
    smt().
  auto => />.
  rewrite /gauss_output_frame.
  smt().
qed.

lemma sample_gauss_jazz_count_bound (n b : int) (r : BArray4096.t) :
  hoare [SamplerTarget.M.sample_gauss_jazz :
    gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192 /\ rp = r
    ==>
    0 <= W64.to_uint (BArray8.get64 res.`3 0) <= n /\
    26 * W64.to_uint (BArray8.get64 res.`3 0) <= b /\
    gauss_output_frame r res.`1 n].
proof.
  proc; call (sample_gauss_count_bound n b r); wp; skip; auto => />.
qed.

lemma gauss_mask48 (w : W64.t) :
  0 <= W64.to_uint (w `&` W64.of_int 281474976710655) < 281474976710656.
proof.
  have -> : W64.of_int 281474976710655 = W64.of_int (2^48 - 1) by done.
  rewrite W64.to_uint_and_mod 1:// /=.
  smt(modz_cmp).
qed.

lemma sample_gauss_normalized :
  hoare [SamplerTarget.M._sample_gauss : true
    ==> 0 <= W64.to_uint (BArray16.get64 res.`2 0) < 281474976710656].
proof.
  proc; wp.
  while (true); first by auto.
  auto => />.
  move=> c l s h; smt(gauss_mask48).
qed.

lemma sample_gauss_jazz_normalized :
  hoare [SamplerTarget.M.sample_gauss_jazz : true
    ==> 0 <= W64.to_uint (BArray16.get64 res.`2 0) < 281474976710656].
proof. proc; call sample_gauss_normalized; wp; skip; auto. qed.

lemma gauss_counts_encode (n b : int) :
  0 <= n <= 512 => 0 <= b <= 8192 =>
  gauss_requested (W64.of_int (b * 4294967296 + n)) = n /\
  gauss_available (W64.of_int (b * 4294967296 + n)) = b.
proof.
  move=> hn hb.
  rewrite /gauss_requested /gauss_available.
  have -> : W64.of_int 4294967295 = W64.of_int (2^32 - 1) by done.
  rewrite W64.to_uint_and_mod 1:// W64.to_uint_shr 1:// W64.of_uintK /=.
  have hm : (b * 4294967296 + n) %% 18446744073709551616 =
    b * 4294967296 + n by apply modz_small; smt().
  rewrite hm.
  split.
  + rewrite modzMDl; apply modz_small; smt().
  apply (divz_eqP _ _ b); smt().
qed.

(* A finite byte budget suffices for termination even if every attempt is
   rejected. The separate leaf totality premise concerns one fixed-size
   attempt, not this consumer or an unbounded SHAKE refill stream. *)
lemma sample_gauss_lossless_from_attempt :
  islossless SamplerTarget.M.__sample_gauss_sigma76_regs =>
  islossless SamplerTarget.M._sample_gauss.
proof.
  move=> hattempt.
  proc; wp.
  while (coefcnt = scoefcnt /\ len = slen)
    (if coefcnt \ult len then W64.to_uint sbytecnt + 1 else 0).
  + move=> z; wp; sp 1; if.
    - auto => />; smt(W64.to_uint_cmp).
    wp; call hattempt.
    while (0 <= k <= 26) (26 - k).
    - by move=> t; auto => />; smt().
    auto => />.
    move=> &hr hloop hbytes k.
    rewrite W64.ultE W64.of_uintK /= in hbytes.
    rewrite /protect_64 gauss_bytes_subtract 1:/#.
    smt().
  auto => />.
  smt(W64.to_uint_cmp).
qed.

lemma gauss_cdt_lossless : islossless SamplerTarget.M._sample_gauss83.
proof.
  proc.
  while (W64.to_uint i <= 166) (166 - W64.to_uint i).
  + move=> z; auto => /> &hr hi hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt().
  while (W64.to_uint i <= 76) (76 - W64.to_uint i).
  + move=> z; auto => /> &hr hi hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt().
  auto => />; smt(W64.ultE W64.of_uintK W64.to_uint_cmp).
qed.

lemma gauss_sigma_lossless :
  islossless SamplerTarget.M.__sample_gauss_sigma76_regs.
proof.
  proc; wp; call approx_exp_lossless.
  wp; call square_array_lossless.
  wp; call gauss_cdt_lossless.
  wp; skip; auto.
qed.

lemma sample_gauss_lossless : islossless SamplerTarget.M._sample_gauss.
proof. exact (sample_gauss_lossless_from_attempt gauss_sigma_lossless). qed.

lemma sample_gauss_jazz_lossless : islossless SamplerTarget.M.sample_gauss_jazz.
proof. proc; call sample_gauss_lossless; wp; skip; auto. qed.

lemma sample_gauss_jazz_bounded_total (n b : int) (r : BArray4096.t) :
  phoare [SamplerTarget.M.sample_gauss_jazz :
    gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192 /\ rp = r
    ==>
    0 <= W64.to_uint (BArray8.get64 res.`3 0) <= n /\
    26 * W64.to_uint (BArray8.get64 res.`3 0) <= b /\
    gauss_output_frame r res.`1 n] = 1%r.
proof.
  by conseq sample_gauss_jazz_lossless (sample_gauss_jazz_count_bound n b r).
qed.

lemma sample_gauss_jazz_normalized_total :
  phoare [SamplerTarget.M.sample_gauss_jazz : true
    ==> 0 <= W64.to_uint (BArray16.get64 res.`2 0) < 281474976710656] = 1%r.
proof. by conseq sample_gauss_jazz_lossless sample_gauss_jazz_normalized. qed.
