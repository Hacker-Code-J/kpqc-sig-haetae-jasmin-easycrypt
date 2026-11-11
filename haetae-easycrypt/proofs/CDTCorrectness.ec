require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import SamplerTarget CDTTermination SamplerConstants ReferenceConstants.
import SLH64.

(* Integer threshold-count specification.  The high limb is implicit and
   constant for the last 90 entries, exactly as in the HAETAE-1.2.0 table. *)
op cdt_low (j : int) : int =
  W64.to_uint (BArray1328.get64 jcdt83_lo j).

op cdt_high (j : int) : int =
  if j < 76 then W32.to_uint (BArray304.get32 jcdt83_hi j)
  else 524287.

op cdt_threshold (j : int) : int = cdt_high j * 18446744073709551616 + cdt_low j.

op cdt_input (lo : W64.t) (hi : W32.t) : int =
  W32.to_uint hi * 18446744073709551616 + W64.to_uint lo.

op cdt_count (lo : W64.t) (hi : W32.t) (n : int) : int =
  count (fun j => cdt_threshold j < cdt_input lo hi) (iota_ 0 n).

lemma cdt_count0 lo hi : cdt_count lo hi 0 = 0.
proof. by rewrite /cdt_count iota0. qed.

lemma cdt_countS lo hi n : 0 <= n =>
  cdt_count lo hi (n + 1) =
  cdt_count lo hi n + b2i (cdt_threshold n < cdt_input lo hi).
proof. by move=> hn; rewrite /cdt_count iotaSr 1:hn -cats1 count_cat /=. qed.

lemma cdt_count_range lo hi n : 0 <= n => 0 <= cdt_count lo hi n <= n.
proof.
  move=> hn; rewrite /cdt_count.
  have := count_ge0 (fun j => cdt_threshold j < cdt_input lo hi) (iota_ 0 n).
  have := count_size (fun j => cdt_threshold j < cdt_input lo hi) (iota_ 0 n).
  rewrite size_iota; smt().
qed.

(* A subtraction of two small high limbs has its sign encoded faithfully
   by bit 63, including the borrow from the full-width low subtraction. *)
lemma cdt_sbb_sign (a b : W64.t) (borrow : bool) :
  0 <= W64.to_uint a < 4294967296 =>
  0 <= W64.to_uint b < 4294967296 =>
  W64.to_uint ((sbb_64 a b borrow).`2 `>>` W8.of_int 63) =
  b2i (W64.to_uint a < W64.to_uint b + b2i borrow).
proof.
  move=> ha hb.
  rewrite W64.subcE /= W64.shr_div W8.of_uintK /= W64.to_uintBb /=.
  case: (W64.to_uint a < W64.to_uint b + b2i borrow) => hc.
  + rewrite /b2i /=.
    rewrite divz_eqP //; smt().
  + rewrite /b2i /=.
    apply divz_small; rewrite /=; smt().
qed.

lemma cdt_borrow_compare (lo rlo : W64.t) (hi rhi : W64.t) :
  0 <= W64.to_uint hi < 4294967296 =>
  0 <= W64.to_uint rhi < 4294967296 =>
  W64.to_uint
    ((sbb_64 hi rhi (sbb_64 lo rlo false).`1).`2 `>>` W8.of_int 63) =
  b2i (W64.to_uint hi * 18446744073709551616 + W64.to_uint lo <
       W64.to_uint rhi * 18446744073709551616 + W64.to_uint rlo).
proof.
  move=> hh hr.
  rewrite cdt_sbb_sign // W64.subcE /W64.borrow_sub /= /b2i.
  have /= := W64.to_uint_cmp lo.
  have /= := W64.to_uint_cmp rlo.
  smt().
qed.

lemma cdt_step_head (rlo : W64.t) (rhi : W32.t) (j : int) : j < 76 =>
  W64.to_uint
    ((sbb_64 (zeroextu64 (BArray304.get32 jcdt83_hi j)) (zeroextu64 rhi)
       (sbb_64 (BArray1328.get64 jcdt83_lo j) rlo false).`1).`2
      `>>` W8.of_int 63) =
  b2i (cdt_threshold j < cdt_input rlo rhi).
proof.
  move=> hj.
  rewrite cdt_borrow_compare.
  + rewrite W2u32.to_uint_zeroextu64; exact: W32.to_uint_cmp.
  + rewrite W2u32.to_uint_zeroextu64; exact: W32.to_uint_cmp.
  by rewrite /cdt_threshold /cdt_high hj /cdt_low /cdt_input
             !W2u32.to_uint_zeroextu64.
qed.

lemma cdt_step_tail (rlo : W64.t) (rhi : W32.t) (j : int) : 76 <= j =>
  W64.to_uint
    ((sbb_64 (W64.of_int 524287) (zeroextu64 rhi)
       (sbb_64 (BArray1328.get64 jcdt83_lo j) rlo false).`1).`2
      `>>` W8.of_int 63) =
  b2i (cdt_threshold j < cdt_input rlo rhi).
proof.
  move=> hj.
  rewrite cdt_borrow_compare.
  + by rewrite W64.of_uintK /=.
  + rewrite W2u32.to_uint_zeroextu64; exact: W32.to_uint_cmp.
  have hj' : !(j < 76) by smt().
  by rewrite /cdt_threshold /cdt_high hj' /cdt_low /cdt_input
             W2u32.to_uint_zeroextu64 W64.of_uintK /=.
qed.

lemma cdt_add_count (r d lo : W64.t) (hi : W32.t) (j : int) :
  0 <= j =>
  r = W64.of_int (cdt_count lo hi j) =>
  W64.to_uint d = b2i (cdt_threshold j < cdt_input lo hi) =>
  r + d = W64.of_int (cdt_count lo hi (j + 1)).
proof.
  move=> hj -> hd.
  by rewrite -(W64.to_uintK d) hd -W64.of_intD -cdt_countS.
qed.

lemma cdt_next_index (i : W64.t) : 0 <= W64.to_uint i < 166 =>
  W64.to_uint (i + W64.of_int 1) = W64.to_uint i + 1.
proof.
  move=> hi; rewrite W64.to_uintD W64.to_uint1 modz_small //; smt().
qed.

(* The implementation contract holds for every 32-bit high word, hence in
   particular for the 19-bit high words used by the 83-bit sampler. *)
lemma sample_gauss83_word_correct (ll : W64.t) (hh : W32.t) :
  hoare [SamplerTarget.M._sample_gauss83 : rand_lo = ll /\ rand_hi = hh
    ==> res = W64.of_int (cdt_count ll hh 166)].
proof.
  proc.
  while (rand_lo = ll /\ rand_hi = hh /\
    rndhi = zeroextu64 hh /\ hip = jcdt83_hi /\ lop = jcdt83_lo /\
    76 <= W64.to_uint i <= 166 /\
    r = W64.of_int (cdt_count ll hh (W64.to_uint i))).
  + auto => /> &m hi0 hi1 hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    rewrite cdt_next_index 1:/#.
    split; first smt().
    apply cdt_add_count => //; first smt().
    by apply cdt_step_tail.
  while (rand_lo = ll /\ rand_hi = hh /\
    rndhi = zeroextu64 hh /\ hip = jcdt83_hi /\ lop = jcdt83_lo /\
    0 <= W64.to_uint i <= 76 /\
    r = W64.of_int (cdt_count ll hh (W64.to_uint i))).
  + auto => /> &m hi0 hi1 hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    rewrite cdt_next_index 1:/#.
    split; first smt().
    apply cdt_add_count => //.
    by apply cdt_step_head.
  auto => />.
  rewrite cdt_count0.
  split; first smt().
  move=> i hguard hi0 hi1.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  split; first smt().
  move=> i' hguard' hi0' hi1'.
  rewrite W64.ultE W64.of_uintK /= in hguard'.
  have -> : W64.to_uint i' = 166 by smt().
  trivial.
qed.

lemma sample_gauss83_correct (ll : W64.t) (hh : W32.t) :
  hoare [SamplerTarget.M._sample_gauss83 : rand_lo = ll /\ rand_hi = hh
    ==> W64.to_uint res = cdt_count ll hh 166 /\ 0 <= W64.to_uint res <= 166].
proof.
  conseq (sample_gauss83_word_correct ll hh) => //.
  move=> &m _ result ->.
  have h := cdt_count_range ll hh 166 _; first smt().
  rewrite W64.to_uint_small 1:/#; exact h.
qed.

lemma sample_gauss83_jazz_word_correct (ll : W64.t) (hh : W32.t) :
  hoare [SamplerTarget.M.sample_gauss83_jazz : rand_lo = ll /\ rand_hi = hh
    ==> res = W64.of_int (cdt_count ll hh 166)].
proof.
  proc; call (sample_gauss83_word_correct ll hh); wp; skip; auto => />.
qed.

lemma sample_gauss83_jazz_correct (ll : W64.t) (hh : W32.t) :
  hoare [SamplerTarget.M.sample_gauss83_jazz : rand_lo = ll /\ rand_hi = hh
    ==> W64.to_uint res = cdt_count ll hh 166 /\ 0 <= W64.to_uint res <= 166].
proof.
  proc; call (sample_gauss83_correct ll hh); wp; skip; auto => />.
qed.

lemma sample_gauss83_total (ll : W64.t) (hh : W32.t) :
  phoare [SamplerTarget.M._sample_gauss83 : rand_lo = ll /\ rand_hi = hh
    ==> W64.to_uint res = cdt_count ll hh 166 /\
        0 <= W64.to_uint res <= 166] = 1%r.
proof. by conseq sample_gauss83_ll (sample_gauss83_correct ll hh). qed.

lemma sample_gauss83_jazz_total (ll : W64.t) (hh : W32.t) :
  phoare [SamplerTarget.M.sample_gauss83_jazz : rand_lo = ll /\ rand_hi = hh
    ==> W64.to_uint res = cdt_count ll hh 166 /\
        0 <= W64.to_uint res <= 166] = 1%r.
proof. by conseq sample_gauss83_jazz_ll (sample_gauss83_jazz_correct ll hh). qed.

(* Boundary certificates use the independently extracted C literal lists. *)
lemma cdt_high_bound (j : int) : 0 <= j < 166 => cdt_high j <= 524287.
proof.
  move=> hj; rewrite /cdt_high.
  case (j < 76) => hj76; last smt().
  rewrite cdt83_hi_matches_reference /reference_cdt83_hi
    BArray304.get32_of_list32 1:reference_cdt83_hi_length 1://.
  have hall : all (fun w => W32.to_uint w <= 524287) reference_cdt83_hi_words.
  + by rewrite /reference_cdt83_hi_words /=.
  rewrite -(all_nthP _ _ W32.zero) in hall.
  apply hall; rewrite reference_cdt83_hi_length; smt().
qed.

lemma cdt_low_below_max (j : int) : 0 <= j < 166 =>
  cdt_low j < 18446744073709551615.
proof.
  move=> hj; rewrite /cdt_low cdt83_lo_matches_reference /reference_cdt83_lo
    BArray1328.get64_of_list64 1:reference_cdt83_lo_length 1://.
  have hall : all (fun w => W64.to_uint w < 18446744073709551615)
    reference_cdt83_lo_words.
  + by rewrite /reference_cdt83_lo_words /=.
  rewrite -(all_nthP _ _ W64.zero) in hall.
  apply hall; by rewrite reference_cdt83_lo_length.
qed.

lemma cdt_threshold_below_max83 (j : int) : 0 <= j < 166 =>
  cdt_threshold j < cdt_input (W64.of_int (-1)) (W32.of_int 524287).
proof.
  move=> hj.
  have hh := cdt_high_bound j hj.
  have hl := cdt_low_below_max j hj.
  rewrite /cdt_threshold /cdt_input !W32.of_uintK !W64.of_uintK /=; smt().
qed.

lemma cdt_count_max83 : cdt_count (W64.of_int (-1)) (W32.of_int 524287) 166 = 166.
proof.
  rewrite /cdt_count count_predT_eq_in.
  + move=> j; rewrite mem_iota /=; move=> hj.
    apply (cdt_threshold_below_max83 j); smt().
  by rewrite size_iota /=.
qed.

lemma sample_gauss83_max83_total :
  phoare [SamplerTarget.M.sample_gauss83_jazz :
    rand_lo = W64.of_int (-1) /\ rand_hi = W32.of_int 524287
    ==> W64.to_uint res = 166] = 1%r.
proof.
  conseq (sample_gauss83_jazz_total (W64.of_int (-1)) (W32.of_int 524287)) => />.
  rewrite cdt_count_max83; smt().
qed.
