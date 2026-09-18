require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import ApiTarget SHAKEBlockSpec.

theory GaussianRefillCorrectness.
module Signer = ApiTarget.M(ApiTarget.Syscall).

op gauss_carry_prefix (before after : BArray8192.t) (source copied : int) : bool =
  forall j, 0 <= j < 8192 =>
    BArray8192.get8 after j =
      if j < copied then BArray8192.get8 before (source + j)
      else BArray8192.get8 before j.

lemma gauss_carry_step before after source i :
  0 <= source => 0 <= i < 8192 => source + i < 8192 =>
  gauss_carry_prefix before after source i =>
  gauss_carry_prefix before
    (BArray8192.set8 after i (BArray8192.get8 after (source + i))) source (i + 1).
proof.
  move=> hs hi hsi hp.
  have hnot : !(source + i < i) by smt().
  have hread := hp (source + i) _; first smt().
  rewrite hnot /= in hread.
  rewrite /gauss_carry_prefix => j hj.
  rewrite BArray8192.get_set_if hread.
  have := hp j hj; smt().
qed.

lemma gauss_carry_index (base i : int) :
  0 <= base => 0 <= i => base + i < 8192 =>
  W64.to_uint (W64.of_int base + W64.of_int i) = base + i.
proof. move=> hb hi hsum; rewrite -W64.of_intD W64.of_uintK /=; apply modz_small; smt(). qed.

lemma gauss_carry_correct (before : BArray8192.t)
    (available signs remaining : int) (has_prefix : bool) :
  hoare [Signer._sample_gauss_N_carry :
    bufp = before /\ bytecnt = W64.of_int available /\ signbytes = W64.of_int signs /\
    off = W64.of_int remaining /\ (firstflag <> W64.zero) = has_prefix /\
    0 <= remaining <= available /\ 0 <= signs /\
    available + (if has_prefix then signs else 0) <= 8192
    ==>
    gauss_carry_prefix before res
      (available + (if has_prefix then signs else 0) - remaining) remaining].
proof.
  proc.
  while (src = W64.of_int (available + (if has_prefix then signs else 0) - remaining) /\
    off = W64.of_int remaining /\ 0 <= remaining <= available /\ 0 <= signs /\
    available + (if has_prefix then signs else 0) <= 8192 /\
    0 <= W64.to_uint i <= remaining /\
    gauss_carry_prefix before bufp
      (available + (if has_prefix then signs else 0) - remaining) (W64.to_uint i)).
  + auto => /> &hr ho0 hob hs hsum hi0 hio hp hguard.
    have ho64 : W64.to_uint (W64.of_int remaining) = remaining by
      rewrite W64.of_uintK /=; apply modz_small; smt().
    move: hguard; rewrite W64.ultE ho64 => hguard.
    have hindex :
      W64.to_uint
        (W64.of_int (available + (if has_prefix then signs else 0) - remaining) + i{hr}) =
      available + (if has_prefix then signs else 0) - remaining + W64.to_uint i{hr}.
    + rewrite -(W64.to_uintK' i{hr}); apply gauss_carry_index; smt().
    rewrite hindex W64.to_uintD_small 1:/# W64.to_uint1.
    split; first smt().
    apply gauss_carry_step; smt().
  sp 1; if; auto => />.
  - move=> &hr ho hb hs hsum hf.
    have hrange : W64.to_uint (W64.of_int remaining) = remaining.
    + rewrite W64.of_uintK /=; apply modz_small; smt().
    split; first by rewrite /gauss_carry_prefix; smt().
    move=> buf0 i0; rewrite W64.ultE hrange; smt().
  - move=> ho hb hs hsum.
    have hrange : W64.to_uint (W64.of_int remaining) = remaining.
    + rewrite W64.of_uintK /=; apply modz_small; smt().
    split; first by rewrite /gauss_carry_prefix; smt().
    move=> buf0 i0; rewrite W64.ultE hrange; smt().
qed.

lemma gauss_carry_lossless : islossless Signer._sample_gauss_N_carry.
proof.
  proc.
  while (W64.to_uint i <= W64.to_uint off) (W64.to_uint off - W64.to_uint i).
  + move=> z; auto => /> &hr hi hguard.
    rewrite W64.ultE in hguard.
    have hoff := W64.to_uint_cmp off{hr}.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    smt(W64.to_uint_cmp).
  sp 1; if; auto => />; smt(W64.to_uint_cmp).
qed.

lemma initial_gaussian_candidate_budget :
  49 * 136 = 6664 /\ 256 %/ 8 = 32 /\ 257 %/ 8 = 32 /\
  (6664 - 32) %/ 26 = 255 /\ (6664 - 32) %% 26 = 2.
proof. trivial. qed.

lemma gauss_carry_total (before : BArray8192.t)
    (available signs remaining : int) (has_prefix : bool) :
  phoare [Signer._sample_gauss_N_carry :
    bufp = before /\ bytecnt = W64.of_int available /\ signbytes = W64.of_int signs /\
    off = W64.of_int remaining /\ (firstflag <> W64.zero) = has_prefix /\
    0 <= remaining <= available /\ 0 <= signs /\
    available + (if has_prefix then signs else 0) <= 8192
    ==>
    gauss_carry_prefix before res
      (available + (if has_prefix then signs else 0) - remaining) remaining] = 1%r.
proof.
  by conseq gauss_carry_lossless
    (gauss_carry_correct before available signs remaining has_prefix).
qed.

(* Compose the established carry and block-serialization contracts. This is a
   finite buffer-layout fact, not a proof of the whole rejection loop. *)
lemma gauss_carry_squeeze_layout before carried after state source remaining :
  0 <= remaining <= 25 =>
  gauss_carry_prefix before carried source remaining =>
  (forall j, 0 <= j < 136 =>
    BArray8192.get8 after (remaining + j) = BArray200.get8 state j) =>
  SHAKEBlockSpec.rate_block_frame carried after remaining 136 =>
  forall j, 0 <= j < 8192 =>
    BArray8192.get8 after j =
      if j < remaining then BArray8192.get8 before (source + j)
      else if j < remaining + 136 then BArray200.get8 state (j - remaining)
      else BArray8192.get8 before j.
proof.
  move=> hr hc hs hf j hj.
  have hcarry := hc j hj.
  case (j < remaining) => hfirst.
  + have hframe := hf j hj _; first smt().
    smt().
  case (j < remaining + 136) => hblock.
  + have hstream := hs (j - remaining) _; first smt().
    smt().
  have hframe := hf j hj _; first smt().
  smt().
qed.

lemma gaussian_refill_candidate_budget remaining :
  0 <= remaining < 26 =>
  136 <= 136 + remaining <= 161 /\
  5 <= (136 + remaining) %/ 26 <= 6 /\
  0 <= (136 + remaining) %% 26 < 26.
proof.
  move=> hr.
  have hd := divz_eq (136 + remaining) 26.
  have hm := modz_cmp (136 + remaining) 26.
  smt().
qed.

end GaussianRefillCorrectness.
