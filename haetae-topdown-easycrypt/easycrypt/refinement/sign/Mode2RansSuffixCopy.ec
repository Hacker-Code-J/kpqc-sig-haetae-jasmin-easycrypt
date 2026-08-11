require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import HbzFullEncodeTarget Mode2HbzCodecSpec.

theory Mode2RansSuffixCopy.

import Mode2HbzCodecSpec.

module Copy = HbzFullEncodeTarget.M.

op slice_eq
    (enc out : BArray2048.t) (off n : int) : bool =
  forall j, 0 <= j < n =>
    BArray2048.get8 out j = BArray2048.get8 enc (off + j).

op suffix_frame
    (before after : BArray2048.t) (start : int) : bool =
  forall j, start <= j < mode2_hbz_capacity =>
    BArray2048.get8 after j = BArray2048.get8 before j.

lemma slice_eq_zero enc out off :
  slice_eq enc out off 0.
proof. rewrite /slice_eq; smt(). qed.

lemma suffix_frame_refl bytes start :
  suffix_frame bytes bytes start.
proof. rewrite /suffix_frame; trivial. qed.

lemma slice_eq_extend enc out off n :
  0 <= n < mode2_hbz_capacity =>
  0 <= off =>
  off + n < mode2_hbz_capacity =>
  slice_eq enc out off n =>
  slice_eq enc
    (BArray2048.set8 out n (BArray2048.get8 enc (off + n)))
    off (n + 1).
proof.
move=> hn hoff hidx hs.
rewrite /slice_eq => j hj.
rewrite BArray2048.get_setE 1:/#.
case (j = n) => heq.
+ by subst j.
+ apply hs; smt().
qed.

lemma suffix_frame_advance_set before after start value :
  0 <= start < mode2_hbz_capacity =>
  suffix_frame before after start =>
  suffix_frame before (BArray2048.set8 after start value) (start + 1).
proof.
move=> hstart hf.
rewrite /suffix_frame => j hj.
rewrite BArray2048.get_setE 1:/# ifF 1:/#.
apply hf; smt().
qed.

lemma copy_guard_exit i n :
  0 <= W64.to_uint i <= n =>
  0 <= n < W64.modulus =>
  ! (i \ult W64.of_int n) =>
  W64.to_uint i = n.
proof.
move=> hi hn hguard.
move: hguard.
rewrite W64.ultE W64.of_uintK modz_small 1:/#.
smt().
qed.

lemma copy_index_no_wrap off i n :
  0 <= off =>
  0 <= W64.to_uint i < n =>
  off + n <= mode2_hbz_capacity =>
  W64.to_uint (W64.of_int off + i) = off + W64.to_uint i.
proof.
move=> hoff hi hcap.
rewrite W64.to_uintD_small.
+ rewrite W64.to_uint_small 1:/#.
  rewrite /mode2_hbz_capacity in hcap.
  smt(W64.to_uint_cmp).
rewrite W64.to_uint_small 1:/#.
trivial.
qed.

lemma copy_encoded_suffix_correct
    (out0 enc0 : BArray2048.t) (off0 n : int) :
  hoare [Copy.__copy_encoded_suffix :
    outp = out0 /\ encp = enc0 /\
    off = W64.of_int off0 /\ size = W64.of_int n /\
    0 <= off0 /\ 0 <= n /\
    off0 + n <= mode2_hbz_capacity
    ==>
    slice_eq enc0 res off0 n /\ suffix_frame out0 res n].
proof.
proc.
while
  (encp = enc0 /\ off = W64.of_int off0 /\
   size = W64.of_int n /\
   0 <= off0 /\ 0 <= n /\
   off0 + n <= mode2_hbz_capacity /\
   0 <= W64.to_uint i <= n /\
   slice_eq enc0 outp off0 (W64.to_uint i) /\
   suffix_frame out0 outp (W64.to_uint i)).
+ auto => /> &hr hoff hn hcap hi0 hile hs hf hguard.
  have hilt : W64.to_uint i{hr} < n.
  + move: hguard.
    rewrite W64.ultE W64.of_uintK modz_small 1:/#.
    smt().
  have hidx := copy_index_no_wrap off0 i{hr} n hoff _ hcap.
  + smt().
  have hinext :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    rewrite /mode2_hbz_capacity in hcap.
    smt(W64.to_uint_cmp).
  rewrite hidx hinext.
  split; first smt().
  split.
  + apply slice_eq_extend; first smt().
    * exact hoff.
    * smt().
    * exact hs.
  + apply suffix_frame_advance_set; first smt().
    exact hf.
auto => /> hoff hn hcap.
split.
+ exact (slice_eq_zero enc0 out0 off0).
move=> i out hguard hi0 hile hs hf.
  have hieq : W64.to_uint i = n.
  + apply (copy_guard_exit i n); first smt().
    * rewrite /mode2_hbz_capacity in hcap.
      smt().
    * exact hguard.
  rewrite -hieq.
  split; first exact hs.
  exact hf.
qed.

lemma copy_encoded_suffix_preconditions_satisfiable :
  0 <= 1024 /\ 0 <= 8 /\
  1024 + 8 <= mode2_hbz_capacity.
proof. by rewrite /mode2_hbz_capacity. qed.

end Mode2RansSuffixCopy.
