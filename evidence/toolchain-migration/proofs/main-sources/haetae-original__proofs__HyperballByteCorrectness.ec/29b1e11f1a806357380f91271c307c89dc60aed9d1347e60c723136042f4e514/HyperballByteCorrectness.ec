require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import ApiTarget BArray1 BArray64 BArray200 Array25 SHAKEBlockSpec
  SHAKEBlockCorrectness SHAKEStreamSpec SHAKESeedInitCorrectness.

theory HyperballByteCorrectness.
module Signer = ApiTarget.M(ApiTarget.Syscall).
import SHAKEStreamSpec SHAKEBlockSpec.Word.

lemma hyperball_shift_zero (w : W64.t) : w `<<` W8.zero = w.
proof.
apply W64.wordP => bit hbit.
by rewrite /(`<<`) W8.to_uint0 W64.shlwE hbit /=.
qed.

lemma hyperball_nonce_first seed nonce :
  BArray200.set64 (shake_seed_prefix seed 64) 8
    (BArray200.get64 (shake_seed_prefix seed 64) 8 `^`
      zeroextu64 (truncateu8 nonce)) = shake_nonce_prefix seed nonce 1.
proof.
have h := shake_nonce_prefix_step seed nonce 0 _; first trivial.
rewrite /= shake_nonce_prefix0 SHAKEBlockSpec.drop_bytes0
  shake_absorb_byte_word 1:// /= in h.
rewrite hyperball_shift_zero in h.
exact h.
qed.

lemma hyperball_nonce_second seed nonce :
  BArray200.set64 (shake_nonce_prefix seed nonce 1) 8
    (BArray200.get64 (shake_nonce_prefix seed nonce 1) 8 `^`
      (zeroextu64 (truncateu8 (nonce `>>` W8.of_int 8)) `<<` W8.of_int 8)) =
    shake_nonce_prefix seed nonce 2.
proof.
have h := shake_nonce_prefix_step seed nonce 1 _; first trivial.
rewrite /= SHAKEBlockSpec.drop_bytes_shrw 1:// shake_absorb_byte_word 1:// /= in h.
by move: h; rewrite /(`>>`) W8.of_uintK /=.
qed.

lemma hyperball_first_state_byte (state : BArray200.t) :
  truncateu8 (BArray200.get64 state 0) =
    (word_state_of_barray state).[0] \bits8 0.
proof.
have hbyte := SHAKEBlockSpec.rate_lane_byte_get8 state 0 0 _ _;
  first 2 trivial.
rewrite /SHAKEBlockSpec.rate_lane_byte SHAKEBlockSpec.drop_bytes0 /= in hbyte.
have hword := shake_state_byte state 0 _; first trivial.
rewrite /= in hword.
by rewrite hbyte hword.
qed.

(* This is the actual separate byte helper used after the Gaussian calls.
   Its initial state is cleared by the production initializer, and the two
   straight-line nonce writes absorb only the same low 16 bits as seed64. *)
lemma hyperball_b_raw_correct (seed0 : BArray64.t) (nonce0 : W64.t) :
  hoare [Signer._sf_hyperball_b_raw : seedp = seed0 /\ nonce = nonce0 ==>
    BArray1.get8 res 0 = shake_stream_byte (shake_initial_words seed0 nonce0) 0].
proof.
proc; wp.
call (SHAKEBlockCorrectness.keccakf1600_word_correct (shake_seed_state seed0 nonce0)).
wp.
while (seedp = seed0 /\ nonce = nonce0 /\ 0 <= W64.to_uint i <= 64 /\
       sp_0 = shake_seed_prefix seed0 (W64.to_uint i)).
+ auto => /> &hr hi0 hi64 hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  have hnext : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1 by
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  have hstep := shake_seed_prefix_step seed0 (W64.to_uint i{hr}) _; first smt().
  rewrite W64.to_uintK /shake_absorb_byte in hstep.
  rewrite hnext; smt().
wp; call SHAKESeedInitCorrectness.keccak_init_zero.
auto => />.
move=> state hzero.
split.
+ exact (SHAKESeedInitCorrectness.zero_state_seed_prefix state seed0 hzero).
move=> i hdone hi0 hi64.
have hi : W64.to_uint i = 64 by
  move: hdone; rewrite W64.ultE W64.of_uintK /=; smt().
rewrite hi.
have hpad := shake_pad_nonce_prefix seed0 nonce0.
rewrite -(hyperball_nonce_second seed0 nonce0)
  -(hyperball_nonce_first seed0 nonce0) /shake_pad /= in hpad.
rewrite hpad /=.
move=> result hstate.
rewrite hyperball_first_state_byte hstate.
by rewrite /shake_stream_byte /shake_initial_words /shake_iterate /=
  (iotaSr 0 0) 1:// iota0 /=.
qed.

lemma hyperball_b_raw_ll : islossless Signer._sf_hyperball_b_raw.
proof.
proc; wp; call SHAKEBlockCorrectness.keccakf1600_ll.
wp.
while (W64.to_uint i <= 64) (64 - W64.to_uint i).
+ move=> z; auto => /> &hr hi hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
wp; call SHAKESeedInitCorrectness.keccak_init_ll.
auto => />; smt(W64.to_uint_cmp W64.ultE W64.of_uintK).
qed.

lemma hyperball_b_raw_total_correct (seed0 : BArray64.t) (nonce0 : W64.t) :
  phoare [Signer._sf_hyperball_b_raw : seedp = seed0 /\ nonce = nonce0 ==>
    BArray1.get8 res 0 = shake_stream_byte (shake_initial_words seed0 nonce0) 0] = 1%r.
proof. by conseq hyperball_b_raw_ll (hyperball_b_raw_correct seed0 nonce0). qed.

lemma hyperball_b_raw_array_correct (seed0 : BArray64.t) (nonce0 : W64.t) :
  hoare [Signer._sf_hyperball_b_raw : seedp = seed0 /\ nonce = nonce0 ==>
    res = BArray1.init (fun _ => shake_stream_byte (shake_initial_words seed0 nonce0) 0)].
proof.
conseq (hyperball_b_raw_correct seed0 nonce0) => //.
move=> &hr hpre result hbyte.
apply BArray1.ext_eq => i hi.
have -> : i = 0 by smt().
by rewrite BArray1.initiE 1:// /= hbyte.
qed.

lemma hyperball_b_raw_array_total (seed0 : BArray64.t) (nonce0 : W64.t) :
  phoare [Signer._sf_hyperball_b_raw : seedp = seed0 /\ nonce = nonce0 ==>
    res = BArray1.init (fun _ => shake_stream_byte (shake_initial_words seed0 nonce0) 0)] = 1%r.
proof. by conseq hyperball_b_raw_ll (hyperball_b_raw_array_correct seed0 nonce0). qed.

end HyperballByteCorrectness.
