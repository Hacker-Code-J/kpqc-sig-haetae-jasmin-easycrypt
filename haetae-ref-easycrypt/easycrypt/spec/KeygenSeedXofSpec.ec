require import AllCore IntDiv List StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import
  BArray32 BArray128 BArray200
  HAETAE_FIPS202 HAETAE_Keccak1600
  KeygenKeccak1600Spec KeygenShakeStreamSpec.

theory KeygenSeedXofSpec.

op seed_input_bytes (seed : BArray32.t) : int list =
  mkseq (fun i => W8.to_uint (BArray32.get8 seed i)) 32.

op seed_step
    (seed : BArray32.t) (state : BArray200.t) (i : int) : BArray200.t =
  KeygenShakeStreamSpec.absorb_byte
    state (BArray32.get8 seed i) (W64.of_int i).

op seed_absorb
    (state : BArray200.t) (seed : BArray32.t) (count : int) : BArray200.t =
  foldl (seed_step seed) state (iota_ 0 count).

(* This finalizer is deliberately seed-only: the SHAKE256 domain byte is
   byte 32 (lane 4, byte 0), not byte 34 (lane byte 2) as in seed||nonce. *)
op seed_finalize (state : BArray200.t) : BArray200.t =
  KeygenShakeStreamSpec.xor_lane_byte
    (KeygenShakeStreamSpec.xor_lane_byte
      state 4 0 (W8.of_int 31))
    16 7 (W8.of_int 128).

op seed_framing (state : BArray200.t) (seed : BArray32.t) : bool =
  exists initial,
    KeygenShakeStreamSpec.zero_lanes initial /\
    state = seed_finalize (seed_absorb initial seed 32).

op seed_prefix
    (state : BArray200.t) (seed : BArray32.t) (count : int) : bool =
  forall i,
    0 <= i < 200 =>
    BArray200.get8 state i =
      if i < count then BArray32.get8 seed i else W8.zero.

op seed_padded_prefix
    (state : BArray200.t) (seed : BArray32.t) : bool =
  forall i,
    0 <= i < 200 =>
    BArray200.get8 state i =
      if i < 32 then BArray32.get8 seed i
      else if i = 32 then W8.of_int 31
      else if i = 135 then W8.of_int 128
      else W8.zero.

op seed_padded_state (seed : BArray32.t) : int list =
  HAETAE_FIPS202.shake256_absorb_once_short_state
    (seed_input_bytes seed) 32.

op seed_permuted_state (seed : BArray32.t) : int list =
  HAETAE_FIPS202.shake256_absorb_once (seed_input_bytes seed) 32.

op seed_output_bytes (seed : BArray32.t) : int list =
  HAETAE_FIPS202.shake256 (seed_input_bytes seed) 32 128.

op output_state_prefix
    (out : BArray128.t) (state : BArray200.t) (count : int) : bool =
  forall i,
    0 <= i < count =>
    BArray128.get8 out i = BArray200.get8 state i.

op output_matches (out : BArray128.t) (seed : BArray32.t) : bool =
  forall i,
    0 <= i < 128 =>
    W8.to_uint (BArray128.get8 out i) = nth 0 (seed_output_bytes seed) i.

op output_slice_matches
    (out : BArray128.t) (seed : BArray32.t)
    (offset length : int) : bool =
  forall i,
    0 <= i < length =>
    W8.to_uint (BArray128.get8 out (offset + i)) =
      nth 0 (seed_output_bytes seed) (offset + i).

op uniform_seed_slice_matches
    (out : BArray128.t) (seed : BArray32.t) : bool =
  output_slice_matches out seed 0 32.

op eta_seed_slice_matches
    (out : BArray128.t) (seed : BArray32.t) : bool =
  output_slice_matches out seed 32 64.

op key_seed_slice_matches
    (out : BArray128.t) (seed : BArray32.t) : bool =
  output_slice_matches out seed 96 32.

lemma seed_input_bytes_size seed : size (seed_input_bytes seed) = 32.
proof. by rewrite /seed_input_bytes size_mkseq. qed.

lemma seed_input_bytes_nth seed i :
  0 <= i < 32 =>
  nth 0 (seed_input_bytes seed) i = W8.to_uint (BArray32.get8 seed i).
proof. by move=> hi; rewrite /seed_input_bytes nth_mkseq. qed.

lemma seed_absorb0 state seed : seed_absorb state seed 0 = state.
proof. by rewrite /seed_absorb iota0. qed.

lemma seed_absorb_succ state seed count :
  0 <= count =>
  seed_absorb state seed (count + 1) =
    seed_step seed (seed_absorb state seed count) count.
proof.
move=> hcount.
by rewrite /seed_absorb iotaSr 1:// foldl_rcons.
qed.

lemma seed_prefix_step state seed count :
  0 <= count < 32 =>
  seed_prefix state seed count =>
  seed_prefix (seed_step seed state count) seed (count + 1).
proof.
rewrite /seed_prefix.
move=> hcount hprefix i hi.
rewrite /seed_step
        KeygenShakeStreamSpec.absorb_byte_at_int_get8 1:/# 1://.
case (i = count) => heq.
+ subst i.
  rewrite (hprefix count hi) /=.
  have hnext : count < count + 1 by smt().
  by rewrite hnext /=.
have hlt : (i < count + 1) = (i < count) by smt().
rewrite hlt.
exact (hprefix i hi).
qed.

lemma seed_absorb_prefix initial seed count :
  KeygenShakeStreamSpec.zero_lanes initial =>
  0 <= count =>
  count <= 32 =>
  seed_prefix (seed_absorb initial seed count) seed count.
proof.
move=> hzero.
move: count.
apply intind.
+ move=> _.
  rewrite seed_absorb0 /seed_prefix.
  move=> i hi.
  rewrite (_ : !(i < 0)) 1:/# /=.
  exact (KeygenShakeStreamSpec.zero_lanes_get8 initial i hzero hi).
+ move=> count hcount ih hbound.
  rewrite seed_absorb_succ 1://.
  apply seed_prefix_step.
  + smt().
  apply ih.
  smt().
qed.

lemma seed_finalize_prefix state seed :
  seed_prefix state seed 32 =>
  seed_padded_prefix (seed_finalize state) seed.
proof.
move=> hprefix.
rewrite /seed_finalize /seed_padded_prefix.
move=> i hi.
rewrite KeygenShakeStreamSpec.xor_lane_byte_get8 1:/# 1:/# 1://.
rewrite KeygenShakeStreamSpec.xor_lane_byte_get8 1:/# 1:/# 1://.
have hp := hprefix i hi.
case (i = 135) => hfinal.
+ subst i.
  by rewrite hp /=.
case (i = 32) => hdomain_case.
+ subst i.
  by rewrite hp /=.
rewrite hfinal hdomain_case /=.
by rewrite hp.
qed.

lemma seed_framing_padded_prefix state seed :
  seed_framing state seed => seed_padded_prefix state seed.
proof.
rewrite /seed_framing.
move=> [initial [hzero ->]].
apply seed_finalize_prefix.
apply seed_absorb_prefix.
+ exact hzero.
+ smt().
smt().
qed.

lemma seed_padded_prefix_fips_state state seed :
  seed_padded_prefix state seed =>
  KeygenShakeStreamSpec.state_bytes_le state = seed_padded_state seed.
proof.
move=> hprefix.
apply/(eq_from_nth 0).
+ rewrite KeygenShakeStreamSpec.state_bytes_le_size.
  by rewrite /seed_padded_state
             /HAETAE_FIPS202.shake256_absorb_once_short_state
             /HAETAE_FIPS202.fips202_state_bytes size_mkseq.
move=> i.
rewrite KeygenShakeStreamSpec.state_bytes_le_size => hi.
rewrite KeygenShakeStreamSpec.state_bytes_le_nth 1:hi.
rewrite /seed_padded_state
        /HAETAE_FIPS202.shake256_absorb_once_short_state
        /HAETAE_FIPS202.fips202_state_bytes
        nth_mkseq 1:hi
        /HAETAE_FIPS202.shake256_absorb_once_short_block_byte
        /HAETAE_FIPS202.shake256_rate_bytes.
have hp := hprefix i hi.
rewrite /seed_padded_prefix in hp.
rewrite hp.
case (i < 136) => hrate /=.
+ case (0 <= i /\ i < 32) => hinput /=.
  + have hseed : i < 32 by smt().
    rewrite hrate hseed /=.
    apply eq_sym.
    apply seed_input_bytes_nth.
    smt().
  have hnseed : !(i < 32) by smt().
  rewrite hnseed /=.
  case (i = 32) => hdomain.
  + subst i.
    by rewrite /HAETAE_FIPS202.shake256_domain_separator /=.
  case (i = 135) => hfinal.
  + subst i.
    by rewrite /HAETAE_FIPS202.fips202_final_padding_byte /=.
  trivial.
have hnseed : !(i < 32) by smt().
have hdomain : i <> 32 by smt().
have hfinal : i <> 135 by smt().
by rewrite hnseed hdomain hfinal /=.
qed.

lemma seed_framing_fips_state state seed :
  seed_framing state seed =>
  KeygenShakeStreamSpec.state_bytes_le state = seed_padded_state seed.
proof.
move=> hframe.
apply seed_padded_prefix_fips_state.
exact (seed_framing_padded_prefix state seed hframe).
qed.

lemma seed_returned_state_bytes state seed :
  KeygenKeccak1600Spec.state_of_barray state =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (HAETAE_Keccak1600.keccak_lanes_of_bytes (seed_padded_state seed)) =>
  KeygenShakeStreamSpec.state_bytes_le state = seed_permuted_state seed.
proof.
move=> hstate.
rewrite KeygenShakeStreamSpec.state_bytes_le_of_lanes hstate.
rewrite /seed_permuted_state
        /HAETAE_FIPS202.shake256_absorb_once
        /HAETAE_FIPS202.fips202_keccak_f1600
        /HAETAE_Keccak1600.keccak_f1600_bytes.
trivial.
qed.

lemma output_state_prefix_matches out state seed :
  KeygenShakeStreamSpec.state_bytes_le state = seed_permuted_state seed =>
  output_state_prefix out state 128 =>
  output_matches out seed.
proof.
move=> hstate hprefix.
rewrite /seed_permuted_state in hstate.
rewrite /output_state_prefix in hprefix.
rewrite /output_matches /seed_output_bytes
        /HAETAE_FIPS202.shake256 /HAETAE_FIPS202.shake256_squeeze.
move=> i hi.
rewrite nth_mkseq 1:/#.
rewrite -hstate /=.
rewrite (hprefix i hi).
by rewrite KeygenShakeStreamSpec.state_bytes_le_nth 1:/#.
qed.

lemma output_state_prefix0 out state :
  output_state_prefix out state 0.
proof.
rewrite /output_state_prefix.
move=> i hi.
by smt().
qed.

lemma output_state_prefix_set_next out state count :
  0 <= count < 128 =>
  output_state_prefix out state count =>
  output_state_prefix
    (BArray128.set8 out count (BArray200.get8 state count))
    state (count + 1).
proof.
move=> hcount hprefix.
rewrite /output_state_prefix.
move=> i hi.
rewrite BArray128.get_setE 1:/#.
case (i = count) => [-> | hne].
+ by rewrite eq_sym /=.
apply hprefix.
smt().
qed.

lemma output_matches_slice out seed offset length :
  output_matches out seed =>
  0 <= offset =>
  0 <= length =>
  offset + length <= 128 =>
  output_slice_matches out seed offset length.
proof.
rewrite /output_matches /output_slice_matches.
move=> hmatch hoff hlen hcap i hi.
apply hmatch.
smt().
qed.

lemma output_matches_uniform_slice out seed :
  output_matches out seed => uniform_seed_slice_matches out seed.
proof.
move=> hmatch.
apply (output_matches_slice out seed 0 32 hmatch); smt().
qed.

lemma output_matches_eta_slice out seed :
  output_matches out seed => eta_seed_slice_matches out seed.
proof.
move=> hmatch.
apply (output_matches_slice out seed 32 64 hmatch); smt().
qed.

lemma output_matches_key_slice out seed :
  output_matches out seed => key_seed_slice_matches out seed.
proof.
move=> hmatch.
apply (output_matches_slice out seed 96 32 hmatch); smt().
qed.

lemma seed_padding_positions seed :
  nth 0 (seed_padded_state seed) 32 = 31 /\
  nth 0 (seed_padded_state seed) 135 = 128.
proof.
rewrite /seed_padded_state
        /HAETAE_FIPS202.shake256_absorb_once_short_state
        /HAETAE_FIPS202.fips202_state_bytes
        !nth_mkseq 1:/# 1:/# /=.
rewrite /HAETAE_FIPS202.shake256_absorb_once_short_block_byte /=.
by rewrite /HAETAE_FIPS202.shake256_domain_separator
           /HAETAE_FIPS202.fips202_final_padding_byte /=.
qed.

lemma seed_output_bytes_size seed : size (seed_output_bytes seed) = 128.
proof.
rewrite /seed_output_bytes.
by apply HAETAE_FIPS202.shake256_size.
qed.

end KeygenSeedXofSpec.
