require import AllCore IntDiv List StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import
  KeygenSamplerCallersTarget
  KeygenShakeStreamSpec
  HAETAE_FIPS202
  HAETAE_Keccak1600
  KeygenKeccak1600Spec
  TargetKeygenKeccak1600.

theory TargetKeygenShakeStream.

lemma keccak_init_state_zero :
  hoare [KeygenSamplerCallersTarget.M._keccak_init_state :
    true ==> KeygenShakeStreamSpec.zero_lanes res].
proof.
proc.
while (
  (forall lane,
     0 <= lane < W64.to_uint i =>
     BArray200.get64 sp_0 lane = W64.zero) /\
  0 <= W64.to_uint i <= 25).
+ auto => /> &hr hprefix hlo hhi hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  split.
  + move=> lane hlane0 hlane1.
    rewrite BArray200.get_set64E 1:/# 1:/#.
    case (lane = W64.to_uint i{hr}) => [-> | hne].
    + trivial.
    have -> /= : !(W64.to_uint i{hr} = lane) by smt().
    apply hprefix.
    rewrite W64.to_uintD_small 1:/# in hlane1.
    rewrite W64.to_uint1 in hlane1.
    smt().
  rewrite W64.to_uintD_small 1:/#.
  smt(W64.to_uint_cmp).
wp.
skip => &hr _ /=.
split.
+ smt(W64.to_uint_cmp).
move=> i0 state hdone [hprefix hlo hhi].
rewrite /KeygenShakeStreamSpec.zero_lanes.
move=> hlane.
apply hprefix.
rewrite W64.ultE W64.of_uintK /= in hdone.
smt(W64.to_uint_cmp).
qed.

lemma shake128_init_seedbuf_framing
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  hoare [KeygenSamplerCallersTarget.M.__kp_shake128_init_seedbuf :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size
    ==>
    KeygenShakeStreamSpec.shake128_seedbuf_framing
      res seed0 seedoff0 nonce0].
proof.
proc.
wp.
while (
  (exists initial,
     KeygenShakeStreamSpec.zero_lanes initial /\
     (sp_0, n, pos) =
       KeygenShakeStreamSpec.nonce_run
         (KeygenShakeStreamSpec.seed_absorb
            initial seed0 seedoff0 32,
          nonce0, W64.of_int 32)
         k) /\
  0 <= k <= 2).
+ auto => /> &hr initial hzero hrun hk0 hk2 hguard.
  split.
  + exists initial.
    split; first exact hzero.
    rewrite KeygenShakeStreamSpec.nonce_run_succ 1:/#.
    rewrite /KeygenShakeStreamSpec.nonce_step
            /KeygenShakeStreamSpec.absorb_byte /=.
    rewrite -hrun.
    trivial.
  smt().
wp.
while (
  (exists initial,
     KeygenShakeStreamSpec.zero_lanes initial /\
     sp_0 =
       KeygenShakeStreamSpec.seed_absorb
         initial seed0 seedoff0 (W64.to_uint pos)) /\
  n = nonce0 /\
  seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
  0 <= W64.to_uint pos <= 32).
+ auto => /> &hr initial hzero hpos0 hpos32 hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  split.
  + exists initial.
    split; first exact hzero.
    have hnowrap :
      W64.to_uint pos{hr} + W64.to_uint W64.one < W64.modulus.
    + rewrite W64.to_uint1.
      smt(W64.to_uint_cmp).
    rewrite [W64.to_uint (pos{hr} + W64.one)]W64.to_uintD_small.
    + exact hnowrap.
    rewrite KeygenShakeStreamSpec.seed_absorb_succ.
    + exact hpos0.
    rewrite /KeygenShakeStreamSpec.seed_step
            /KeygenShakeStreamSpec.seed_byte64
            /KeygenShakeStreamSpec.absorb_byte /=.
    trivial.
  have hnowrap2 :
    W64.to_uint pos{hr} + W64.to_uint W64.one < W64.modulus.
  + rewrite W64.to_uint1.
    smt(W64.to_uint_cmp).
  rewrite [W64.to_uint (pos{hr} + W64.one)]W64.to_uintD_small.
  + exact hnowrap2.
  smt(W64.to_uint_cmp).
wp.
call keccak_init_state_zero.
auto => /> &hr.
move=> result hzero.
split.
+ exists result.
  split; first exact hzero.
  by rewrite KeygenShakeStreamSpec.seed_absorb0.
move=> pos0 hposdone initial hinitial hpos0 hpos32.
split.
+ exists initial.
  split; first exact hinitial.
  have hpos : W64.to_uint pos0 = 32.
  + rewrite W64.ultE W64.of_uintK /= in hposdone.
    smt(W64.to_uint_cmp).
  have -> : pos0 = W64.of_int 32.
  + by rewrite -(W64.to_uintK' pos0) hpos.
  by rewrite KeygenShakeStreamSpec.nonce_run0.
move=> k0 n0 pos1 sp_01 hkdone initial0 hzero0 hrun hk0 hk2.
have hk : k0 = 2 by smt().
subst k0.
rewrite /KeygenShakeStreamSpec.shake128_seedbuf_framing
        /KeygenShakeStreamSpec.finalize_shake128 /=.
exists initial0.
split; first exact hzero0.
by rewrite -hrun.
qed.

lemma shake128_init_seedbuf_padded_state
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  hoare [KeygenSamplerCallersTarget.M.__kp_shake128_init_seedbuf :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size
    ==>
    KeygenShakeStreamSpec.state_bytes_le res =
      KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0].
proof.
conseq (shake128_init_seedbuf_framing seed0 seedoff0 nonce0).
move=> &hr hpre result hframing.
apply (KeygenShakeStreamSpec.shake128_framing_fips_state
  result seed0 seedoff0 nonce0).
+ smt().
exact hframing.
qed.

lemma shake256_init_seedbuf_framing
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  hoare [KeygenSamplerCallersTarget.M.__kp_shake256_init_seedbuf :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint seedoff0 + 64 <= BArray128.size
    ==>
    KeygenShakeStreamSpec.shake256_seedbuf_framing
      res seed0 seedoff0 nonce0].
proof.
proc.
wp.
while (
  (exists initial,
     KeygenShakeStreamSpec.zero_lanes initial /\
     (sp_0, n, pos) =
       KeygenShakeStreamSpec.nonce_run
         (KeygenShakeStreamSpec.seed_absorb
            initial seed0 seedoff0 64,
          nonce0, W64.of_int 64)
         k) /\
  0 <= k <= 2).
+ auto => /> &hr initial hzero hrun hk0 hk2 hguard.
  split.
  + exists initial.
    split; first exact hzero.
    rewrite KeygenShakeStreamSpec.nonce_run_succ 1:/#.
    rewrite /KeygenShakeStreamSpec.nonce_step
            /KeygenShakeStreamSpec.absorb_byte /=.
    rewrite -hrun.
    trivial.
  smt().
wp.
while (
  (exists initial,
     KeygenShakeStreamSpec.zero_lanes initial /\
     sp_0 =
       KeygenShakeStreamSpec.seed_absorb
         initial seed0 seedoff0 (W64.to_uint pos)) /\
  n = nonce0 /\
  seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
  0 <= W64.to_uint pos <= 64).
+ auto => /> &hr initial hzero hpos0 hpos64 hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  split.
  + exists initial.
    split; first exact hzero.
    have hnowrap :
      W64.to_uint pos{hr} + W64.to_uint W64.one < W64.modulus.
    + rewrite W64.to_uint1.
      smt(W64.to_uint_cmp).
    rewrite [W64.to_uint (pos{hr} + W64.one)]W64.to_uintD_small.
    + exact hnowrap.
    rewrite KeygenShakeStreamSpec.seed_absorb_succ.
    + exact hpos0.
    rewrite /KeygenShakeStreamSpec.seed_step
            /KeygenShakeStreamSpec.seed_byte64
            /KeygenShakeStreamSpec.absorb_byte /=.
    trivial.
  have hnowrap2 :
    W64.to_uint pos{hr} + W64.to_uint W64.one < W64.modulus.
  + rewrite W64.to_uint1.
    smt(W64.to_uint_cmp).
  rewrite [W64.to_uint (pos{hr} + W64.one)]W64.to_uintD_small.
  + exact hnowrap2.
  smt(W64.to_uint_cmp).
wp.
call keccak_init_state_zero.
auto => /> &hr.
move=> result hzero.
split.
+ exists result.
  split; first exact hzero.
  by rewrite KeygenShakeStreamSpec.seed_absorb0.
move=> pos0 hposdone initial hinitial hpos0 hpos64.
split.
+ exists initial.
  split; first exact hinitial.
  have hpos : W64.to_uint pos0 = 64.
  + rewrite W64.ultE W64.of_uintK /= in hposdone.
    smt(W64.to_uint_cmp).
  have -> : pos0 = W64.of_int 64.
  + by rewrite -(W64.to_uintK' pos0) hpos.
  by rewrite KeygenShakeStreamSpec.nonce_run0.
move=> k0 n0 pos1 sp_01 hkdone initial0 hzero0 hrun hk0 hk2.
have hk : k0 = 2 by smt().
subst k0.
rewrite /KeygenShakeStreamSpec.shake256_seedbuf_framing
        /KeygenShakeStreamSpec.finalize_shake256 /=.
exists initial0.
split; first exact hzero0.
by rewrite -hrun.
qed.

lemma shake256_init_seedbuf_padded_state
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  hoare [KeygenSamplerCallersTarget.M.__kp_shake256_init_seedbuf :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint seedoff0 + 64 <= BArray128.size
    ==>
    KeygenShakeStreamSpec.state_bytes_le res =
      KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0].
proof.
conseq (shake256_init_seedbuf_framing seed0 seedoff0 nonce0).
move=> &hr hpre result hframing.
apply (KeygenShakeStreamSpec.shake256_framing_fips_state
  result seed0 seedoff0 nonce0).
+ smt().
exact hframing.
qed.

lemma squeeze128_rate_block
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (state0 : BArray200.t) :
  hoare [KeygenSamplerCallersTarget.M.__poly_sample_squeeze128 :
    outp = out0 /\ outoff = outoff0 /\ sp_0 = state0 /\
    W64.to_uint outoff0 + 168 <= BArray1024.size
    ==>
    KeygenShakeStreamSpec.rate_block_matches
      res.`1 (W64.to_uint outoff0) res.`2 168 /\
    KeygenShakeStreamSpec.rate_block_frame
      out0 res.`1 (W64.to_uint outoff0) 168 /\
    KeygenKeccak1600Spec.state_of_barray res.`2 =
      HAETAE_Keccak1600.keccak_f1600_lanes
        (KeygenKeccak1600Spec.state_of_barray state0)].
proof.
proc.
while (
  KeygenShakeStreamSpec.rate_prefix_matches
    outp (W64.to_uint outoff0) sp_0 (W64.to_uint i) /\
  KeygenShakeStreamSpec.rate_block_frame
    out0 outp (W64.to_uint outoff0) 168 /\
  W64.to_uint idx = W64.to_uint outoff0 + W64.to_uint i /\
  0 <= W64.to_uint i <= 168 /\
  W64.to_uint i %% 8 = 0 /\
  W64.to_uint outoff0 + 168 <= BArray1024.size /\
  KeygenKeccak1600Spec.state_of_barray sp_0 =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (KeygenKeccak1600Spec.state_of_barray state0)).
+ wp.
  while (
    KeygenShakeStreamSpec.rate_prefix_matches
      outp (W64.to_uint outoff0) sp_0
        (W64.to_uint i + W64.to_uint j) /\
    KeygenShakeStreamSpec.rate_block_frame
      out0 outp (W64.to_uint outoff0) 168 /\
    W64.to_uint idx =
      W64.to_uint outoff0 + W64.to_uint i + W64.to_uint j /\
    W64.to_uint lane = W64.to_uint i %/ 8 /\
    t = KeygenShakeStreamSpec.drop_bytes
          (BArray200.get64 sp_0 (W64.to_uint i %/ 8))
          (W64.to_uint j) /\
    0 <= W64.to_uint i < 168 /\
    W64.to_uint i %% 8 = 0 /\
    0 <= W64.to_uint j <= 8 /\
    W64.to_uint outoff0 + 168 <= BArray1024.size /\
    KeygenKeccak1600Spec.state_of_barray sp_0 =
      HAETAE_Keccak1600.keccak_f1600_lanes
        (KeygenKeccak1600Spec.state_of_barray state0)).
  + auto => /> &hr hprefix hframe hidx hlane
                   hi0 hi168 himod hj0 hj8 hcap hperm hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    have hi8 := KeygenShakeStreamSpec.div8_split
                  (W64.to_uint i{hr}) hi0 himod.
    have hoff : 0 <= W64.to_uint outoff0 by smt(W64.to_uint_cmp).
    have hjlt : 0 <= W64.to_uint j{hr} < 8 by smt().
    have hwritecap :
      W64.to_uint outoff0 +
        (W64.to_uint i{hr} + W64.to_uint j{hr}) <
      BArray1024.size by smt().
    have hp := KeygenShakeStreamSpec.rate_prefix_set_cursor
      outp{hr} (W64.to_uint outoff0) sp_0{hr}
      (W64.to_uint i{hr}) (W64.to_uint j{hr})
      hoff hi0 himod hjlt hwritecap hprefix.
    rewrite /KeygenShakeStreamSpec.rate_lane_byte in hp.
    split.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1 hidx.
      have -> :
        W64.to_uint outoff0 + W64.to_uint i{hr} +
          W64.to_uint j{hr} =
        W64.to_uint outoff0 +
          (W64.to_uint i{hr} + W64.to_uint j{hr}) by ring.
      have -> :
        W64.to_uint i{hr} + (W64.to_uint j{hr} + 1) =
        W64.to_uint i{hr} + W64.to_uint j{hr} + 1 by ring.
      exact hp.
    split.
    + rewrite hidx.
      have -> :
        W64.to_uint outoff0 + W64.to_uint i{hr} +
          W64.to_uint j{hr} =
        W64.to_uint outoff0 +
          (W64.to_uint i{hr} + W64.to_uint j{hr}) by ring.
      apply (KeygenShakeStreamSpec.rate_block_frame_set_inside
               out0 outp{hr} (W64.to_uint outoff0) 168
               (W64.to_uint i{hr} + W64.to_uint j{hr})
               (truncateu8
                 (KeygenShakeStreamSpec.drop_bytes
                   (BArray200.get64 sp_0{hr}
                     (W64.to_uint i{hr} %/ 8))
                   (W64.to_uint j{hr})))).
      + exact hoff.
      + smt().
      + exact hcap.
      + exact hframe.
    do split.
    + rewrite W64.to_uintD_small 1:/#.
      rewrite hidx.
      ring.
    + smt().
    + rewrite W64.to_uintD_small 1:/#.
      rewrite KeygenShakeStreamSpec.drop_bytes_succ 1:/#.
      trivial.
    + smt().
    + smt().
  auto => /> &hr hprefix hframe hidx hi0 hi168 himod hcap hperm hguard.
  split.
  + split.
    + rewrite W64.shr_div_le 1:/# /=.
    split.
    + rewrite KeygenShakeStreamSpec.drop_bytes0.
      rewrite W64.shr_div_le 1:/# /=.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    exact hguard.
  move=> idx0 j0 outp0 hjdone hp hf hidx0 hlane hi168' hj0 hj8.
  rewrite W64.ultE W64.of_uintK /= in hjdone.
  have hj : W64.to_uint j0 = 8 by smt(W64.to_uint_cmp).
  have hjword : j0 = W64.of_int 8.
  + by rewrite -(W64.to_uintK' j0) hj.
  subst j0.
  rewrite W64.to_uintD_small 1:/# /=.
  do split.
  + exact hp.
  + rewrite hidx0.
    ring.
  + smt(W64.to_uint_cmp).
  + smt(W64.to_uint_cmp).
  smt().
wp.
call (TargetKeygenKeccak1600.keccakf1600_correct state0).
auto => /> &hr hcap hperm.
split.
+ exact (KeygenShakeStreamSpec.rate_prefix_zero
           (SLH64.protect_ptr out0 W64.zero)
           (W64.to_uint outoff0) hcap).
move=> i0 idx0 outp0 hdone hprefix hframe hidx hi0 hi168 himod.
rewrite /KeygenShakeStreamSpec.rate_block_matches.
have <- : W64.to_uint i0 = 168.
+ rewrite W64.ultE W64.of_uintK /= in hdone.
  smt(W64.to_uint_cmp).
exact hprefix.
qed.

lemma squeeze256_rate_block
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (state0 : BArray200.t) :
  hoare [KeygenSamplerCallersTarget.M.__poly_sample_squeeze256 :
    outp = out0 /\ outoff = outoff0 /\ sp_0 = state0 /\
    W64.to_uint outoff0 + 136 <= BArray1024.size
    ==>
    KeygenShakeStreamSpec.rate_block_matches
      res.`1 (W64.to_uint outoff0) res.`2 136 /\
    KeygenShakeStreamSpec.rate_block_frame
      out0 res.`1 (W64.to_uint outoff0) 136 /\
    KeygenKeccak1600Spec.state_of_barray res.`2 =
      HAETAE_Keccak1600.keccak_f1600_lanes
        (KeygenKeccak1600Spec.state_of_barray state0)].
proof.
proc.
while (
  KeygenShakeStreamSpec.rate_prefix_matches
    outp (W64.to_uint outoff0) sp_0 (W64.to_uint i) /\
  KeygenShakeStreamSpec.rate_block_frame
    out0 outp (W64.to_uint outoff0) 136 /\
  W64.to_uint idx = W64.to_uint outoff0 + W64.to_uint i /\
  0 <= W64.to_uint i <= 136 /\
  W64.to_uint i %% 8 = 0 /\
  W64.to_uint outoff0 + 136 <= BArray1024.size /\
  KeygenKeccak1600Spec.state_of_barray sp_0 =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (KeygenKeccak1600Spec.state_of_barray state0)).
+ wp.
  while (
    KeygenShakeStreamSpec.rate_prefix_matches
      outp (W64.to_uint outoff0) sp_0
        (W64.to_uint i + W64.to_uint j) /\
    KeygenShakeStreamSpec.rate_block_frame
      out0 outp (W64.to_uint outoff0) 136 /\
    W64.to_uint idx =
      W64.to_uint outoff0 + W64.to_uint i + W64.to_uint j /\
    W64.to_uint lane = W64.to_uint i %/ 8 /\
    t = KeygenShakeStreamSpec.drop_bytes
          (BArray200.get64 sp_0 (W64.to_uint i %/ 8))
          (W64.to_uint j) /\
    0 <= W64.to_uint i < 136 /\
    W64.to_uint i %% 8 = 0 /\
    0 <= W64.to_uint j <= 8 /\
    W64.to_uint outoff0 + 136 <= BArray1024.size /\
    KeygenKeccak1600Spec.state_of_barray sp_0 =
      HAETAE_Keccak1600.keccak_f1600_lanes
        (KeygenKeccak1600Spec.state_of_barray state0)).
  + auto => /> &hr hprefix hframe hidx hlane
                   hi0 hi136 himod hj0 hj8 hcap hperm hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    have hi8 := KeygenShakeStreamSpec.div8_split
                  (W64.to_uint i{hr}) hi0 himod.
    have hoff : 0 <= W64.to_uint outoff0 by smt(W64.to_uint_cmp).
    have hjlt : 0 <= W64.to_uint j{hr} < 8 by smt().
    have hwritecap :
      W64.to_uint outoff0 +
        (W64.to_uint i{hr} + W64.to_uint j{hr}) <
      BArray1024.size by smt().
    have hp := KeygenShakeStreamSpec.rate_prefix_set_cursor
      outp{hr} (W64.to_uint outoff0) sp_0{hr}
      (W64.to_uint i{hr}) (W64.to_uint j{hr})
      hoff hi0 himod hjlt hwritecap hprefix.
    rewrite /KeygenShakeStreamSpec.rate_lane_byte in hp.
    split.
    + rewrite W64.to_uintD_small 1:/# W64.to_uint1 hidx.
      have -> :
        W64.to_uint outoff0 + W64.to_uint i{hr} +
          W64.to_uint j{hr} =
        W64.to_uint outoff0 +
          (W64.to_uint i{hr} + W64.to_uint j{hr}) by ring.
      have -> :
        W64.to_uint i{hr} + (W64.to_uint j{hr} + 1) =
        W64.to_uint i{hr} + W64.to_uint j{hr} + 1 by ring.
      exact hp.
    split.
    + rewrite hidx.
      have -> :
        W64.to_uint outoff0 + W64.to_uint i{hr} +
          W64.to_uint j{hr} =
        W64.to_uint outoff0 +
          (W64.to_uint i{hr} + W64.to_uint j{hr}) by ring.
      apply (KeygenShakeStreamSpec.rate_block_frame_set_inside
               out0 outp{hr} (W64.to_uint outoff0) 136
               (W64.to_uint i{hr} + W64.to_uint j{hr})
               (truncateu8
                 (KeygenShakeStreamSpec.drop_bytes
                   (BArray200.get64 sp_0{hr}
                     (W64.to_uint i{hr} %/ 8))
                   (W64.to_uint j{hr})))).
      + exact hoff.
      + smt().
      + exact hcap.
      + exact hframe.
    do split.
    + rewrite W64.to_uintD_small 1:/#.
      rewrite hidx.
      ring.
    + smt().
    + rewrite W64.to_uintD_small 1:/#.
      rewrite KeygenShakeStreamSpec.drop_bytes_succ 1:/#.
      trivial.
    + smt().
    + smt().
  auto => /> &hr hprefix hframe hidx hi0 hi136 himod hcap hperm hguard.
  split.
  + split.
    + rewrite W64.shr_div_le 1:/# /=.
    split.
    + rewrite KeygenShakeStreamSpec.drop_bytes0.
      rewrite W64.shr_div_le 1:/# /=.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    exact hguard.
  move=> idx0 j0 outp0 hjdone hp hf hidx0 hlane hi136' hj0 hj8.
  rewrite W64.ultE W64.of_uintK /= in hjdone.
  have hj : W64.to_uint j0 = 8 by smt(W64.to_uint_cmp).
  have hjword : j0 = W64.of_int 8.
  + by rewrite -(W64.to_uintK' j0) hj.
  subst j0.
  rewrite W64.to_uintD_small 1:/# /=.
  do split.
  + exact hp.
  + rewrite hidx0.
    ring.
  + smt(W64.to_uint_cmp).
  + smt(W64.to_uint_cmp).
  smt().
wp.
call (TargetKeygenKeccak1600.keccakf1600_correct state0).
auto => /> &hr hcap hperm.
split.
+ exact (KeygenShakeStreamSpec.rate_prefix_zero
           (SLH64.protect_ptr out0 W64.zero)
           (W64.to_uint outoff0) hcap).
move=> i0 idx0 outp0 hdone hprefix hframe hidx hi0 hi136 himod.
rewrite /KeygenShakeStreamSpec.rate_block_matches.
have <- : W64.to_uint i0 = 136.
+ rewrite W64.ultE W64.of_uintK /= in hdone.
  smt(W64.to_uint_cmp).
exact hprefix.
qed.

module CheckedShakeOneBlock = {
  proc shake128
      (outp : BArray1024.t, outoff : W64.t,
       seedp : BArray128.t, seedoff nonce : W64.t) :
      BArray1024.t * BArray200.t = {
    var sp_0 : BArray200.t;

    sp_0 <- witness;
    sp_0 <@ KeygenSamplerCallersTarget.M.__kp_shake128_init_seedbuf
      (sp_0, seedp, seedoff, nonce);
    (outp, sp_0) <@ KeygenSamplerCallersTarget.M.__poly_sample_squeeze128
      (outp, outoff, sp_0);
    return (outp, sp_0);
  }

  proc shake256
      (outp : BArray1024.t, outoff : W64.t,
       seedp : BArray128.t, seedoff nonce : W64.t) :
      BArray1024.t * BArray200.t = {
    var sp_0 : BArray200.t;

    sp_0 <- witness;
    sp_0 <@ KeygenSamplerCallersTarget.M.__kp_shake256_init_seedbuf
      (sp_0, seedp, seedoff, nonce);
    (outp, sp_0) <@ KeygenSamplerCallersTarget.M.__poly_sample_squeeze256
      (outp, outoff, sp_0);
    return (outp, sp_0);
  }
}.

lemma shake128_seedbuf_one_block_raw
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  hoare [CheckedShakeOneBlock.shake128 :
    outp = out0 /\ outoff = outoff0 /\
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size /\
    W64.to_uint outoff0 + 168 <= BArray1024.size
    ==>
    exists framed,
      KeygenShakeStreamSpec.shake128_seedbuf_framing
        framed seed0 seedoff0 nonce0 /\
      KeygenShakeStreamSpec.rate_block_matches
        res.`1 (W64.to_uint outoff0) res.`2 168 /\
      KeygenShakeStreamSpec.rate_block_frame
        out0 res.`1 (W64.to_uint outoff0) 168 /\
      KeygenKeccak1600Spec.state_of_barray res.`2 =
        HAETAE_Keccak1600.keccak_f1600_lanes
          (KeygenKeccak1600Spec.state_of_barray framed)].
proof.
proc.
seq 2 :
  (KeygenShakeStreamSpec.shake128_seedbuf_framing
       sp_0 seed0 seedoff0 nonce0 /\
   outp = out0 /\ outoff = outoff0 /\
   seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
   W64.to_uint seedoff0 + 32 <= BArray128.size /\
   W64.to_uint outoff0 + 168 <= BArray1024.size).
+ wp.
  call (shake128_init_seedbuf_framing seed0 seedoff0 nonce0).
  auto => />.
+ wp.
  exlim sp_0 => framed.
  call (squeeze128_rate_block out0 outoff0 framed).
  auto => />; smt().
qed.

lemma shake256_seedbuf_one_block_raw
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  hoare [CheckedShakeOneBlock.shake256 :
    outp = out0 /\ outoff = outoff0 /\
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint seedoff0 + 64 <= BArray128.size /\
    W64.to_uint outoff0 + 136 <= BArray1024.size
    ==>
    exists framed,
      KeygenShakeStreamSpec.shake256_seedbuf_framing
        framed seed0 seedoff0 nonce0 /\
      KeygenShakeStreamSpec.rate_block_matches
        res.`1 (W64.to_uint outoff0) res.`2 136 /\
      KeygenShakeStreamSpec.rate_block_frame
        out0 res.`1 (W64.to_uint outoff0) 136 /\
      KeygenKeccak1600Spec.state_of_barray res.`2 =
        HAETAE_Keccak1600.keccak_f1600_lanes
          (KeygenKeccak1600Spec.state_of_barray framed)].
proof.
proc.
seq 2 :
  (KeygenShakeStreamSpec.shake256_seedbuf_framing
       sp_0 seed0 seedoff0 nonce0 /\
   outp = out0 /\ outoff = outoff0 /\
   seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
   W64.to_uint seedoff0 + 64 <= BArray128.size /\
   W64.to_uint outoff0 + 136 <= BArray1024.size).
+ wp.
  call (shake256_init_seedbuf_framing seed0 seedoff0 nonce0).
  auto => />.
+ wp.
  exlim sp_0 => framed.
  call (squeeze256_rate_block out0 outoff0 framed).
  auto => />; smt().
qed.

lemma shake128_seedbuf_one_block_post
    (out0 out1 : BArray1024.t) (outoff0 : W64.t)
    (framed state1 : BArray200.t)
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  W64.to_uint seedoff0 + 32 <= BArray128.size =>
  KeygenShakeStreamSpec.shake128_seedbuf_framing
    framed seed0 seedoff0 nonce0 =>
  KeygenShakeStreamSpec.rate_block_matches
    out1 (W64.to_uint outoff0) state1 168 =>
  KeygenShakeStreamSpec.rate_block_frame
    out0 out1 (W64.to_uint outoff0) 168 =>
  KeygenKeccak1600Spec.state_of_barray state1 =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (KeygenKeccak1600Spec.state_of_barray framed) =>
  KeygenShakeStreamSpec.state_bytes_le state1 =
    KeygenShakeStreamSpec.shake128_seed_nonce_state
      seed0 seedoff0 nonce0 /\
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    out1 (W64.to_uint outoff0)
    (KeygenShakeStreamSpec.shake128_seed_nonce_state
      seed0 seedoff0 nonce0) 168 /\
  KeygenShakeStreamSpec.rate_block_frame
    out0 out1 (W64.to_uint outoff0) 168.
proof.
move=> hseedcap hframing hmatches hframe hperm.
have hpadded :=
  KeygenShakeStreamSpec.shake128_framing_fips_state
    framed seed0 seedoff0 nonce0 hseedcap hframing.
have hlanes :=
  KeygenShakeStreamSpec.state_of_barray_state_bytes_le framed.
have hstate :=
  KeygenShakeStreamSpec.shake128_returned_state_bytes
    state1 seed0 seedoff0 nonce0 _.
+ by rewrite hperm hlanes hpadded.
have hprefix :=
  KeygenShakeStreamSpec.shake128_rate_block_first_block
    out1 (W64.to_uint outoff0) state1
    seed0 seedoff0 nonce0 hstate hmatches.
by rewrite hstate hprefix.
qed.

lemma shake256_seedbuf_one_block_post
    (out0 out1 : BArray1024.t) (outoff0 : W64.t)
    (framed state1 : BArray200.t)
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  W64.to_uint seedoff0 + 64 <= BArray128.size =>
  KeygenShakeStreamSpec.shake256_seedbuf_framing
    framed seed0 seedoff0 nonce0 =>
  KeygenShakeStreamSpec.rate_block_matches
    out1 (W64.to_uint outoff0) state1 136 =>
  KeygenShakeStreamSpec.rate_block_frame
    out0 out1 (W64.to_uint outoff0) 136 =>
  KeygenKeccak1600Spec.state_of_barray state1 =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (KeygenKeccak1600Spec.state_of_barray framed) =>
  KeygenShakeStreamSpec.state_bytes_le state1 =
    KeygenShakeStreamSpec.shake256_seed_nonce_state
      seed0 seedoff0 nonce0 /\
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    out1 (W64.to_uint outoff0)
    (KeygenShakeStreamSpec.shake256_seed_nonce_state
      seed0 seedoff0 nonce0) 136 /\
  KeygenShakeStreamSpec.rate_block_frame
    out0 out1 (W64.to_uint outoff0) 136.
proof.
move=> hseedcap hframing hmatches hframe hperm.
have hpadded :=
  KeygenShakeStreamSpec.shake256_framing_fips_state
    framed seed0 seedoff0 nonce0 hseedcap hframing.
have hlanes :=
  KeygenShakeStreamSpec.state_of_barray_state_bytes_le framed.
have hstate :=
  KeygenShakeStreamSpec.shake256_returned_state_bytes
    state1 seed0 seedoff0 nonce0 _.
+ by rewrite hperm hlanes hpadded.
have hprefix :=
  KeygenShakeStreamSpec.shake256_rate_block_first_block
    out1 (W64.to_uint outoff0) state1
    seed0 seedoff0 nonce0 hstate hmatches.
by rewrite hstate hprefix.
qed.

lemma shake128_seedbuf_one_block
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  hoare [CheckedShakeOneBlock.shake128 :
    outp = out0 /\ outoff = outoff0 /\
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size /\
    W64.to_uint outoff0 + 168 <= BArray1024.size
    ==>
    KeygenShakeStreamSpec.state_bytes_le res.`2 =
      KeygenShakeStreamSpec.shake128_seed_nonce_state
        seed0 seedoff0 nonce0 /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      res.`1 (W64.to_uint outoff0)
      (KeygenShakeStreamSpec.shake128_seed_nonce_state
        seed0 seedoff0 nonce0) 168 /\
    KeygenShakeStreamSpec.rate_block_frame
      out0 res.`1 (W64.to_uint outoff0) 168].
proof.
conseq (shake128_seedbuf_one_block_raw
  out0 outoff0 seed0 seedoff0 nonce0).
move=> &hr hpre result
  [framed [hframing [hmatches [hframe hperm]]]].
apply (shake128_seedbuf_one_block_post
  out0 result.`1 outoff0 framed result.`2 seed0 seedoff0 nonce0).
+ by smt().
+ exact hframing.
+ exact hmatches.
+ exact hframe.
+ exact hperm.
qed.

lemma shake256_seedbuf_one_block
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  hoare [CheckedShakeOneBlock.shake256 :
    outp = out0 /\ outoff = outoff0 /\
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint seedoff0 + 64 <= BArray128.size /\
    W64.to_uint outoff0 + 136 <= BArray1024.size
    ==>
    KeygenShakeStreamSpec.state_bytes_le res.`2 =
      KeygenShakeStreamSpec.shake256_seed_nonce_state
        seed0 seedoff0 nonce0 /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      res.`1 (W64.to_uint outoff0)
      (KeygenShakeStreamSpec.shake256_seed_nonce_state
        seed0 seedoff0 nonce0) 136 /\
    KeygenShakeStreamSpec.rate_block_frame
      out0 res.`1 (W64.to_uint outoff0) 136].
proof.
conseq (shake256_seedbuf_one_block_raw
  out0 outoff0 seed0 seedoff0 nonce0).
move=> &hr hpre result
  [framed [hframing [hmatches [hframe hperm]]]].
apply (shake256_seedbuf_one_block_post
  out0 result.`1 outoff0 framed result.`2 seed0 seedoff0 nonce0).
+ by smt().
+ exact hframing.
+ exact hmatches.
+ exact hframe.
+ exact hperm.
qed.

module CheckedShakeBlocks = {
  proc shake128
      (outp : BArray1024.t, outoff : W64.t,
       seedp : BArray128.t, seedoff nonce : W64.t,
       nblocks : int) : BArray1024.t * BArray200.t = {
    var sp_0 : BArray200.t;
    var blockoff : W64.t;
    var i : int;

    sp_0 <- witness;
    sp_0 <@ KeygenSamplerCallersTarget.M.__kp_shake128_init_seedbuf
      (sp_0, seedp, seedoff, nonce);
    blockoff <- outoff;
    i <- 0;
    while (i < nblocks) {
      (outp, sp_0) <@
        KeygenSamplerCallersTarget.M.__poly_sample_squeeze128
          (outp, blockoff, sp_0);
      blockoff <- blockoff + W64.of_int 168;
      i <- i + 1;
    }
    return (outp, sp_0);
  }

  proc shake256
      (outp : BArray1024.t, outoff : W64.t,
       seedp : BArray128.t, seedoff nonce : W64.t,
       nblocks : int) : BArray1024.t * BArray200.t = {
    var sp_0 : BArray200.t;
    var blockoff : W64.t;
    var i : int;

    sp_0 <- witness;
    sp_0 <@ KeygenSamplerCallersTarget.M.__kp_shake256_init_seedbuf
      (sp_0, seedp, seedoff, nonce);
    blockoff <- outoff;
    i <- 0;
    while (i < nblocks) {
      (outp, sp_0) <@
        KeygenSamplerCallersTarget.M.__poly_sample_squeeze256
          (outp, blockoff, sp_0);
      blockoff <- blockoff + W64.of_int 136;
      i <- i + 1;
    }
    return (outp, sp_0);
  }
}.

lemma shake128_seedbuf_blocks
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t)
    (blocks0 : int) :
  hoare [CheckedShakeBlocks.shake128 :
    outp = out0 /\ outoff = outoff0 /\
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    nblocks = blocks0 /\
    0 <= blocks0 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size /\
    W64.to_uint outoff0 + blocks0 * 168 <= BArray1024.size
    ==>
    KeygenShakeStreamSpec.state_bytes_le res.`2 =
      KeygenShakeStreamSpec.squeeze_state_iter
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) blocks0 /\
    KeygenShakeStreamSpec.squeeze_blocks_matches
      res.`1 (W64.to_uint outoff0)
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 168 blocks0 /\
    KeygenShakeStreamSpec.squeeze_region_frame
      out0 res.`1 (W64.to_uint outoff0) 168 blocks0].
proof.
proc.
seq 2 :
  (KeygenShakeStreamSpec.shake128_seedbuf_framing
     sp_0 seed0 seedoff0 nonce0 /\
   outp = out0 /\ outoff = outoff0 /\ nblocks = blocks0 /\
   0 <= blocks0 /\
   W64.to_uint seedoff0 + 32 <= BArray128.size /\
   W64.to_uint outoff0 + blocks0 * 168 <= BArray1024.size).
+ wp.
  call (shake128_init_seedbuf_framing seed0 seedoff0 nonce0).
  auto => />.
+ while (
  KeygenShakeStreamSpec.state_bytes_le sp_0 =
    KeygenShakeStreamSpec.squeeze_state_iter
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) i /\
  KeygenShakeStreamSpec.squeeze_blocks_matches
    outp (W64.to_uint outoff0)
    (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
      seed0 seedoff0 nonce0) 168 i /\
  KeygenShakeStreamSpec.squeeze_region_frame
    out0 outp (W64.to_uint outoff0) 168 i /\
  W64.to_uint blockoff = W64.to_uint outoff0 + i * 168 /\
  0 <= i <= blocks0 /\
  nblocks = blocks0 /\
  W64.to_uint outoff0 + blocks0 * 168 <= BArray1024.size).
+ wp.
  exlim outp => before_out.
  exlim sp_0 => before_state.
  exlim blockoff => before_off.
  call (squeeze128_rate_block before_out before_off before_state).
  auto => /> &hr hstate hmatches hregion hoff hi0 hile hn htotal.
  have hilt : i{hr} < blocks0 by smt().
  have hnextcap :
      W64.to_uint outoff0 + (i{hr} + 1) * 168 <=
      BArray1024.size by smt().
  have hcallcap :
      W64.to_uint before_off + 168 <= BArray1024.size.
  + rewrite hoff.
    smt().
  split; first exact hcallcap.
  move=> _ result hblock hframe hperm.
  have hstate_next :=
    KeygenShakeStreamSpec.squeeze_state_iter_barray_step
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0)
      before_state result.`2 i{hr} hi0 hstate hperm.
  have hprefix0 :=
    KeygenShakeStreamSpec.rate_block_matches_fips_prefix
      result.`1 (W64.to_uint before_off) result.`2
      (KeygenShakeStreamSpec.squeeze_state_iter
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) (i{hr} + 1)) 168
      _ hstate_next hblock.
  + smt().
  have hprefix :
      KeygenShakeStreamSpec.fips_rate_prefix_matches
        result.`1 (W64.to_uint outoff0 + i{hr} * 168)
        (KeygenShakeStreamSpec.squeeze_state_iter
          (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
            seed0 seedoff0 nonce0) (i{hr} + 1)) 168.
  + by rewrite -hoff.
  have hframe_at :
      KeygenShakeStreamSpec.rate_block_frame
        before_out result.`1
        (W64.to_uint outoff0 + i{hr} * 168) 168.
  + by rewrite -hoff.
  have [hmatches_next hregion_next] :=
    KeygenShakeStreamSpec.squeeze_blocks_induction_step
      out0 before_out result.`1 (W64.to_uint outoff0)
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 168 i{hr}
      _ hi0 _ hnextcap hmatches hregion hprefix hframe_at.
  + smt(W64.to_uint_cmp).
  + smt().
  have hoff_next :
      W64.to_uint (before_off + W64.of_int 168) =
      W64.to_uint outoff0 + (i{hr} + 1) * 168.
  + rewrite W64.to_uintD_small.
    + rewrite W64.to_uint_small 1:/# hoff.
      smt(W64.to_uint_cmp).
    rewrite W64.to_uint_small 1:/# hoff.
    ring.
  do split.
  + exact hstate_next.
  + exact hmatches_next.
  + exact hregion_next.
  + exact hoff_next.
  + smt().
  smt().
wp.
skip => &hr
  [hframing [hout [houtoff [hn [hblocks [hseedcap htotal]]]]]].
split.
+ rewrite hout houtoff hn.
  have hstate0 :=
    KeygenShakeStreamSpec.shake128_framing_fips_state
      sp_0{hr} seed0 seedoff0 nonce0 hseedcap hframing.
  do split.
  + by rewrite KeygenShakeStreamSpec.squeeze_state_iter0; exact hstate0.
  + exact (KeygenShakeStreamSpec.squeeze_blocks_matches0
             out0 (W64.to_uint outoff0)
             (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
               seed0 seedoff0 nonce0) 168).
  + smt().
  + smt().
  smt().
qed.

lemma shake256_seedbuf_blocks
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t)
    (blocks0 : int) :
  hoare [CheckedShakeBlocks.shake256 :
    outp = out0 /\ outoff = outoff0 /\
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    nblocks = blocks0 /\
    0 <= blocks0 /\
    W64.to_uint seedoff0 + 64 <= BArray128.size /\
    W64.to_uint outoff0 + blocks0 * 136 <= BArray1024.size
    ==>
    KeygenShakeStreamSpec.state_bytes_le res.`2 =
      KeygenShakeStreamSpec.squeeze_state_iter
        (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
          seed0 seedoff0 nonce0) blocks0 /\
    KeygenShakeStreamSpec.squeeze_blocks_matches
      res.`1 (W64.to_uint outoff0)
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 136 blocks0 /\
    KeygenShakeStreamSpec.squeeze_region_frame
      out0 res.`1 (W64.to_uint outoff0) 136 blocks0].
proof.
proc.
seq 2 :
  (KeygenShakeStreamSpec.shake256_seedbuf_framing
     sp_0 seed0 seedoff0 nonce0 /\
   outp = out0 /\ outoff = outoff0 /\ nblocks = blocks0 /\
   0 <= blocks0 /\
   W64.to_uint seedoff0 + 64 <= BArray128.size /\
   W64.to_uint outoff0 + blocks0 * 136 <= BArray1024.size).
+ wp.
  call (shake256_init_seedbuf_framing seed0 seedoff0 nonce0).
  auto => />.
+ while (
  KeygenShakeStreamSpec.state_bytes_le sp_0 =
    KeygenShakeStreamSpec.squeeze_state_iter
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0) i /\
  KeygenShakeStreamSpec.squeeze_blocks_matches
    outp (W64.to_uint outoff0)
    (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
      seed0 seedoff0 nonce0) 136 i /\
  KeygenShakeStreamSpec.squeeze_region_frame
    out0 outp (W64.to_uint outoff0) 136 i /\
  W64.to_uint blockoff = W64.to_uint outoff0 + i * 136 /\
  0 <= i <= blocks0 /\
  nblocks = blocks0 /\
  W64.to_uint outoff0 + blocks0 * 136 <= BArray1024.size).
+ wp.
  exlim outp => before_out.
  exlim sp_0 => before_state.
  exlim blockoff => before_off.
  call (squeeze256_rate_block before_out before_off before_state).
  auto => /> &hr hstate hmatches hregion hoff hi0 hile hn htotal.
  have hilt : i{hr} < blocks0 by smt().
  have hnextcap :
      W64.to_uint outoff0 + (i{hr} + 1) * 136 <=
      BArray1024.size by smt().
  have hcallcap :
      W64.to_uint before_off + 136 <= BArray1024.size.
  + rewrite hoff.
    smt().
  split; first exact hcallcap.
  move=> _ result hblock hframe hperm.
  have hstate_next :=
    KeygenShakeStreamSpec.squeeze_state_iter_barray_step
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0)
      before_state result.`2 i{hr} hi0 hstate hperm.
  have hprefix0 :=
    KeygenShakeStreamSpec.rate_block_matches_fips_prefix
      result.`1 (W64.to_uint before_off) result.`2
      (KeygenShakeStreamSpec.squeeze_state_iter
        (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
          seed0 seedoff0 nonce0) (i{hr} + 1)) 136
      _ hstate_next hblock.
  + smt().
  have hprefix :
      KeygenShakeStreamSpec.fips_rate_prefix_matches
        result.`1 (W64.to_uint outoff0 + i{hr} * 136)
        (KeygenShakeStreamSpec.squeeze_state_iter
          (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
            seed0 seedoff0 nonce0) (i{hr} + 1)) 136.
  + by rewrite -hoff.
  have hframe_at :
      KeygenShakeStreamSpec.rate_block_frame
        before_out result.`1
        (W64.to_uint outoff0 + i{hr} * 136) 136.
  + by rewrite -hoff.
  have [hmatches_next hregion_next] :=
    KeygenShakeStreamSpec.squeeze_blocks_induction_step
      out0 before_out result.`1 (W64.to_uint outoff0)
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 136 i{hr}
      _ hi0 _ hnextcap hmatches hregion hprefix hframe_at.
  + smt(W64.to_uint_cmp).
  + smt().
  have hoff_next :
      W64.to_uint (before_off + W64.of_int 136) =
      W64.to_uint outoff0 + (i{hr} + 1) * 136.
  + rewrite W64.to_uintD_small.
    + rewrite W64.to_uint_small 1:/# hoff.
      smt(W64.to_uint_cmp).
    rewrite W64.to_uint_small 1:/# hoff.
    ring.
  do split.
  + exact hstate_next.
  + exact hmatches_next.
  + exact hregion_next.
  + exact hoff_next.
  + smt().
  smt().
wp.
skip => &hr
  [hframing [hout [houtoff [hn [hblocks [hseedcap htotal]]]]]].
split.
+ rewrite hout houtoff hn.
  have hstate0 :=
    KeygenShakeStreamSpec.shake256_framing_fips_state
      sp_0{hr} seed0 seedoff0 nonce0 hseedcap hframing.
  do split.
  + by rewrite KeygenShakeStreamSpec.squeeze_state_iter0; exact hstate0.
  + exact (KeygenShakeStreamSpec.squeeze_blocks_matches0
             out0 (W64.to_uint outoff0)
             (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
               seed0 seedoff0 nonce0) 136).
  + smt().
  + smt().
smt().
qed.

lemma shake128_seedbuf_blocks_one_block
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  hoare [CheckedShakeBlocks.shake128 :
    outp = out0 /\ outoff = outoff0 /\
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    nblocks = 1 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size /\
    W64.to_uint outoff0 + 168 <= BArray1024.size
    ==>
    KeygenShakeStreamSpec.state_bytes_le res.`2 =
      KeygenShakeStreamSpec.shake128_seed_nonce_state
        seed0 seedoff0 nonce0 /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      res.`1 (W64.to_uint outoff0)
      (KeygenShakeStreamSpec.shake128_seed_nonce_state
        seed0 seedoff0 nonce0) 168 /\
    KeygenShakeStreamSpec.rate_block_frame
      out0 res.`1 (W64.to_uint outoff0) 168].
proof.
conseq (shake128_seedbuf_blocks
  out0 outoff0 seed0 seedoff0 nonce0 1).
move=> &hr hpre result [hstate [hmatches hframe]].
have hstate1 :
    KeygenShakeStreamSpec.squeeze_state_iter
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 1 =
    KeygenShakeStreamSpec.shake128_seed_nonce_state
      seed0 seedoff0 nonce0.
+ rewrite (_ : 1 = 0 + 1) 1:/#
          KeygenShakeStreamSpec.squeeze_state_iter_succ 1:/#
          KeygenShakeStreamSpec.squeeze_state_iter0.
  by rewrite /KeygenShakeStreamSpec.shake128_seed_nonce_state
             /KeygenShakeStreamSpec.shake128_absorb_once
             /KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
             /HAETAE_Keccak1600.keccak_f1600_bytes.
have hprefix :
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      result.`1 (W64.to_uint outoff0)
      (KeygenShakeStreamSpec.squeeze_state_iter
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 1) 168.
+ rewrite /KeygenShakeStreamSpec.squeeze_blocks_matches in hmatches.
  rewrite /KeygenShakeStreamSpec.fips_rate_prefix_matches.
  move=> byte hbyte.
  have hmatch := hmatches 0 byte _ hbyte; first smt().
  by rewrite /= in hmatch.
have hframe1 :
    KeygenShakeStreamSpec.rate_block_frame
      out0 result.`1 (W64.to_uint outoff0) 168.
+ rewrite /KeygenShakeStreamSpec.squeeze_region_frame in hframe.
  rewrite /KeygenShakeStreamSpec.rate_block_frame.
  move=> byte_index hindex houtside.
  apply (hframe byte_index hindex).
  smt().
do split.
+ by rewrite hstate hstate1.
+ by rewrite -hstate1.
exact hframe1.
qed.

lemma shake256_seedbuf_blocks_one_block
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  hoare [CheckedShakeBlocks.shake256 :
    outp = out0 /\ outoff = outoff0 /\
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    nblocks = 1 /\
    W64.to_uint seedoff0 + 64 <= BArray128.size /\
    W64.to_uint outoff0 + 136 <= BArray1024.size
    ==>
    KeygenShakeStreamSpec.state_bytes_le res.`2 =
      KeygenShakeStreamSpec.shake256_seed_nonce_state
        seed0 seedoff0 nonce0 /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      res.`1 (W64.to_uint outoff0)
      (KeygenShakeStreamSpec.shake256_seed_nonce_state
        seed0 seedoff0 nonce0) 136 /\
    KeygenShakeStreamSpec.rate_block_frame
      out0 res.`1 (W64.to_uint outoff0) 136].
proof.
conseq (shake256_seedbuf_blocks
  out0 outoff0 seed0 seedoff0 nonce0 1).
move=> &hr hpre result [hstate [hmatches hframe]].
have hstate1 :
    KeygenShakeStreamSpec.squeeze_state_iter
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 1 =
    KeygenShakeStreamSpec.shake256_seed_nonce_state
      seed0 seedoff0 nonce0.
+ rewrite (_ : 1 = 0 + 1) 1:/#
          KeygenShakeStreamSpec.squeeze_state_iter_succ 1:/#
          KeygenShakeStreamSpec.squeeze_state_iter0.
  by rewrite /KeygenShakeStreamSpec.shake256_seed_nonce_state
             /HAETAE_FIPS202.shake256_absorb_once
             /HAETAE_FIPS202.fips202_keccak_f1600
             /KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             /HAETAE_Keccak1600.keccak_f1600_bytes.
have hprefix :
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      result.`1 (W64.to_uint outoff0)
      (KeygenShakeStreamSpec.squeeze_state_iter
        (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 1) 136.
+ rewrite /KeygenShakeStreamSpec.squeeze_blocks_matches in hmatches.
  rewrite /KeygenShakeStreamSpec.fips_rate_prefix_matches.
  move=> byte hbyte.
  have hmatch := hmatches 0 byte _ hbyte; first smt().
  by rewrite /= in hmatch.
have hframe1 :
    KeygenShakeStreamSpec.rate_block_frame
      out0 result.`1 (W64.to_uint outoff0) 136.
+ rewrite /KeygenShakeStreamSpec.squeeze_region_frame in hframe.
  rewrite /KeygenShakeStreamSpec.rate_block_frame.
  move=> byte_index hindex houtside.
  apply (hframe byte_index hindex).
  smt().
do split.
+ by rewrite hstate hstate1.
+ by rewrite -hstate1.
exact hframe1.
qed.

lemma shake128_seedbuf_four_blocks
    (out0 : BArray1024.t)
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  hoare [CheckedShakeBlocks.shake128 :
    outp = out0 /\ outoff = W64.of_int 0 /\
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    nblocks = 4 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size
    ==>
    KeygenShakeStreamSpec.state_bytes_le res.`2 =
      KeygenShakeStreamSpec.squeeze_state_iter
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 4 /\
    KeygenShakeStreamSpec.squeeze_blocks_matches
      res.`1 0
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 168 4 /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      res.`1 0
      (KeygenShakeStreamSpec.shake128_squeeze_bytes
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 4) 672 /\
    KeygenShakeStreamSpec.squeeze_region_frame
      out0 res.`1 0 168 4].
proof.
conseq (shake128_seedbuf_blocks
  out0 (W64.of_int 0) seed0 seedoff0 nonce0 4).
move=> &hr hpre result [hstate [hmatches hframe]].
have hprefix :=
  KeygenShakeStreamSpec.shake128_squeeze_blocks_fips
    result.`1 0
    (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
      seed0 seedoff0 nonce0) 4 _ hmatches.
+ smt().
do split.
+ exact hstate.
+ exact hmatches.
+ by rewrite /= in hprefix.
exact hframe.
qed.

(* Totality here follows solely from the fixed generated loop bounds and the
   totality of Keccak-f1600.  In particular, no output-distribution or
   rejection-sampling hypothesis is used. *)
lemma shake128_init_seedbuf_ll :
  islossless KeygenSamplerCallersTarget.M.__kp_shake128_init_seedbuf.
proof.
proc.
wp.
while (0 <= k <= 2) (2 - k).
+ by move=> z; auto => />; smt().
wp.
while (W64.to_uint pos <= 32) (32 - W64.to_uint pos).
+ move=> z.
  auto => /> &hr hpos hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
  smt().
wp.
call TargetKeygenKeccak1600.keccak_init_state_ll.
auto => />.
move=> pos0.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma shake256_init_seedbuf_ll :
  islossless KeygenSamplerCallersTarget.M.__kp_shake256_init_seedbuf.
proof.
proc.
wp.
while (0 <= k <= 2) (2 - k).
+ by move=> z; auto => />; smt().
wp.
while (W64.to_uint pos <= 64) (64 - W64.to_uint pos).
+ move=> z.
  auto => /> &hr hpos hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
  smt().
wp.
call TargetKeygenKeccak1600.keccak_init_state_ll.
auto => />.
move=> pos0.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma squeeze128_ll :
  islossless KeygenSamplerCallersTarget.M.__poly_sample_squeeze128.
proof.
proc.
while (exists n, 0 <= n <= 21 /\ W64.to_uint i = 8 * n)
      (168 - W64.to_uint i).
+ move=> z.
  wp.
  while (W64.to_uint j <= 8) (8 - W64.to_uint j).
  + move=> z0.
    auto => /> &hr hj hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
    smt().
  auto => />.
  move=> &hr n hn0 hn21 hi hguard j0.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
  rewrite W64.ultE W64.of_uintK /=.
  split; first smt().
  move=> _ _.
  smt().
wp.
call TargetKeygenKeccak1600.keccakf1600_ll.
auto => />.
split; first by exists 0.
move=> i0 n hn0 hn21 hi hvariant.
rewrite W64.ultE W64.of_uintK /=.
smt().
qed.

lemma squeeze256_ll :
  islossless KeygenSamplerCallersTarget.M.__poly_sample_squeeze256.
proof.
proc.
while (exists n, 0 <= n <= 17 /\ W64.to_uint i = 8 * n)
      (136 - W64.to_uint i).
+ move=> z.
  wp.
  while (W64.to_uint j <= 8) (8 - W64.to_uint j).
  + move=> z0.
    auto => /> &hr hj hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
    smt().
  auto => />.
  move=> &hr n hn0 hn17 hi hguard j0.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
  rewrite W64.ultE W64.of_uintK /=.
  split; first smt().
  move=> _ _.
  smt().
wp.
call TargetKeygenKeccak1600.keccakf1600_ll.
auto => />.
split; first by exists 0.
move=> i0 n hn0 hn17 hi hvariant.
rewrite W64.ultE W64.of_uintK /=.
smt().
qed.

lemma shake128_init_seedbuf_padded_state_pll
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  phoare [KeygenSamplerCallersTarget.M.__kp_shake128_init_seedbuf :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint seedoff0 + 32 <= BArray128.size
    ==>
    KeygenShakeStreamSpec.state_bytes_le res =
      KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed0 seedoff0 nonce0] = 1%r.
proof.
by conseq shake128_init_seedbuf_ll
          (shake128_init_seedbuf_padded_state seed0 seedoff0 nonce0).
qed.

lemma shake256_init_seedbuf_padded_state_pll
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) :
  phoare [KeygenSamplerCallersTarget.M.__kp_shake256_init_seedbuf :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint seedoff0 + 64 <= BArray128.size
    ==>
    KeygenShakeStreamSpec.state_bytes_le res =
      KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0] = 1%r.
proof.
by conseq shake256_init_seedbuf_ll
          (shake256_init_seedbuf_padded_state seed0 seedoff0 nonce0).
qed.

lemma squeeze128_rate_block_pll
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (state0 : BArray200.t) :
  phoare [KeygenSamplerCallersTarget.M.__poly_sample_squeeze128 :
    outp = out0 /\ outoff = outoff0 /\ sp_0 = state0 /\
    W64.to_uint outoff0 + 168 <= BArray1024.size
    ==>
    KeygenShakeStreamSpec.rate_block_matches
      res.`1 (W64.to_uint outoff0) res.`2 168 /\
    KeygenShakeStreamSpec.rate_block_frame
      out0 res.`1 (W64.to_uint outoff0) 168 /\
    KeygenKeccak1600Spec.state_of_barray res.`2 =
      HAETAE_Keccak1600.keccak_f1600_lanes
        (KeygenKeccak1600Spec.state_of_barray state0)] = 1%r.
proof.
by conseq squeeze128_ll
          (squeeze128_rate_block out0 outoff0 state0).
qed.

lemma squeeze256_rate_block_pll
    (out0 : BArray1024.t) (outoff0 : W64.t)
    (state0 : BArray200.t) :
  phoare [KeygenSamplerCallersTarget.M.__poly_sample_squeeze256 :
    outp = out0 /\ outoff = outoff0 /\ sp_0 = state0 /\
    W64.to_uint outoff0 + 136 <= BArray1024.size
    ==>
    KeygenShakeStreamSpec.rate_block_matches
      res.`1 (W64.to_uint outoff0) res.`2 136 /\
    KeygenShakeStreamSpec.rate_block_frame
      out0 res.`1 (W64.to_uint outoff0) 136 /\
    KeygenKeccak1600Spec.state_of_barray res.`2 =
      HAETAE_Keccak1600.keccak_f1600_lanes
        (KeygenKeccak1600Spec.state_of_barray state0)] = 1%r.
proof.
by conseq squeeze256_ll
          (squeeze256_rate_block out0 outoff0 state0).
qed.

end TargetKeygenShakeStream.
