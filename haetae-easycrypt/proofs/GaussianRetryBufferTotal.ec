require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import GaussianStreamBuffer GaussianStreamCorrectness GaussianRefillCorrectness
  SHAKEBlockSpec SHAKEBlockCorrectness SHAKEStreamSpec SHAKESeedInitCorrectness.
import SHAKEStreamSpec SHAKEBlockSpec.Word.

section.

(* Snapshot mutable arrays inside the total contract. Callers need only
   the fixed mathematical stream and block index as logical parameters. *)
local lemma gr_initial_squeeze_correct (iw : word_state) (blocks : int) :
  hoare [SHAKESeedInitCorrectness.Signer.__sample_full_squeeze256 :
    0 <= blocks < 49 /\ W64.to_uint outoff = 136*blocks /\
    word_state_of_barray sp_0 = shake_iterate iw blocks /\
    gs_buffer_segment (shake_stream_byte iw) outp 0 0 (136*blocks)
    ==>
    word_state_of_barray res.`2 = shake_iterate iw (blocks+1) /\
    gs_buffer_segment (shake_stream_byte iw) res.`1 0 0 (136*(blocks+1))].
proof.
  exists* outp, outoff, sp_0; elim* => before offset state.
  conseq (SHAKESeedInitCorrectness.shake_block_stream_correct iw blocks before offset state) => />.
  + move=> &hr hbounds hoff hstate hbuf; smt().
  move=> &hr hb0 hb49 hoff hstate hbuf result hbytes hframe hnext.
  have hbounds : 0 <= blocks < 49 by smt().
  apply (gs_initial_block_extend (shake_stream_byte iw) outp{hr} result.`1 blocks hbounds hbuf).
  + by move: hbytes; rewrite hoff.
  by move: hframe; rewrite hoff.
qed.

local lemma gr_carry_correct (stream : int -> W8.t) (blocks : int) :
  hoare [GaussianRefillCorrectness.Signer._sample_gauss_N_carry :
    49 <= blocks /\ signbytes = W64.of_int 32 /\
    off = W64.of_int (gs_stream_tail blocks) /\
    gs_tail_matches stream bufp (W64.to_uint bytecnt) (firstflag <> W64.zero) blocks
    ==>
    gs_buffer_segment stream res 0 (136*blocks-gs_stream_tail blocks)
      (gs_stream_tail blocks)].
proof.
  exists* bufp, bytecnt, firstflag; elim* => before available flag.
  conseq (GaussianRefillCorrectness.gauss_carry_correct before (W64.to_uint available)
    32 (gs_stream_tail blocks) (flag <> W64.zero)) => />.
  + move=> &hr hb hsign hoff h0 hbound hcap hmod hsegment.
    have hd := divz_eq (W64.to_uint bytecnt{hr}) 26.
    have hq := divz_ge0 (W64.to_uint bytecnt{hr}) 26 _; first smt().
    have hm := modz_cmp (W64.to_uint bytecnt{hr}) 26; smt().
  move=> &hr hb hsign hoff h0 hbound hcap hmod hsegment result hcarry.
  have htail : gs_tail_matches stream bufp{hr} (W64.to_uint bytecnt{hr})
    (firstflag{hr} <> W64.zero) blocks by rewrite /gs_tail_matches; smt().
  apply (gs_carry_prefix stream bufp{hr} result (W64.to_uint bytecnt{hr})
    (firstflag{hr} <> W64.zero) blocks htail).
  by rewrite hmod.
qed.

local lemma gr_refill_squeeze_correct (iw : word_state) (blocks : int) :
  hoare [SHAKESeedInitCorrectness.Signer.__sample_full_squeeze256 :
    49 <= blocks /\ W64.to_uint outoff = gs_stream_tail blocks /\
    word_state_of_barray sp_0 = shake_iterate iw blocks /\
    gs_buffer_segment (shake_stream_byte iw) outp 0
      (136*blocks-gs_stream_tail blocks) (gs_stream_tail blocks)
    ==>
    word_state_of_barray res.`2 = shake_iterate iw (blocks+1) /\
    gs_buffer_segment (fun j => shake_stream_byte iw (32+j)) res.`1 0
      (26*gs_stream_attempts blocks) (136+gs_stream_tail blocks) /\
    gs_tail_matches (shake_stream_byte iw) res.`1 (136+gs_stream_tail blocks)
      false (blocks+1)].
proof.
  exists* outp, outoff, sp_0; elim* => carried offset state.
  conseq (SHAKESeedInitCorrectness.shake_block_stream_correct iw blocks carried offset state) => />.
  + move=> &hr hb hoff hstate hcarry.
    have [_ ht] := gs_stream_bounds blocks hb; smt().
  move=> &hr hb hoff hstate hcarry result hbytes hframe hnext.
  have hbytes' : forall j, 0 <= j < 136 =>
    BArray8192.get8 result.`1 (gs_stream_tail blocks+j) =
      shake_stream_byte iw (136*blocks+j) by move: hbytes; rewrite hoff.
  have hframe' : SHAKEBlockSpec.rate_block_frame outp{hr} result.`1
    (gs_stream_tail blocks) 136 by move: hframe; rewrite hoff.
  have hsegment := gs_refill_segment (shake_stream_byte iw) outp{hr} result.`1
    blocks hb hcarry hbytes' hframe'.
  split; first exact (gs_refill_candidates (shake_stream_byte iw) result.`1 blocks hsegment).
  have htail := gs_refill_tail (shake_stream_byte iw) result.`1 blocks hb hsegment.
  move: htail; rewrite /gs_tail_matches /=; smt().
qed.

lemma gr_initial_squeeze_total (iw : word_state) (blocks : int) :
  phoare [SHAKESeedInitCorrectness.Signer.__sample_full_squeeze256 :
    0 <= blocks < 49 /\ W64.to_uint outoff = 136*blocks /\
    word_state_of_barray sp_0 = shake_iterate iw blocks /\
    gs_buffer_segment (shake_stream_byte iw) outp 0 0 (136*blocks)
    ==>
    word_state_of_barray res.`2 = shake_iterate iw (blocks+1) /\
    gs_buffer_segment (shake_stream_byte iw) res.`1 0 0 (136*(blocks+1))] = 1%r.
proof. by conseq SHAKEBlockCorrectness.squeeze256_ll (gr_initial_squeeze_correct iw blocks). qed.

lemma gr_carry_total (stream : int -> W8.t) (blocks : int) :
  phoare [GaussianRefillCorrectness.Signer._sample_gauss_N_carry :
    49 <= blocks /\ signbytes = W64.of_int 32 /\
    off = W64.of_int (gs_stream_tail blocks) /\
    gs_tail_matches stream bufp (W64.to_uint bytecnt) (firstflag <> W64.zero) blocks
    ==>
    gs_buffer_segment stream res 0 (136*blocks-gs_stream_tail blocks)
      (gs_stream_tail blocks)] = 1%r.
proof. by conseq GaussianRefillCorrectness.gauss_carry_lossless (gr_carry_correct stream blocks). qed.

lemma gr_refill_squeeze_total (iw : word_state) (blocks : int) :
  phoare [SHAKESeedInitCorrectness.Signer.__sample_full_squeeze256 :
    49 <= blocks /\ W64.to_uint outoff = gs_stream_tail blocks /\
    word_state_of_barray sp_0 = shake_iterate iw blocks /\
    gs_buffer_segment (shake_stream_byte iw) outp 0
      (136*blocks-gs_stream_tail blocks) (gs_stream_tail blocks)
    ==>
    word_state_of_barray res.`2 = shake_iterate iw (blocks+1) /\
    gs_buffer_segment (fun j => shake_stream_byte iw (32+j)) res.`1 0
      (26*gs_stream_attempts blocks) (136+gs_stream_tail blocks) /\
    gs_tail_matches (shake_stream_byte iw) res.`1 (136+gs_stream_tail blocks)
      false (blocks+1)] = 1%r.
proof. by conseq SHAKEBlockCorrectness.squeeze256_ll (gr_refill_squeeze_correct iw blocks). qed.

end section.
