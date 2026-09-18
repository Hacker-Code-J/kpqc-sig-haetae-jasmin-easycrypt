require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import ApiTarget VerifyTarget ApiBoundaryTarget ApiBoundaryCorrectness.

(* These are the helpers reached from the extracted public entry points.
   In particular, signing uses _sf_prepare_pre_raw, whose word counter and
   advancing address differ from the unused _api_prepare_pre_raw helper. *)
theory ProductionApiCorrectness.

module Sign = ApiTarget.M(ApiTarget.Syscall).
module Verify = VerifyTarget.M.
module Boundary = ApiBoundaryTarget.M.

import ApiBoundaryCorrectness.

lemma production_sf_prepare_pre_raw_correct
    (before : BArray257.t) (mem0 : global_mem_t) (base n : int) :
  hoare [Sign._sf_prepare_pre_raw :
    prep = before /\ Glob.mem = mem0 /\ ctxaddr = W64.of_int base /\
    ctxlen = W64.of_int n /\ 0 <= n <= 255 /\ canonical_region base n
    ==>
    Glob.mem = mem0 /\ prepared_prefix before res mem0 base n n].
proof.
proc.
while (Glob.mem = mem0 /\ ctxlen = W64.of_int n /\
       ctxaddr = W64.of_int (base + W64.to_uint i) /\
       0 <= n <= 255 /\ canonical_region base n /\
       0 <= W64.to_uint i <= n /\
       prepared_prefix before prep mem0 base n (W64.to_uint i)).
+ auto => /> &hr hn0 hn255 hb0 hbmax hn0b hsum hi0 hin hpref hguard.
  have hi_lt : W64.to_uint i{hr} < n by
    move: hguard; rewrite W64.ultE W64.to_uint_small 1:/#.
  have hnext : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1 by
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  have hread : W64.to_uint (W64.of_int (base + W64.to_uint i{hr})) =
      base + W64.to_uint i{hr} by
    rewrite W64.to_uint_small 1:/#.
  rewrite hnext hread.
  split; first smt().
  split; first smt().
  rewrite /prepared_prefix => j hj.
  rewrite BArray257.get_set_if.
  have hjold := hpref j hj.
  case: (j = W64.to_uint i{hr} + 1) => hjnew; smt().
auto => /> hn0 hn255 hb0 hbmax hn0b hsum.
split.
+ rewrite /prepared_prefix context_length_byte 1:/# => j hj.
  rewrite BArray257.get_set_if; smt().
+ move=> i after hdone hi0 hin hpref.
  have heq : W64.to_uint i = n by
    move: hdone; rewrite W64.ultE W64.to_uint_small 1:/#; smt().
  by move: hpref; rewrite heq.
qed.

lemma production_sf_prepare_pre_raw_ll : islossless Sign._sf_prepare_pre_raw.
proof.
proc.
while (W64.to_uint i <= W64.to_uint ctxlen)
      (W64.to_uint ctxlen - W64.to_uint i).
+ move=> z; auto => /> &hr hi hguard.
  have /= hlen := W64.to_uint_cmp ctxlen{hr}.
  rewrite W64.ultE in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
auto => />.
move=> &hr; split; first smt(W64.to_uint_cmp).
move=> i hi hvariant; rewrite W64.ultE; smt().
qed.

lemma production_sf_prepare_pre_raw_total_correct
    (before : BArray257.t) (mem0 : global_mem_t) (base n : int) :
  phoare [Sign._sf_prepare_pre_raw :
    prep = before /\ Glob.mem = mem0 /\ ctxaddr = W64.of_int base /\
    ctxlen = W64.of_int n /\ 0 <= n <= 255 /\ canonical_region base n
    ==>
    Glob.mem = mem0 /\ prepared_prefix before res mem0 base n n] = 1%r.
proof.
by conseq production_sf_prepare_pre_raw_ll
  (production_sf_prepare_pre_raw_correct before mem0 base n).
qed.

lemma production_sign_backward_copy_equiv :
  equiv [Sign._api_copy_addr_to_addr_backward ~ Boundary._api_copy_addr_to_addr_backward :
    ={Glob.mem, dstp, srcp, len} ==> ={Glob.mem, res}].
proof. proc; sim. qed.

lemma production_sign_backward_copy_correct
    (mem0 : global_mem_t) (dst0 src0 size : W64.t) :
  hoare [Sign._api_copy_addr_to_addr_backward :
    Glob.mem = mem0 /\ dstp = dst0 /\ srcp = src0 /\ len = size /\
    canonical_region (W64.to_uint dst0) (W64.to_uint size) /\
    canonical_region (W64.to_uint src0) (W64.to_uint size) /\
    backward_alias (W64.to_uint dst0) (W64.to_uint src0) (W64.to_uint size)
    ==>
    res = dst0 /\
    copied_bytes mem0 Glob.mem (W64.to_uint dst0) (W64.to_uint src0) (W64.to_uint size) /\
    byte_frame mem0 Glob.mem (W64.to_uint dst0) (W64.to_uint size)].
proof.
by conseq production_sign_backward_copy_equiv
  (api_copy_addr_to_addr_backward_correct mem0 dst0 src0 size) => /#.
qed.

lemma production_sign_backward_copy_ll :
  islossless Sign._api_copy_addr_to_addr_backward.
proof.
by conseq production_sign_backward_copy_equiv api_copy_addr_to_addr_backward_ll => /#.
qed.

lemma production_sign_backward_copy_total_correct
    (mem0 : global_mem_t) (dst0 src0 size : W64.t) :
  phoare [Sign._api_copy_addr_to_addr_backward :
    Glob.mem = mem0 /\ dstp = dst0 /\ srcp = src0 /\ len = size /\
    canonical_region (W64.to_uint dst0) (W64.to_uint size) /\
    canonical_region (W64.to_uint src0) (W64.to_uint size) /\
    backward_alias (W64.to_uint dst0) (W64.to_uint src0) (W64.to_uint size)
    ==>
    res = dst0 /\
    copied_bytes mem0 Glob.mem (W64.to_uint dst0) (W64.to_uint src0) (W64.to_uint size) /\
    byte_frame mem0 Glob.mem (W64.to_uint dst0) (W64.to_uint size)] = 1%r.
proof.
by conseq production_sign_backward_copy_ll
  (production_sign_backward_copy_correct mem0 dst0 src0 size).
qed.

lemma production_verify_zero_equiv :
  equiv [Verify._api_zero_raw_len64 ~ Boundary._api_zero_raw_len64 :
    ={Glob.mem, dstp, len} ==> ={Glob.mem, res}].
proof. proc; sim. qed.

lemma production_verify_zero_correct
    (mem0 : global_mem_t) (base : int) (size : W64.t) :
  hoare [Verify._api_zero_raw_len64 :
    Glob.mem = mem0 /\ dstp = base /\ len = size /\
    canonical_region base (W64.to_uint size)
    ==>
    res = base /\ zero_prefix mem0 Glob.mem base (W64.to_uint size) /\
    byte_frame mem0 Glob.mem base (W64.to_uint size)].
proof.
by conseq production_verify_zero_equiv (api_zero_raw_len64_correct mem0 base size) => /#.
qed.

lemma production_verify_zero_ll : islossless Verify._api_zero_raw_len64.
proof. by conseq production_verify_zero_equiv api_zero_raw_len64_ll => /#. qed.

lemma production_verify_zero_total_correct
    (mem0 : global_mem_t) (base : int) (size : W64.t) :
  phoare [Verify._api_zero_raw_len64 :
    Glob.mem = mem0 /\ dstp = base /\ len = size /\
    canonical_region base (W64.to_uint size)
    ==>
    res = base /\ zero_prefix mem0 Glob.mem base (W64.to_uint size) /\
    byte_frame mem0 Glob.mem base (W64.to_uint size)] = 1%r.
proof.
by conseq production_verify_zero_ll (production_verify_zero_correct mem0 base size).
qed.

end ProductionApiCorrectness.
