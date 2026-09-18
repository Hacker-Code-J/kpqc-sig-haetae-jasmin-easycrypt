require import AllCore IntDiv.

from Jasmin require import JModel_x86.
require import ApiBoundaryTarget.

(* These contracts concern generated source-level API helpers. The generic
   _api_prepare_pre_raw is currently unused; production signing uses the
   distinct _sf_prepare_pre_raw covered by ProductionApiCorrectness.
   Global memory is the Jasmin total byte map.  Canonical ranges below expose
   the address/no-wrap obligations required by callers. *)
theory ApiBoundaryCorrectness.

module Api = ApiBoundaryTarget.M.

op canonical_region (base len : int) : bool =
  0 <= base < W64.modulus /\ 0 <= len /\ base + len <= W64.modulus.

op byte_frame (before after : global_mem_t) (base len : int) : bool =
  forall a, !(base <= a < base + len) =>
    loadW8 after a = loadW8 before a.

op prepared_prefix (before after : BArray257.t)
    (mem : global_mem_t) (base len copied : int) : bool =
  forall j, 0 <= j < 257 =>
    BArray257.get8 after j =
      if j = 0 then W8.of_int len
      else if 1 <= j <= copied then loadW8 mem (base + j - 1)
      else BArray257.get8 before j.

lemma context_length_byte (len : int) :
  0 <= len <= 255 => truncateu8 (W64.of_int len) = W8.of_int len.
proof.
move=> hlen.
rewrite W8.to_uint_eq.
rewrite W8u8.to_uint_truncateu8 !W64.of_uintK !W8.of_uintK /=.
smt(IntDiv.modz_small).
qed.

lemma context_index (i : int) :
  0 <= i < 255 =>
  W64.to_uint (W64.of_int 1 + W64.of_int i) = 1 + i.
proof.
move=> hi.
have hu : W64.to_uint (W64.of_int i) = i by
  rewrite W64.of_uintK /=; smt(IntDiv.modz_small).
rewrite W64.to_uintD_small 1:/# hu W64.to_uint1.
trivial.
qed.

lemma api_prepare_pre_raw_correct
    (before : BArray257.t) (mem0 : global_mem_t) (base n : int) :
  hoare [Api._api_prepare_pre_raw :
    prep = before /\ Glob.mem = mem0 /\ ctxp = base /\ ctxlen = n /\
    0 <= n <= 255 /\ canonical_region base n
    ==>
    Glob.mem = mem0 /\ prepared_prefix before res mem0 base n n].
proof.
proc.
while (Glob.mem = mem0 /\ ctxp = base /\ ctxlen = n /\
       0 <= n <= 255 /\ 0 <= i <= n /\
       prepared_prefix before prep mem0 base n i).
+ auto => /> &hr hn0 hn255 hi0 hin hpref hguard.
  split; first smt().
  rewrite /prepared_prefix => j hj.
  rewrite BArray257.get_set_if.
  rewrite W64.of_uintK /=.
  have hidx : (1 + i{hr}) %% 18446744073709551616 = 1 + i{hr} by smt(IntDiv.modz_small).
  rewrite hidx.
  have hjold := hpref j hj.
  case: (j = 1 + i{hr}) => hjnew; smt().
auto => /> hn0 hn255 hb0 hbmax hn0b hsum.
split.
+ rewrite /prepared_prefix context_length_byte 1:/# => j hj.
  rewrite BArray257.get_set_if; smt().
+ move=> i after hdone hi0 hin hpref.
  have heq : i = n by smt().
  by move: hpref; rewrite heq.
qed.

lemma api_prepare_pre_raw_ll : islossless Api._api_prepare_pre_raw.
proof.
proc.
while (0 <= i) (ctxlen - i).
+ by move=> z; auto => />; smt().
auto => />; smt().
qed.

op zero_prefix (before after : global_mem_t) (base len : int) : bool =
  forall a, loadW8 after a =
    if base <= a < base + len then W8.zero else loadW8 before a.

lemma zero_prefix_step (before mem : global_mem_t) (base i : int) :
  0 <= i => zero_prefix before mem base i =>
  zero_prefix before (storeW8 mem (base + i) W8.zero) base (i + 1).
proof.
move=> hi hpref.
rewrite /zero_prefix => a.
have ha := hpref a.
rewrite /loadW8 /storeW8 get_setE.
rewrite /loadW8 in ha.
smt().
qed.

lemma zero_prefix_frame (before after : global_mem_t) (base len : int) :
  zero_prefix before after base len => byte_frame before after base len.
proof. by rewrite /zero_prefix /byte_frame; smt(). qed.

lemma api_zero_raw_len64_correct
    (mem0 : global_mem_t) (base : int) (size : W64.t) :
  hoare [Api._api_zero_raw_len64 :
    Glob.mem = mem0 /\ dstp = base /\ len = size /\
    canonical_region base (W64.to_uint size)
    ==>
    res = base /\ zero_prefix mem0 Glob.mem base (W64.to_uint size) /\
    byte_frame mem0 Glob.mem base (W64.to_uint size)].
proof.
proc.
while (dstp = base /\ dstbase = W64.of_int base /\ len = size /\
       canonical_region base (W64.to_uint size) /\
       0 <= W64.to_uint i <= W64.to_uint size /\
       zero_prefix mem0 Glob.mem base (W64.to_uint i)).
+ auto => /> &hr hb0 hbmax hs0 hsum hi0 hin hpref hguard.
  have hi_lt : W64.to_uint i{hr} < W64.to_uint size by
    move: hguard; rewrite W64.ultE.
  have hbase : W64.to_uint (W64.of_int base) = base by
    rewrite W64.of_uintK /=; smt(IntDiv.modz_small).
  have hsize := W64.to_uint_cmp size.
  rewrite /= in hsize.
  have hi_succ : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1 by
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  have haddr : W64.to_uint (W64.of_int base) + W64.to_uint i{hr} < W64.modulus by
    rewrite hbase /=; smt().
  have hadd := W64.to_uintD_small (W64.of_int base) i{hr} haddr.
  rewrite hbase in hadd.
  rewrite hi_succ hadd.
  split; first smt().
  exact (zero_prefix_step mem0 Glob.mem{hr} base (W64.to_uint i{hr}) hi0 hpref).
auto => /> hb0 hbmax hs0 hsum.
split.
+ rewrite /zero_prefix; smt().
+ move=> mem i hdone hi0 hin hpref.
  have heq : W64.to_uint i = W64.to_uint size by
    move: hdone; rewrite W64.ultE; smt().
  have hfinal : zero_prefix mem0 mem base (W64.to_uint size) by
    move: hpref; rewrite heq.
  split; first exact hfinal.
  exact (zero_prefix_frame mem0 mem base (W64.to_uint size) hfinal).
qed.

lemma api_zero_raw_len64_ll : islossless Api._api_zero_raw_len64.
proof.
proc.
while (W64.to_uint i <= W64.to_uint len)
      (W64.to_uint len - W64.to_uint i).
+ move=> z.
  auto => /> &hr hi hguard.
  have hlen := W64.to_uint_cmp len{hr}.
  rewrite /= in hlen.
  rewrite W64.ultE in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  smt().
auto => />.
move=> &hr; split; first smt(W64.to_uint_cmp).
move=> i hi hvariant; rewrite W64.ultE; smt().
qed.

(* Backward copying permits identical buffers, an overlapping destination
   above the source, or a disjoint destination below the source. *)
op backward_alias (dst src len : int) : bool =
  src <= dst \/ dst + len <= src.

op copied_suffix (before after : global_mem_t)
    (dst src len pending : int) : bool =
  forall a, loadW8 after a =
    if dst + pending <= a < dst + len
    then loadW8 before (src + a - dst)
    else loadW8 before a.

op copied_bytes (before after : global_mem_t) (dst src len : int) : bool =
  forall j, 0 <= j < len =>
    loadW8 after (dst + j) = loadW8 before (src + j).

lemma backward_copy_step
    (before mem : global_mem_t) (dst src len i : int) :
  1 <= i <= len => backward_alias dst src len =>
  copied_suffix before mem dst src len i =>
  copied_suffix before
    (storeW8 mem (dst + (i - 1)) (loadW8 mem (src + (i - 1))))
    dst src len (i - 1).
proof.
move=> hi halias hpref.
have hread : loadW8 mem (src + (i - 1)) = loadW8 before (src + (i - 1)).
+ have h := hpref (src + (i - 1)).
  have hout : !(dst + i <= src + (i - 1) < dst + len) by
    move: halias; rewrite /backward_alias; smt().
  by move: h; rewrite hout.
rewrite /copied_suffix => a.
rewrite /loadW8 /storeW8 get_setE.
have ha := hpref a.
rewrite /loadW8 in ha.
rewrite /loadW8 in hread.
smt().
qed.

lemma copied_suffix_complete
    (before after : global_mem_t) (dst src len : int) :
  copied_suffix before after dst src len 0 =>
  copied_bytes before after dst src len /\ byte_frame before after dst len.
proof.
rewrite /copied_suffix /copied_bytes /byte_frame.
smt().
qed.

lemma api_copy_addr_to_addr_backward_correct
    (mem0 : global_mem_t) (dst0 src0 size : W64.t) :
  hoare [Api._api_copy_addr_to_addr_backward :
    Glob.mem = mem0 /\ dstp = dst0 /\ srcp = src0 /\ len = size /\
    canonical_region (W64.to_uint dst0) (W64.to_uint size) /\
    canonical_region (W64.to_uint src0) (W64.to_uint size) /\
    backward_alias (W64.to_uint dst0) (W64.to_uint src0) (W64.to_uint size)
    ==>
    res = dst0 /\
    copied_bytes mem0 Glob.mem (W64.to_uint dst0) (W64.to_uint src0) (W64.to_uint size) /\
    byte_frame mem0 Glob.mem (W64.to_uint dst0) (W64.to_uint size)].
proof.
proc.
while (dstp = dst0 /\ srcp = src0 /\ len = size /\
       canonical_region (W64.to_uint dst0) (W64.to_uint size) /\
       canonical_region (W64.to_uint src0) (W64.to_uint size) /\
       backward_alias (W64.to_uint dst0) (W64.to_uint src0) (W64.to_uint size) /\
       0 <= W64.to_uint i <= W64.to_uint size /\
       copied_suffix mem0 Glob.mem (W64.to_uint dst0) (W64.to_uint src0)
         (W64.to_uint size) (W64.to_uint i)).
+ auto => /> &hr hd0 hdmax hn0 hds hs0 hsmax hns hss halias hi0 hin hpref hguard.
  have hi_pos : 0 < W64.to_uint i{hr} by
    move: hguard; rewrite W64.to_uint_eq W64.to_uint0; smt().
  have hle : W64.one \ule i{hr} by
    rewrite W64.uleE W64.to_uint1; smt().
  have hpred : W64.to_uint (i{hr} - W64.one) = W64.to_uint i{hr} - 1 by
    rewrite W64.to_uintB 1:hle W64.to_uint1.
  have hsaddr : W64.to_uint src0 + W64.to_uint (i{hr} - W64.one) < W64.modulus by
    rewrite hpred /=; smt().
  have hdaddr : W64.to_uint dst0 + W64.to_uint (i{hr} - W64.one) < W64.modulus by
    rewrite hpred /=; smt().
  rewrite (W64.to_uintD_small src0 _ hsaddr)
          (W64.to_uintD_small dst0 _ hdaddr) hpred.
  split; first smt().
  apply backward_copy_step; smt().
auto => /> hd0 hdmax hn0 hds hs0 hsmax hns hss halias.
split.
+ rewrite /copied_suffix; smt().
+ move=> mem _ hpref.
  exact (copied_suffix_complete mem0 mem (W64.to_uint dst0)
    (W64.to_uint src0) (W64.to_uint size) hpref).
qed.

lemma api_copy_addr_to_addr_backward_ll :
  islossless Api._api_copy_addr_to_addr_backward.
proof.
proc.
while (true) (W64.to_uint i).
+ move=> z; auto => /> &hr hguard.
  have hi := W64.to_uint_cmp i{hr}.
  have hpos : 0 < W64.to_uint i{hr} by
    move: hguard; rewrite W64.to_uint_eq W64.to_uint0; smt().
  have hle : W64.one \ule i{hr} by
    rewrite W64.uleE W64.to_uint1; smt().
  rewrite W64.to_uintB 1:hle W64.to_uint1; smt().
auto => />; smt(W64.to_uint_cmp W64.to_uint_eq W64.to_uint0).
qed.

(* In-place attached signing shifts the original message above the reserved
   signature prefix.  The source and destination ranges may overlap. *)
lemma api_copy_signature_prefix_shift
    (mem0 : global_mem_t) (base signaturelen : int) (size : W64.t) :
  0 <= signaturelen =>
  canonical_region base (W64.to_uint size) =>
  canonical_region (base + signaturelen) (W64.to_uint size) =>
  hoare [Api._api_copy_addr_to_addr_backward :
    Glob.mem = mem0 /\ dstp = W64.of_int (base + signaturelen) /\
    srcp = W64.of_int base /\ len = size
    ==>
    res = W64.of_int (base + signaturelen) /\
    copied_bytes mem0 Glob.mem (base + signaturelen) base (W64.to_uint size) /\
    byte_frame mem0 Glob.mem (base + signaturelen) (W64.to_uint size)].
proof.
move=> hsig hsrc hdst.
have hs : W64.to_uint (W64.of_int base) = base.
+ rewrite W64.to_uint_small //; move: hsrc; rewrite /canonical_region; smt().
have hd : W64.to_uint (W64.of_int (base + signaturelen)) = base + signaturelen.
+ rewrite W64.to_uint_small //; move: hdst; rewrite /canonical_region; smt().
move: hsrc hdst; rewrite /canonical_region => hsrc hdst.
conseq (api_copy_addr_to_addr_backward_correct mem0
  (W64.of_int (base + signaturelen)) (W64.of_int base) size) => />.
+ rewrite hs hd /backward_alias; smt().
+ by rewrite hs hd.
qed.

end ApiBoundaryCorrectness.
