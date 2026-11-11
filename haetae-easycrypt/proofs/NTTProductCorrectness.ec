require import AllCore IntDiv List StdOrder.
from Jasmin require import JModel_x86.
require import ApiTarget NTTProductTarget BArray1024 BArray8192.
require import NTTVectorTotal NTTPointwiseCorrectness NTTVectorSpec NTTTransformAlgebra NTTFullSpec NTT_Fq Fq Rq GFq Array256.
import NTTVectorSpec Zq.

theory NTTProductCorrectness.
module Api = ApiTarget.M(ApiTarget.Syscall).
module Target = NTTProductTarget.M.

lemma product_fqmul_equiv :
  equiv [Target.__fqmul ~ Api.__fqmul : ={a,b} ==> ={res}].
proof. proc; inline Target.__montgomery_reduce Api.__montgomery_reduce; sim. qed.

lemma product_pointwise_equiv :
  equiv [Target._polyvec_poly_pointwise ~ Api._polyvec_poly_pointwise :
    ={rp,up,vp,count} ==> ={res}].
proof.
proc.
inline Target.__fqmul Target.__montgomery_reduce Api.__fqmul Api.__montgomery_reduce.
sim.
qed.

lemma product_invntt_equiv :
  equiv [Target._polyvec_invntt ~ Api._polyvec_invntt :
    ={xp,count} ==> ={res}].
proof.
proc.
inline Target.__fqmul Target.__montgomery_reduce Api.__fqmul Api.__montgomery_reduce.
sim.
qed.

lemma product_pointwise_ll : islossless Target._polyvec_poly_pointwise.
proof.
by conseq product_pointwise_equiv NTTPointwiseCorrectness.polyvec_pointwise_ll => /#.
qed.

lemma product_pointwise_total initial up0 vp0 ps q n :
  vector_repr up0 ps n 24 => NTT_Fq.poly_repr_bound vp0 q 24 =>
  phoare[Target._polyvec_poly_pointwise :
    rp=initial /\ up=up0 /\ vp=vp0 /\ count=W64.of_int n ==>
    vector_repr res (List.map (fun p => NTTPointwiseCorrectness.montgomery_pointwise p q) ps) n 17 /\
    inactive_unchanged initial res n] = 1%r.
proof.
move=> hu hv.
by conseq product_pointwise_equiv
  (NTTPointwiseCorrectness.polyvec_pointwise_field_total initial up0 vp0 ps q n hu hv) => /#.
qed.

lemma montgomery_pointwise_scale p q :
  NTTPointwiseCorrectness.montgomery_pointwise p q =
  NTTTransformAlgebra.scale (inv NTT_Fq.R) (NTTTransformAlgebra.pointwise p q).
proof.
apply Array256.ext_eq => i hi.
rewrite NTTPointwiseCorrectness.montgomery_pointwiseE 1:hi
  NTTTransformAlgebra.scaleE 1:hi NTTTransformAlgebra.pointwiseE 1:hi.
by ring.
qed.

lemma product_inverse_identity p q :
  NTT_Fq.array256_mont (NTTFullSpec.full_invntt
    (NTTPointwiseCorrectness.montgomery_pointwise
      (NTTFullSpec.full_ntt p) (NTTFullSpec.full_ntt q))) = p &* q.
proof.
by rewrite montgomery_pointwise_scale NTTTransformAlgebra.full_ntt_product_pipeline.
qed.

lemma product_bound_ready a ps n : vector_repr a ps n 17 => vector_repr a ps n 18.
proof.
move=> [hn [hs hp]]; split; first exact hn.
split; first exact hs.
move=> k hk.
have [he hb] := hp k hk.
split; first exact he.
rewrite /NTT_Fq.barray256_bound => i hi.
have := hb i hi.
by rewrite /Fq.bw32 /=; smt().
qed.

lemma product_vector_identity ps q :
  List.map (fun p => NTT_Fq.array256_mont (NTTFullSpec.full_invntt p))
    (List.map (fun p => NTTPointwiseCorrectness.montgomery_pointwise p (NTTFullSpec.full_ntt q))
      (List.map NTTFullSpec.full_ntt ps)) =
  List.map (fun p => p &* q) ps.
proof.
elim: ps => [|p ps ih] //=.
by rewrite product_inverse_identity ih.
qed.

lemma product_invntt_total initial ps n :
  vector_repr initial ps n 18 =>
  phoare[Target._polyvec_invntt : xp=initial /\ count=W64.of_int n ==>
    vector_repr res (map NTTVectorTotal.inverse_value ps) n 16 /\
    inactive_unchanged initial res n] = 1%r.
proof.
move=> hp.
by conseq product_invntt_equiv (NTTVectorTotal.api_vector_invntt_total18 initial ps n hp) => /#.
qed.

lemma product_invntt_total_pre initial ps n :
  phoare[Target._polyvec_invntt :
    xp=initial /\ count=W64.of_int n /\ vector_repr initial ps n 18 ==>
    vector_repr res (map NTTVectorTotal.inverse_value ps) n 16 /\
    inactive_unchanged initial res n] = 1%r.
proof.
by conseq product_invntt_equiv (NTTVectorTotal.api_vector_invntt_total18_pre initial ps n) => /#.
qed.

lemma sign_compute_cs2_total initial s2hat chat ps c n :
  vector_repr s2hat (map NTTFullSpec.full_ntt ps) n 24 =>
  NTT_Fq.poly_repr_bound chat (NTTFullSpec.full_ntt c) 24 =>
  phoare[Target.sign_compute_cs2_jazz :
    cs2p=initial /\ s2p=s2hat /\ chatp=chat /\ count=W64.of_int n ==>
    vector_repr res (map (fun p => p &* c) ps) n 16 /\
    inactive_unchanged initial res n] = 1%r.
proof.
move=> hs hc.
proc.
ecall (product_invntt_total_pre cs2p
  (map (fun p => NTTPointwiseCorrectness.montgomery_pointwise p (NTTFullSpec.full_ntt c))
    (map NTTFullSpec.full_ntt ps)) n).
wp.
ecall (product_pointwise_total initial s2hat chat (map NTTFullSpec.full_ntt ps)
  (NTTFullSpec.full_ntt c) n hs hc).
wp; skip.
rewrite /protect_ptr /protect_64 /=.
move=> &hr hpre.
split; first exact hpre.
move=> _ mid [hm hf].
split.
+ split; first smt().
  exact (product_bound_ready _ _ _ hm).
move=> _ output [hout hframe].
split.
+ by move: hout; rewrite /NTTVectorTotal.inverse_value product_vector_identity.
+ exact (inactive_unchanged_trans initial mid output n hf hframe).
call product_pointwise_ll; islossless.
qed.

end NTTProductCorrectness.
