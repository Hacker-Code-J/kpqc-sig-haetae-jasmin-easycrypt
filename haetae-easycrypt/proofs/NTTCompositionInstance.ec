require import AllCore IntDiv List StdOrder.
from Jasmin require import JModel_x86.
require import BArray1024 BArray8192 Array256 GFq Rq NTT_Fq NTTFullSpec.
require import HpolyTarget ApiTarget NTTCorrectness NTTVectorSpec
  NTTPointwiseCorrectness NTTTransformAlgebra NTTComposition.

import Zq NTTVectorSpec.

theory NTTCompositionInstance.

op product_value (p:Rq.poly) : Rq.poly =
  NTTTransformAlgebra.scale (inv NTT_Fq.R) (NTTFullSpec.full_ntt p).

clone NTTComposition as Common with
  type polynomial <- Rq.poly,
  type coefficient_buffer <- BArray1024.t,
  type transform_buffer <- BArray1024.t,
  op polynomial_product <- Rq.(&*),
  op input_rep <- NTT_Fq.poly_repr,
  op forward_rep <- (fun x p => NTT_Fq.poly_repr x (NTTFullSpec.full_ntt p)),
  op product_rep <- (fun x p => NTT_Fq.poly_repr x (product_value p)),
  op output_rep <- NTT_Fq.poly_repr,
  op input_bound <- (fun x => NTT_Fq.barray256_bound x 16),
  op forward_bound <- (fun x => NTT_Fq.barray256_bound x 24),
  op inverse_bound <- (fun x => NTT_Fq.barray256_bound x 17),
  op output_bound <- (fun x => NTT_Fq.barray256_bound x 16).

module Api = ApiTarget.M(ApiTarget.Syscall).
module Kernels = {
  proc forward(x:BArray1024.t) : BArray1024.t = {
    var r:BArray1024.t;
    r <@ HpolyTarget.M._poly_ntt(x);
    return r;
  }
  proc multiply(x:BArray1024.t,y:BArray1024.t) : BArray1024.t = {
    var u,r:BArray8192.t;
    u <- put_block8192 witness 0 x;
    r <@ Api._polyvec_poly_pointwise(witness,u,y,W64.of_int 1);
    return block8192 r 0;
  }
  proc inverse(x:BArray1024.t) : BArray1024.t = {
    var r:BArray1024.t;
    r <@ HpolyTarget.M._poly_invntt(x);
    return r;
  }
}.

lemma singleton_repr x p s :
  NTT_Fq.poly_repr_bound x p s =>
  vector_repr (put_block8192 witness 0 x) [p] 1 s.
proof.
move=> hp; rewrite /vector_repr /=.
move=> k hk.
have -> : k=0 by smt().
by rewrite /= block8192_put_same.
qed.

lemma singleton_result r p s :
  vector_repr r [p] 1 s => NTT_Fq.poly_repr_bound (block8192 r 0) p s.
proof.
move=> [_ [_ hp]].
have := hp 0 _; first smt().
by rewrite /=.
qed.

lemma pointwise_total_pre initial up0 vp0 ps q n :
  phoare[Api._polyvec_poly_pointwise :
    rp=initial /\ up=up0 /\ vp=vp0 /\ count=W64.of_int n /\
    vector_repr up0 ps n 24 /\ NTT_Fq.poly_repr_bound vp0 q 24 ==>
    vector_repr res (map (fun p => NTTPointwiseCorrectness.montgomery_pointwise p q) ps) n 17 /\
    inactive_unchanged initial res n] = 1%r.
proof.
case (vector_repr up0 ps n 24) => hu; last by exfalso => /#.
case (NTT_Fq.poly_repr_bound vp0 q 24) => hv; last by exfalso => /#.
by conseq (NTTPointwiseCorrectness.polyvec_pointwise_field_total initial up0 vp0 ps q n hu hv) => /#.
qed.

lemma pointwise_product_value p q :
  NTTPointwiseCorrectness.montgomery_pointwise
    (NTTFullSpec.full_ntt p) (NTTFullSpec.full_ntt q) = product_value (p &* q).
proof.
rewrite /product_value NTTTransformAlgebra.full_ntt_mul.
apply Array256.ext_eq => i hi.
rewrite NTTPointwiseCorrectness.montgomery_pointwiseE 1:hi
  NTTTransformAlgebra.scaleE 1:hi NTTTransformAlgebra.pointwiseE 1:hi.
by ring.
qed.

lemma inverse_product_value p :
  NTT_Fq.array256_mont (NTTFullSpec.full_invntt (product_value p)) = p.
proof.
by rewrite /product_value NTTTransformAlgebra.full_invntt_mont_cancel
  NTTTransformAlgebra.full_invntt_full_ntt.
qed.

lemma forward_total p :
  phoare[Kernels.forward : NTT_Fq.poly_repr_bound x p 16 ==>
    NTT_Fq.poly_repr_bound res (NTTFullSpec.full_ntt p) 24] = 1%r.
proof.
proc; call (NTTCorrectness.target_poly_ntt_total p); skip; smt().
qed.

lemma multiply_total p q :
  phoare[Kernels.multiply :
    NTT_Fq.poly_repr_bound x (NTTFullSpec.full_ntt p) 24 /\
    NTT_Fq.poly_repr_bound y (NTTFullSpec.full_ntt q) 24 ==>
    NTT_Fq.poly_repr_bound res (product_value (p &* q)) 17] = 1%r.
proof.
proc.
ecall (pointwise_total_pre witness (put_block8192 witness 0 x) y
  [NTTFullSpec.full_ntt p] (NTTFullSpec.full_ntt q) 1).
wp; skip.
move=> &hr [hx hy].
rewrite /=.
split.
+ split; first exact (singleton_repr _ _ _ hx).
  exact hy.
move=> _ result [hr hf].
rewrite /= pointwise_product_value in hr.
exact (singleton_result result (product_value (p &* q)) 17 hr).
qed.

lemma inverse_total p :
  phoare[Kernels.inverse : NTT_Fq.poly_repr_bound x (product_value p) 17 ==>
    NTT_Fq.poly_repr_bound res p 16] = 1%r.
proof.
proc.
call (NTTCorrectness.target_poly_invntt_total18 (product_value p)).
skip; rewrite inverse_product_value.
move=> &hr [hp hb].
split; first by split; [exact hp|apply (NTT_Fq.barray256_bound_weaken _ 17 18); smt()].
smt().
qed.

lemma haetae_ntt_product_total p q :
  phoare[Common.Product(Kernels).run :
    NTT_Fq.poly_repr_bound x p 16 /\ NTT_Fq.poly_repr_bound y q 16 ==>
    NTT_Fq.poly_repr_bound res (p &* q) 16] = 1%r.
proof.
have hc := Common.composition_total Kernels p q _ _ _.
+ exact forward_total.
+ move=> a b; conseq (multiply_total a b) => /#.
+ exact inverse_total.
by conseq hc => /#.
qed.

end NTTCompositionInstance.
