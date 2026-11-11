require import AllCore IntDiv List Ring StdOrder.
require import Array256 GFq Rq.
import Zq IntOrder.

theory NTTProductExpansion.

lemma product_fold_sum (p q:Rq.poly) (i:int) (xs:int list) :
  foldr (fun k ci =>
    if 0 <= i-k then ci + p.[k]*q.[i-k]
    else ci - p.[k]*q.[256+(i-k)]) Zq.zero xs =
  Rq.BigDom.BAdd.big predT (fun k =>
    if 0 <= i-k then p.[k]*q.[i-k]
    else -(p.[k]*q.[256+(i-k)])) xs.
proof.
elim: xs => [|k xs ih].
+ by rewrite /= Rq.BigDom.BAdd.big_nil.
rewrite /= Rq.BigDom.BAdd.big_consT ih.
case (0 <= i-k) => h /=.
+ by rewrite h /= ZqRing.addrC.
+ by rewrite h /= ZqRing.addrC.
qed.

lemma rq_mul_coeff (p q:Rq.poly) i : 0 <= i < 256 =>
  (p &* q).[i] =
  Rq.BigDom.BAdd.bigi predT (fun k =>
    if 0 <= i-k then p.[k]*q.[i-k]
    else -(p.[k]*q.[256+(i-k)])) 0 256.
proof.
move=> hi.
rewrite /(&*) Array256.initiE 1:hi.
rewrite /= product_fold_sum.
by [].
qed.

end NTTProductExpansion.
