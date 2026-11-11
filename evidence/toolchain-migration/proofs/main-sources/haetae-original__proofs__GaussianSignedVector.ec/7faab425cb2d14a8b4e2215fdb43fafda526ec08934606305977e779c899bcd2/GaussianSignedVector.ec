require import AllCore List Distr DList DBool SDist StdRing StdOrder.
require import GaussianSignedTarget Gaussian76Spec SigmaConditionalSpec
  GaussianIidNormalization GaussianIidDistribution.
import RField RealOrder.

(* Coordinatewise combination, used below for an independent fair sign
   vector and an unsigned-magnitude vector. *)
op gsv_combine ['a 'b 'c] (h : 'a -> 'b -> 'c)
    (xs : 'a list) (ys : 'b list) : 'c list =
  map (fun (xy : 'a * 'b) => h xy.`1 xy.`2) (zip xs ys).

lemma gsv_combine_cons ['a 'b 'c] (h : 'a -> 'b -> 'c) a xs b ys :
  gsv_combine h (a::xs) (b::ys) = h a b :: gsv_combine h xs ys.
proof. by rewrite /gsv_combine /=. qed.

lemma gsv_combine_iid ['a 'b 'c]
    (da : 'a distr) (db : 'b distr) (h : 'a -> 'b -> 'c) (n : int) :
  0 <= n =>
  dmap (dlist da n `*` dlist db n)
    (fun (xy : 'a list * 'b list) => gsv_combine h xy.`1 xy.`2) =
  dlist (dmap (da `*` db) (fun (ab : 'a * 'b) => h ab.`1 ab.`2)) n.
proof.
  pose dc := dmap (da `*` db) (fun (ab : 'a * 'b) => h ab.`1 ab.`2).
  rewrite -/dc.
  elim: n => [|n hn ih].
  + by rewrite !dlist0 1..3:// dprod_dunit dmap_dunit /gsv_combine /=.
  have hcross := dprod_dmap_cross da (dlist da n) db (dlist db n)
    (fun (ax : 'a * 'a list) => ax.`1 :: ax.`2)
    (fun (bt : 'b * 'b list) => bt.`1 :: bt.`2)
    (gsv_combine h)
    (fun (ab : 'a * 'b) => h ab.`1 ab.`2)
    (fun (xy : 'a list * 'b list) => gsv_combine h xy.`1 xy.`2)
    (fun (c : 'c) (cs : 'c list) => c::cs) _.
  + by move=> a xs b ys; rewrite /= gsv_combine_cons.
  rewrite -/dc in hcross.
  rewrite (dlistS da n hn) (dlistS db n hn) (dlistS dc n hn) /=.
  rewrite (dmap_dprodE _ _ (fun (xy : 'a list * 'b list) =>
    gsv_combine h xy.`1 xy.`2)) /= hcross ih.
  by rewrite (dmap_dprodE dc (dlist dc n)
    (fun (cx : 'c * 'c list) => cx.`1 :: cx.`2)) /=.
qed.

op gsv_apply (bits : bool list) (magnitudes : int list) : int list =
  gsv_combine gst_apply bits magnitudes.

(* Independence is explicit in this product. The operational proof must
   establish that product law for its own sign and magnitude observations. *)
op gsv_distribution (n : int) (magnitudes : int list distr) : int list distr =
  dmap (dlist dbool n `*` magnitudes)
    (fun (bm : bool list * int list) => gsv_apply bm.`1 bm.`2).

op gsv_actual : int list distr = gsv_distribution 256 gid_target.

lemma gsv_apply_size bits magnitudes :
  size (gsv_apply bits magnitudes) = min (size bits) (size magnitudes).
proof. by rewrite /gsv_apply /gsv_combine size_map size_zip. qed.

lemma gsv_apply_nth bits magnitudes i :
  size bits = size magnitudes => 0 <= i < size magnitudes =>
  nth 0 (gsv_apply bits magnitudes) i =
    gst_apply (nth false bits i) (nth 0 magnitudes i).
proof.
  move=> hsize hi; rewrite /gsv_apply /gsv_combine.
  rewrite (nth_map (false,0)) 1:size_zip 1:/#.
  by rewrite (nth_zip false 0 bits magnitudes i hsize) /=.
qed.

lemma gsv_distribution_iid (d : int distr) (n : int) : 0 <= n =>
  gsv_distribution n (dlist d n) = dlist (gst_signed_distribution d) n.
proof.
  move=> hn; rewrite /gsv_distribution /gsv_apply /gst_signed_distribution.
  exact (gsv_combine_iid dbool d gst_apply n hn).
qed.

lemma gsv_distribution_ll n (d : int list distr) : is_lossless d =>
  is_lossless (gsv_distribution n d).
proof.
  move=> hd; rewrite /gsv_distribution; apply dmap_ll; apply dprod_ll_auto.
  + apply dlist_ll; exact dbool_ll.
  exact hd.
qed.

lemma gsv_distribution_contraction n (d e : int list distr) :
  sdist (gsv_distribution n d) (gsv_distribution n e) <= sdist d e.
proof.
  have hw : weight (dlist dbool n) = 1%r by apply dlist_ll; exact dbool_ll.
  have hprod : sdist (dlist dbool n `*` d) (dlist dbool n `*` e) = sdist d e.
  + by rewrite (sdist_dprodC (dlist dbool n) (dlist dbool n) d e)
      sdist_dprod2r hw /=.
  rewrite /gsv_distribution -hprod; exact (sdist_dmap _ _ _).
qed.

lemma gsv_actual_law p :
  gsv_actual = dlist (gst_signed_distribution (sc_actual_conditioned p)) 256.
proof.
  rewrite /gsv_actual (gii_target_conditioned p).
  by apply gsv_distribution_iid.
qed.

lemma gsv_actual_ll : is_lossless gsv_actual.
proof. rewrite /gsv_actual; apply gsv_distribution_ll; exact gii_target_ll. qed.

lemma gsv_ideal_iid n : 0 <= n =>
  gsv_distribution n (dlist g76_rounded n) = dlist gst_target n.
proof.
  move=> hn; by rewrite (gsv_distribution_iid g76_rounded n hn) -gst_target_eq.
qed.

lemma gsv_ideal_law :
  gsv_distribution 256 (dlist g76_rounded 256) = dlist gst_target 256.
proof. by apply gsv_ideal_iid. qed.

lemma gsv_target_ll : is_lossless (dlist gst_target 256).
proof. apply dlist_ll; exact gst_target_ll. qed.

lemma gsv_actual_gaussian &m :
  sdist gsv_actual (dlist gst_target 256) < 1%r/(2^31)%r.
proof.
  rewrite /gsv_actual -gsv_ideal_law.
  exact (ler_lt_trans _ _ _
    (gsv_distribution_contraction 256 gid_target (dlist g76_rounded 256))
    (gii_target_gaussian &m)).
qed.

lemma gsv_actual_gaussian_event (event : int list -> bool) &m :
  `|mu gsv_actual event - mu (dlist gst_target 256) event| < 1%r/(2^31)%r.
proof.
  exact (ler_lt_trans _ _ _ (sdist_upper_bound _ _ event) (gsv_actual_gaussian &m)).
qed.
