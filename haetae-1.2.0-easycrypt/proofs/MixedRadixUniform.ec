require import AllCore IntDiv Distr DInterval StdRing StdOrder.
import RField RealOrder.

op mru_join (p : int) (ab : int * int) : int = ab.`1 + p*ab.`2.
op mru_split (p z : int) : int * int = (z %% p,z %/ p).

lemma mru_join_split p z : mru_join p (mru_split p z) = z.
proof. rewrite /mru_join /mru_split /=; have h := divz_eq z p; smt(). qed.

lemma mru_split_join p a b : 0 < p => 0 <= a < p =>
  mru_split p (mru_join p (a,b)) = (a,b).
proof.
  move=> hp ha; rewrite /mru_join /mru_split /= (mulzC p b).
  have hm : (a+b*p) %% p = a by rewrite modzMDr (pmod_small a p ha).
  have hd : (a+b*p) %/ p = b by rewrite divzMDr 1:/# (pdiv_small a p ha).
  by rewrite hm hd.
qed.

lemma mru_join_range p q a b :
  0 < p => 0 < q => 0 <= a < p => 0 <= b < q =>
  0 <= mru_join p (a,b) < p*q.
proof. move=> hp hq ha hb; rewrite /mru_join /=; smt(). qed.

lemma mru_split_range p q z :
  0 < p => 0 < q => 0 <= z < p*q =>
  0 <= (mru_split p z).`1 < p /\ 0 <= (mru_split p z).`2 < q.
proof.
  move=> hp hq hz; rewrite /mru_split /=.
  have hm0 : 0 <= z %% p by apply modz_ge0; smt().
  have hm1 : z %% p < p by apply ltz_pmod; smt().
  have hd := divz_ge0 z p _; first smt().
  have hu : z %/ p < q by rewrite ltz_divLR 1:hp; smt().
  smt().
qed.

(* Independent bounded digits are exactly a uniform integer in their
   product range. Both directions retain the full joint distribution. *)
lemma mru_join_uniform p q : 0 < p => 0 < q =>
  dmap (dinter 0 (p-1) `*` dinter 0 (q-1)) (mru_join p) =
    dinter 0 (p*q-1).
proof.
  move=> hp hq.
  apply (dmap_bij _ _ (mru_join p) (mru_split p)).
  + move=> [a b] /=; rewrite supp_dprod !supp_dinter /= => -[ha hb].
    have h := mru_join_range p q a b hp hq _ _; first 2 smt().
    smt().
  + move=> z; rewrite supp_dinter => hz.
    have [ha hb] := mru_split_range p q z hp hq _; first smt().
    have ha' : 0 <= z %% p <= p-1 by move: ha; rewrite /mru_split /=; smt().
    have hb' : 0 <= z %/ p <= q-1 by move: hb; rewrite /mru_split /=; smt().
    rewrite /mru_split dprod1E !dinter1E /= hz ha' hb' /= fromintM.
    field; smt().
  + move=> [a b] /=; rewrite supp_dprod !supp_dinter /= => -[ha hb].
    apply mru_split_join; smt().
  move=> z _; exact (mru_join_split p z).
qed.

lemma mru_split_uniform p q : 0 < p => 0 < q =>
  dmap (dinter 0 (p*q-1)) (mru_split p) =
    dinter 0 (p-1) `*` dinter 0 (q-1).
proof.
  move=> hp hq; rewrite -(mru_join_uniform p q hp hq) dmap_comp.
  apply (eq_trans _ (dmap (dinter 0 (p-1) `*` dinter 0 (q-1))
    (fun (ab : int * int) => ab)) _).
  + apply eq_dmap_in; case=> a b /=.
    rewrite supp_dprod !supp_dinter /= => -[ha hb].
    apply mru_split_join; smt().
  by rewrite dmap_id.
qed.
