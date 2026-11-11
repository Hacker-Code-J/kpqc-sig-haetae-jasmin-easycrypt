require import AllCore List Distr DList Finite RealSeries RealExp StdRing StdOrder.
import RField RealOrder.

op iet_sum ['a] (q : 'a -> real) (xs : 'a list) : real =
  foldr (fun x total => q x+total) 0%r xs.
op iet_prod ['a] (w : 'a -> real) (xs : 'a list) : real =
  foldr (fun x total => w x*total) 1%r xs.

lemma iet_finite_dmap ['a 'b] (d : 'a distr) (f : 'a -> 'b) :
  is_finite (Distr.support d) => is_finite (Distr.support (dmap d f)).
proof.
  move=> hd; rewrite /dmap; apply finite_dlet; first exact hd.
  move=> x hx; exact finite_dunit.
qed.

lemma iet_finite_dlist ['a] (d : 'a distr) n :
  is_finite (Distr.support d) => 0 <= n => is_finite (Distr.support (dlist d n)).
proof.
  move=> hd hn; elim: n hn => [|n hn ih].
  + rewrite dlist0 1://; exact finite_dunit.
  rewrite (dlistS d n hn) dapply_dmap.
  apply iet_finite_dmap; exact (finite_dprod d (dlist d n) hd ih).
qed.

(* This product identity needs integrability, not losslessness. *)
lemma iet_expectation_product ['a 'b] (d : 'a distr) (e : 'b distr)
    (f : 'a -> real) (g : 'b -> real) :
  hasE d f => hasE e g =>
  E (d `*` e) (fun (xy : 'a*'b) => f xy.`1*g xy.`2)=E d f*E e g.
proof.
  rewrite /hasE => hf hg.
  pose F := fun (xy : 'a*'b) => (f xy.`1*mu1 d xy.`1)*(g xy.`2*mu1 e xy.`2).
  have hF : RealSeries.summable F by
    rewrite /F; exact (RealSeries.summableM_prod _ _ hf hg).
  have he : E (d `*` e) (fun (xy : 'a*'b) => f xy.`1*g xy.`2)=RealSeries.sum F.
  + rewrite /E /F; apply RealSeries.eq_sum; case=> x y /=.
    rewrite dprod1E; ring.
  rewrite he (RealSeries.sum_pair F hF) /F /= /E -RealSeries.sumZr.
  apply RealSeries.eq_sum => x /=; by rewrite RealSeries.sumZ.
qed.

lemma iet_iid_product ['a] (d : 'a distr) (w : 'a -> real) n :
  is_finite (Distr.support d) => 0 <= n =>
  E (dlist d n) (iet_prod w)=(E d w)^n.
proof.
  move=> hd hn; elim: n hn => [|n hn ih].
  + by rewrite dlist0 1:// exp_dunit /iet_prod /= RField.expr0.
  have hdn := iet_finite_dlist d n hd hn.
  have hdnext := iet_finite_dlist d (n+1) hd _; first smt().
  have hE := hasE_finite (dlist d (n+1)) (iet_prod w) hdnext.
  have hnext := dlistS d n hn; rewrite dapply_dmap in hnext.
  move: hE; rewrite hnext => hE.
  rewrite (exp_dmap _ _ _ hE) /(\o).
  have hf := hasE_finite d w hd.
  have hg := hasE_finite (dlist d n) (iet_prod w) hdn.
  have he : (fun (xy : 'a*'a list) => iet_prod w (xy.`1::xy.`2)) =
      (fun (xy : 'a*'a list) => w xy.`1*iet_prod w xy.`2) by apply fun_ext; case=> x xs; trivial.
  rewrite he (iet_expectation_product d (dlist d n) w (iet_prod w) hf hg) ih
    RField.exprS 1:hn.
  ring.
qed.

lemma iet_prod_nonnegative ['a] (w : 'a -> real) xs :
  all (fun x => 0%r <= w x) xs => 0%r <= iet_prod w xs.
proof.
  elim: xs => [|x xs ih]; first by rewrite /iet_prod.
  rewrite /=.
  move=> [hx hxs].
  rewrite /iet_prod /= -/(iet_prod w xs); exact (mulr_ge0 _ _ hx (ih hxs)).
qed.

lemma iet_iid_prod_nonnegative ['a] (d : 'a distr) (w : 'a -> real) n xs :
  0 <= n => (forall x, x \in d => 0%r <= w x) =>
  xs \in dlist d n => 0%r <= iet_prod w xs.
proof.
  move=> hn hw; rewrite (supp_dlist d n xs hn).
  move=> [_ hall].
  apply iet_prod_nonnegative; apply/allP => x hx.
  move/allP: hall => hall; exact (hw x (hall x hx)).
qed.

lemma iet_markov_nonnegative ['a] (d : 'a distr) (f : 'a -> real) a :
  hasE d f => 0%r < a => (forall x, x \in d => 0%r <= f x) =>
  mu d (fun x => a <= f x) <= E d f/a.
proof.
  move=> hf ha hnonnegative.
  have hc : hasE d (fun x => if a <= f x then a else 0%r) by
    apply hasE_cond; exact (hasEC d a).
  have hpoint : forall x, x \in d => (if a <= f x then a else 0%r) <= f x.
  + move=> x hx; have hn := hnonnegative x hx; case (a<=f x); smt().
  have he := in_ler_exp d _ f hc hf hpoint.
  rewrite expC_cond in he.
  rewrite (ler_pdivl_mulr a _ _ ha) mulrC; exact he.
qed.

lemma iet_iid_product_tail ['a] (d : 'a distr) (w : 'a -> real) n r :
  is_finite (Distr.support d) => 0 <= n =>
  (forall x, x \in d => 0%r <= w x) => E d w <= r =>
  mu (dlist d n) (fun xs => 1%r <= iet_prod w xs) <= r^n.
proof.
  move=> hd hn hw hr.
  have hdn := iet_finite_dlist d n hd hn.
  have hE := hasE_finite (dlist d n) (iet_prod w) hdn.
  have hpos : forall xs, xs \in dlist d n => 0%r <= iet_prod w xs by
    move=> xs hx; exact (iet_iid_prod_nonnegative d w n xs hn hw hx).
  have hm := iet_markov_nonnegative (dlist d n) (iet_prod w) 1%r hE _ hpos;
    first trivial.
  rewrite /= (iet_iid_product d w n hd hn) in hm.
  have hw0 := exp_ge0 d w hw.
  have hp := ler_pexp n (E d w) r hn _; first smt().
  exact (ler_trans _ _ _ hm hp).
qed.

lemma iet_exp_product_upper ['a] (q : 'a -> real) xs t center :
  iet_prod (fun x => RealExp.exp (t*(q x-center))) xs =
    RealExp.exp (t*(iet_sum q xs-(size xs)%r*center)).
proof.
  elim: xs => [|x xs ih].
  + by rewrite /iet_prod /iet_sum /= RealExp.exp0.
  have hp : iet_prod (fun x => RealExp.exp (t*(q x-center))) (x::xs)=
      RealExp.exp (t*(q x-center))*iet_prod (fun x => RealExp.exp (t*(q x-center))) xs
    by rewrite /iet_prod.
  have hs : iet_sum q (x::xs)=q x+iet_sum q xs by rewrite /iet_sum.
  rewrite hp ih -RealExp.expD hs /= fromintD /=; congr; ring.
qed.

lemma iet_exp_product_lower ['a] (q : 'a -> real) xs t center :
  iet_prod (fun x => RealExp.exp (t*(center-q x))) xs =
    RealExp.exp (t*((size xs)%r*center-iet_sum q xs)).
proof.
  have hf : (fun x => RealExp.exp (t*(center-q x))) =
      (fun x => RealExp.exp ((-t)*(q x-center))) by apply fun_ext => x; congr; ring.
  rewrite hf iet_exp_product_upper; congr; ring.
qed.

lemma iet_iid_exponential_upper ['a] (d : 'a distr) (q : 'a -> real) n upper t r :
  is_finite (Distr.support d) => 0 <= n => 0%r < t =>
  E d (fun x => RealExp.exp (t*(q x-upper))) <= r =>
  mu (dlist d n) (fun xs => n%r*upper < iet_sum q xs) <= r^n.
proof.
  move=> hd hn ht hm.
  have hpos : forall x, x \in d => 0%r <= RealExp.exp (t*(q x-upper)) by
    move=> x hx; have h := RealExp.exp_gt0 (t*(q x-upper)); smt().
  have hp := iet_iid_product_tail d (fun x => RealExp.exp (t*(q x-upper))) n r hd hn hpos hm.
  apply (ler_trans _ _ _ _ hp).
  apply mu_le => xs hx hsum.
  move: hx; rewrite (supp_dlist d n xs hn).
  move=> [hsize _].
  rewrite /= (iet_exp_product_upper q xs t upper) hsize -RealExp.exp0 RealExp.exp_mono.
  apply mulr_ge0; smt().
qed.

lemma iet_iid_exponential_lower ['a] (d : 'a distr) (q : 'a -> real) n lower t r :
  is_finite (Distr.support d) => 0 <= n => 0%r < t =>
  E d (fun x => RealExp.exp (t*(lower-q x))) <= r =>
  mu (dlist d n) (fun xs => iet_sum q xs < n%r*lower) <= r^n.
proof.
  move=> hd hn ht hm.
  have hpos : forall x, x \in d => 0%r <= RealExp.exp (t*(lower-q x)) by
    move=> x hx; have h := RealExp.exp_gt0 (t*(lower-q x)); smt().
  have hp := iet_iid_product_tail d (fun x => RealExp.exp (t*(lower-q x))) n r hd hn hpos hm.
  apply (ler_trans _ _ _ _ hp).
  apply mu_le => xs hx hsum.
  move: hx; rewrite (supp_dlist d n xs hn).
  move=> [hsize _].
  rewrite /= (iet_exp_product_lower q xs t lower) hsize -RealExp.exp0 RealExp.exp_mono.
  apply mulr_ge0; smt().
qed.

(* The two scalar exponential bounds are explicit inputs. They concern
   the distribution d itself and are not inferred from its support. *)
lemma iet_iid_exponential_outside ['a] (d : 'a distr) (q : 'a -> real)
    n lower upper tminus tplus rminus rplus :
  is_finite (Distr.support d) => 0 <= n => 0%r < tminus => 0%r < tplus =>
  E d (fun x => RealExp.exp (tminus*(lower-q x))) <= rminus =>
  E d (fun x => RealExp.exp (tplus*(q x-upper))) <= rplus =>
  mu (dlist d n) (fun xs => iet_sum q xs < n%r*lower \/ n%r*upper < iet_sum q xs) <=
    rminus^n+rplus^n.
proof.
  move=> hd hn htm htp hmm hmp.
  have hl := iet_iid_exponential_lower d q n lower tminus rminus hd hn htm hmm.
  have hu := iet_iid_exponential_upper d q n upper tplus rplus hd hn htp hmp.
  have he := mu_or (dlist d n) (fun xs => iet_sum q xs < n%r*lower)
    (fun xs => n%r*upper < iet_sum q xs).
  have hz := ge0_mu (dlist d n) (fun xs =>
    iet_sum q xs < n%r*lower /\ n%r*upper < iet_sum q xs).
  rewrite /predU /predI in he; smt().
qed.
