require import AllCore List Real StdRing StdOrder Bernstein10Spec.
import RField RealOrder.

lemma bernstein10_power_coefficients_size b :
  size (bernstein10_power_coefficients b) = 11.
proof. by rewrite /bernstein10_power_coefficients /=. qed.

lemma bernstein10_identity b t :
  power_eval (bernstein10_power_coefficients b) t = bernstein_eval b t.
proof.
  rewrite /power_eval /bernstein10_power_coefficients /bernstein_eval /=.
  rewrite !(fromintD, fromintM, fromintN) /=.
  ring.
qed.

lemma bernstein10_nth_nonnegative b i :
  all (fun x => 0 <= x) b => 0%r <= (nth 0 b i)%r.
proof.
  move/List.allP=> hb.
  case (0 <= i < size b) => hi.
  + have h := hb (nth 0 b i) (mem_nth 0 b i hi).
    smt().
  by rewrite nth_out 1:hi /=.
qed.

lemma bernstein10_nonnegative b t :
  all (fun x => 0 <= x) b => 0%r <= t <= 1%r =>
  0%r <= bernstein_eval b t.
proof.
  move=> hb ht.
  have hc : forall i, 0%r <= (nth 0 b i)%r
    by move=> i; exact (bernstein10_nth_nonnegative b i hb).
  have hp : forall k, 0%r <= t^k
    by move=> k; apply expr_ge0; smt().
  have hq : forall k, 0%r <= (1%r-t)^k
    by move=> k; apply expr_ge0; smt().
  rewrite /bernstein_eval.
  smt(mulr_ge0).
qed.

lemma bernstein10_checked_nonnegative a b t :
  bernstein10_check a b => 0%r <= t <= 1%r =>
  0%r <= power_eval a t.
proof.
  move=> [ha [hb [he hn]]] ht.
  rewrite he bernstein10_identity.
  exact (bernstein10_nonnegative b t hn ht).
qed.

lemma bernstein10_checked_identity a b t :
  bernstein10_check a b => power_eval a t = bernstein_eval b t.
proof.
  move=> [ha [hb [he hn]]].
  by rewrite he bernstein10_identity.
qed.

lemma bernstein10_power_nonnegative a b t :
  a = bernstein10_power_coefficients b =>
  all (fun x => 0 <= x) b => 0%r <= t <= 1%r =>
  0%r <= power_eval a t.
proof.
  move=> -> hb ht; rewrite bernstein10_identity.
  exact (bernstein10_nonnegative b t hb ht).
qed.
