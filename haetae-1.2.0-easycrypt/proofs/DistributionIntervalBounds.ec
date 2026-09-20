require import AllCore List Distr SDist StdBigop StdOrder RealSeries.
import Bigreal RealOrder RField.

(* Finite certificates concern point masses of abstract integer distributions.
   Neither the interval bounds nor the tail premise assert anything about
   SHAKE output or an implementation's source of randomness. *)
op interval_error_sum (n : int) (error : int -> real) : real =
  Bigreal.BRA.big predT error (iota_ 0 n).

lemma interval_absolute_error (p q lp up lq uq error : real) :
  lp <= p <= up => lq <= q <= uq =>
  up - lq <= error => uq - lp <= error => `|p - q| <= error.
proof. rewrite ler_norml; smt(). qed.

lemma point_interval_absolute_error (p q lower upper error : real) :
  lower <= q <= upper => p - lower <= error => upper - p <= error =>
  `|p - q| <= error.
proof. rewrite ler_norml; smt(). qed.

lemma interval_series_summable (n : int) (f : int -> real) :
  RealSeries.summable (fun k => if 0 <= k < n then f k else 0%r).
proof.
apply (RealSeries.summable_fin _ (iota_ 0 n)) => k.
rewrite mem_iota /=; smt().
qed.

lemma interval_series_sum (n : int) (f : int -> real) :
  RealSeries.sum (fun k => if 0 <= k < n then f k else 0%r) = interval_error_sum n f.
proof.
rewrite (RealSeries.sumE_fin _ (iota_ 0 n)) 1:iota_uniq.
+ move=> k; rewrite mem_iota /=; smt().
rewrite /interval_error_sum.
apply Bigreal.BRA.eq_big_seq => k; rewrite mem_iota /= => hk.
smt().
qed.

lemma interval_error_sum_mono n (f g : int -> real) :
  (forall k, 0 <= k < n => f k <= g k) =>
  interval_error_sum n f <= interval_error_sum n g.
proof.
move=> h; rewrite /interval_error_sum.
apply Bigreal.ler_sum_seq => k; rewrite mem_iota /= => hk _.
apply h; smt().
qed.

lemma interval_error_sum0 f : interval_error_sum 0 f = 0%r.
proof. by rewrite /interval_error_sum iota0 /=. qed.

lemma interval_error_sumS n f : 0 <= n =>
  interval_error_sum (n + 1) f = interval_error_sum n f + f n.
proof.
move=> hn; by rewrite /interval_error_sum iotaSr 1:hn Bigreal.BRA.big_rcons /=.
qed.

lemma interval_error_sum_nth (bounds : real list) :
  interval_error_sum (size bounds) (nth 0%r bounds) =
    Bigreal.BRA.big predT (fun x => x) bounds.
proof.
have hlist := mkseq_nth 0%r bounds.
rewrite /mkseq in hlist.
have hsum := Bigreal.BRA.big_mapT (nth 0%r bounds) (fun x => x) (iota_ 0 (size bounds)).
rewrite hlist /= in hsum.
by rewrite /interval_error_sum -hsum.
qed.

lemma interval_error_sum_certificate n (f : int -> real) (bounds : real list) budget :
  size bounds = n =>
  (forall k, 0 <= k < n => f k <= nth 0%r bounds k) =>
  Bigreal.BRA.big predT (fun x => x) bounds <= budget =>
  interval_error_sum n f <= budget.
proof.
move=> hsize herr hbudget.
have h := interval_error_sum_mono n f (nth 0%r bounds) herr.
rewrite -hsize interval_error_sum_nth in h.
rewrite -hsize.
exact (ler_trans _ _ _ h hbudget).
qed.

lemma finite_interval_support_zero (p : int distr) n k :
  (forall x, x \in p => 0 <= x < n) => !(0 <= k < n) => mu1 p k = 0%r.
proof. move=> hp hk; apply/supportPn; smt(). qed.

lemma nonnegative_support_zero (q : int distr) k :
  (forall x, x \in q => 0 <= x) => k < 0 => mu1 q k = 0%r.
proof. move=> hq hk; apply/supportPn; smt(). qed.

lemma sdist_finite_interval_tail
    (p q : int distr) (n : int) (error : int -> real) (tail : real) :
  is_lossless p => is_lossless q =>
  (forall k, k \in p => 0 <= k < n) =>
  (forall k, k \in q => 0 <= k) =>
  (forall k, 0 <= k < n => `|mu1 p k - mu1 q k| <= error k) =>
  mu q (fun k => n <= k) <= tail =>
  SDist.sdist p q <= (interval_error_sum n error + tail) / 2%r.
proof.
move=> hp hq hpsupport hqsupport herr htail.
pose majorant := fun k =>
  (if 0 <= k < n then error k else 0%r) +
  (if n <= k then mu1 q k else 0%r).
have hpoint : forall k, `|mu1 p k - mu1 q k| <= majorant k.
+ move=> k; rewrite /majorant.
  case (0 <= k < n) => hin.
  - have he := herr k hin; smt().
  have hz := finite_interval_support_zero p n k hpsupport hin.
  have hpositive := ge0_mu1 q k.
  rewrite hz sub0r normrN ger0_norm 1:hpositive.
  case (n <= k) => htailcase; first trivial.
  have hk : k < 0 by smt().
  have hqzero := nonnegative_support_zero q k hqsupport hk.
  by rewrite hqzero.
have he := interval_series_summable n error.
have ht := summable_mu1_cond q (fun k => n <= k).
have hs : RealSeries.summable majorant by
  apply (RealSeries.summableD _ _ he ht).
have hbound := RealSeries.ler_sum _ _ hpoint (SDist.summable_sdist p q) hs.
have hsum : RealSeries.sum majorant =
    interval_error_sum n error + mu q (fun k => n <= k).
+ by rewrite /majorant RealSeries.sumD 1:he 1:ht interval_series_sum -muE.
move: hbound; rewrite hsum => hbound.
rewrite SDist.sdist_tvd (is_losslessP p hp) (is_losslessP q hq) subrr normr0 addr0.
smt().
qed.
