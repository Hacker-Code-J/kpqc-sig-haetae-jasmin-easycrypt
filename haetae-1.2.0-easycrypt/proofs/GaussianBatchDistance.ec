require import AllCore List Distr DList SDist StdRing StdOrder.
import RField RealOrder.

(* The library product bound already holds for subdistributions.  Hence
   losslessness is needed only when discarding an independently drawn tail. *)
lemma gb_batch_distance ['a] (d e : 'a distr) n : 0 <= n =>
  sdist (dlist d n) (dlist e n) <= n%r * sdist d e.
proof. exact (SDist.sdist_dlist d e n). qed.

lemma gb_batch_distance_bound ['a] (d e : 'a distr) n epsilon :
  0 <= n => sdist d e <= epsilon =>
  sdist (dlist d n) (dlist e n) <= n%r * epsilon.
proof.
  move=> hn he.
  have hb := gb_batch_distance d e n hn.
  have hnr : 0%r <= n%r by rewrite le_fromint.
  have hm := ler_wpmul2l n%r hnr _ _ he.
  exact (ler_trans _ _ _ hb hm).
qed.

lemma gb_batch_distance_strict ['a] (d e : 'a distr) n epsilon :
  0 < n => sdist d e < epsilon =>
  sdist (dlist d n) (dlist e n) < n%r * epsilon.
proof.
  move=> hn he.
  have hb := gb_batch_distance d e n _; first smt().
  have hnr : 0%r < n%r by rewrite lt_fromint.
  have hm : n%r * sdist d e < n%r * epsilon
    by rewrite ltr_pmul2l 1:hnr.
  exact (ler_lt_trans _ _ _ hb hm).
qed.

lemma gb_batch_event_distance ['a] (d e : 'a distr) n (event : 'a list -> bool) :
  0 <= n =>
  `|mu (dlist d n) event - mu (dlist e n) event| <= n%r * sdist d e.
proof.
  move=> hn; exact (ler_trans _ _ _ (sdist_upper_bound _ _ event)
    (gb_batch_distance d e n hn)).
qed.

lemma gb_batch_256_2m39 ['a] (d e : 'a distr) :
  sdist d e < 1%r / (2^39)%r =>
  sdist (dlist d 256) (dlist e 256) < 1%r / (2^31)%r.
proof.
  move=> he.
  have hb := gb_batch_distance_strict d e 256 (1%r/(2^39)%r) _ he;
    first trivial.
  have h39 : 2^39 = 549755813888 by ring.
  have h31 : 2^31 = 2147483648 by ring.
  move: hb; rewrite h39 h31; smt().
qed.

lemma gb_batch_257_2m39 ['a] (d e : 'a distr) :
  sdist d e < 1%r / (2^39)%r =>
  sdist (dlist d 257) (dlist e 257) < 257%r / (2^39)%r.
proof.
  move=> he.
  have hb := gb_batch_distance_strict d e 257 (1%r/(2^39)%r) _ he;
    first trivial.
  have heq : 257%r * (1%r/(2^39)%r) = 257%r/(2^39)%r by ring.
  by move: hb; rewrite heq.
qed.

lemma gb_batch_257_2m30 ['a] (d e : 'a distr) :
  sdist d e < 1%r / (2^39)%r =>
  sdist (dlist d 257) (dlist e 257) < 1%r / (2^30)%r.
proof.
  move=> he; have hb := gb_batch_257_2m39 d e he.
  have h39 : 2^39 = 549755813888 by ring.
  have h30 : 2^30 = 1073741824 by ring.
  move: hb; rewrite h39 h30; smt().
qed.

lemma gb_dlist_prefix ['a] (d : 'a distr) n tail :
  is_lossless d => 0 <= n => 0 <= tail =>
  dmap (dlist d (n+tail)) (take n) = dlist d n.
proof.
  move=> hd hn ht; rewrite (dlist_add d n tail hn ht) dmap_comp /(\o).
  apply (eq_trans _
    (dmap (dlist d n `*` dlist d tail) (fun (p : 'a list * 'a list) => p.`1)) _).
  + apply eq_dmap_in; case=> xs ys /=; rewrite supp_dprod => -[hxs hys].
    exact (take_size_cat n xs ys (supp_dlist_size d n xs hn hxs)).
  rewrite dmap_dprodE_swap /= dmap_id.
  exact (dlet_cst (dlist d tail) (dlist d n) (dlist_ll d tail hd)).
qed.

lemma gb_first256_of257 ['a] (d : 'a distr) : is_lossless d =>
  dmap (dlist d 257) (take 256) = dlist d 256.
proof. by move=> hd; exact (gb_dlist_prefix d 256 1 hd _ _). qed.

lemma gb_first256_distance ['a] (d e : 'a distr) :
  is_lossless d => is_lossless e =>
  sdist (dmap (dlist d 257) (take 256)) (dmap (dlist e 257) (take 256)) <=
    256%r * sdist d e.
proof.
  move=> hd he; rewrite (gb_first256_of257 d hd) (gb_first256_of257 e he).
  exact (gb_batch_distance d e 256 _).
qed.

lemma gb_first256_2m39 ['a] (d e : 'a distr) :
  is_lossless d => is_lossless e => sdist d e < 1%r/(2^39)%r =>
  sdist (dmap (dlist d 257) (take 256)) (dmap (dlist e 257) (take 256)) <
    1%r/(2^31)%r.
proof.
  move=> hd he hdist; rewrite (gb_first256_of257 d hd) (gb_first256_of257 e he).
  exact (gb_batch_256_2m39 d e hdist).
qed.
