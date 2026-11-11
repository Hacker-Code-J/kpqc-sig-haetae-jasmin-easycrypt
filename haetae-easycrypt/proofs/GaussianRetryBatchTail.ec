require import AllCore IntDiv List Distr DList RealSeq StdRing StdOrder.
require import GaussianRetryTail.
import RField RealOrder.

(* One accepted candidate in every block supplies at least as many accepted
   candidates as there are blocks.  This is a deterministic list fact. *)
lemma grbt_blocks_adequate ['a] (accept : 'a -> bool) (blocks : 'a list list) :
  all (has accept) blocks => size blocks <= count accept (flatten blocks).
proof.
  elim: blocks => [|xs rest ih] /=; first trivial.
  move=> [hx hr]; rewrite flatten_cons count_cat.
  have hc := ih hr; move: hx; rewrite has_count; smt().
qed.

lemma grbt_insufficient_bad_block ['a] (accept : 'a -> bool) (blocks : 'a list list) :
  count accept (flatten blocks) < size blocks =>
  has (all (predC accept)) blocks.
proof.
  move=> hcount; case (has (all (predC accept)) blocks) => // hbad.
  move/List.hasPn: hbad => hbad.
  have hgood : all (has accept) blocks.
  + apply/List.allP => xs hxs.
    have h := hbad xs hxs; rewrite all_predC in h; smt().
  have h := grbt_blocks_adequate accept blocks hgood; smt().
qed.

lemma grbt_iid_has_bound ['a] (d : 'a distr) (bad : 'a -> bool) n :
  is_lossless d => 0 <= n =>
  mu (dlist d n) (has bad) <= n%r * mu d bad.
proof.
  move=> hd; elim: n => [|n hn ih].
  + by rewrite dlist0 1:// dunitE /=.
  rewrite dlistS 1:hn /= dmapE /(\o) /=.
  have h := le_dprod_or d (dlist d n) bad (has bad).
  rewrite (dlist_ll d n hd) hd /= in h.
  rewrite fromintD /=; smt().
qed.

lemma grbt_prefix_shortfall ['a] (d : 'a distr) (accept : 'a -> bool) n t :
  is_lossless d => 0 <= n => 0 <= t =>
  mu (dlist d (n*t)) (fun xs => count accept xs < n) <=
    n%r * (1%r-mu d accept)^t.
proof.
  move=> hd hn ht.
  have hm : n*t = t*n by ring.
  rewrite hm -(dlist_dlist d t n ht hn) dmapE /(\o).
  have hsub :
    mu (dlist (dlist d t) n) (fun blocks => count accept (flatten blocks) < n) <=
    mu (dlist (dlist d t) n) (has (all (predC accept))).
  + apply mu_le => blocks hblocks hcount.
    have hs := supp_dlist_size (dlist d t) n blocks hn hblocks.
    apply grbt_insufficient_bad_block; smt().
  have hb := grbt_iid_has_bound (dlist d t) (all (predC accept)) n
    (dlist_ll d t hd) hn.
  rewrite gaussian_retry_iid_all 1:ht mu_not hd in hb.
  exact (ler_trans _ _ _ hsub hb).
qed.

lemma grbt_prefix_shortfall_limit ['a] (d : 'a distr) (accept : 'a -> bool) n :
  is_lossless d => 0%r < mu d accept => 0 <= n =>
  RealSeq.convergeto
    (fun t => mu (dlist d (n*t)) (fun xs => count accept xs < n)) 0%r.
proof.
  move=> hd hp hn.
  have hm := mu_bounded d accept.
  have hr : -1%r < 1%r-mu d accept < 1%r by smt().
  have hc := RealSeq.cnvtoZ n%r _ _ (RealSeq.cnvto_pow (1%r-mu d accept) hr).
  rewrite mulr0 in hc.
  apply (RealSeq.squeeze_cnvto (fun _ => 0%r)
    (fun t => n%r*(1%r-mu d accept)^t) 0 _ 0%r).
  + move=> t ht /=; split; first exact (ge0_mu _ _).
    move=> _.
    exact (grbt_prefix_shortfall d accept n t hd hn ht).
  + exact (RealSeq.cnvtoC 0%r).
  exact hc.
qed.

lemma grbt_shortfall_antitone ['a] (d : 'a distr) (accept : 'a -> bool) n a b :
  is_lossless d => 0 <= a <= b =>
  mu (dlist d b) (fun xs => count accept xs < n) <=
    mu (dlist d a) (fun xs => count accept xs < n).
proof.
  move=> hd [ha hab].
  have htail : 0 <= b-a by smt().
  have he : b = a+(b-a) by ring.
  rewrite he (dlist_add d a (b-a) ha htail) dmapE /(\o).
  have hsub :
    mu (dlist d a `*` dlist d (b-a))
      (fun (xy : 'a list * 'a list) => count accept (xy.`1 ++ xy.`2) < n) <=
    mu (dlist d a `*` dlist d (b-a))
      (fun (xy : 'a list * 'a list) => count accept xy.`1 < n).
  + apply mu_le => xy hxy /=; rewrite count_cat.
    have h := count_ge0 accept xy.`2; smt().
  rewrite (dprodEl (dlist d a) (dlist d (b-a))
    (fun xs => count accept xs < n)) (dlist_ll d (b-a) hd) /= in hsub.
  exact hsub.
qed.

(* Convergence is for every increasing finite-prefix length, not only
   lengths divisible by n.  No distribution on infinite functions is used. *)
lemma grbt_all_prefix_shortfall_limit ['a] (d : 'a distr) (accept : 'a -> bool) n :
  is_lossless d => 0%r < mu d accept => 0 <= n =>
  RealSeq.convergeto
    (fun length => mu (dlist d length) (fun xs => count accept xs < n)) 0%r.
proof.
  move=> hd hp hn.
  have hc := grbt_prefix_shortfall_limit d accept n hd hp hn.
  move=> epsilon hepsilon; have [T hT] := hc epsilon hepsilon.
  pose t0 := max 0 T.
  have [ht00 htT] : 0 <= t0 /\ T <= t0 by rewrite /t0 /max; smt().
  have hbase : 0 <= n*t0 by apply IntOrder.mulr_ge0; smt().
  exists (n*t0) => length hlength.
  have hsmall := hT t0 htT.
  have hbound := grbt_shortfall_antitone d accept n (n*t0) length hd _;
    first smt().
  rewrite /= ?subr0 ger0_norm 1:ge0_mu in hsmall.
  rewrite /= ?subr0 ger0_norm 1:ge0_mu.
  exact (ler_lt_trans _ _ _ hbound hsmall).
qed.

lemma grbt_prefix_shortfall_1m7 (d : (int * bool) distr) n t :
  is_lossless d => 1%r/7%r <= mu d snd => 0 <= n => 0 <= t =>
  mu (dlist d (n*t)) (fun xs => count snd xs < n) <= n%r*(6%r/7%r)^t.
proof.
  move=> hd hp hn ht.
  have hb := grbt_prefix_shortfall d snd n t hd hn ht.
  have hm := mu_bounded d snd.
  have hpow : (1%r-mu d snd)^t <= (6%r/7%r)^t.
  + apply (ler_pexp t (1%r-mu d snd) (6%r/7%r) ht); smt().
  have hnreal : 0%r <= n%r by rewrite le_fromint.
  exact (ler_trans _ _ _ hb (ler_wpmul2l n%r hnreal _ _ hpow)).
qed.

lemma grbt_prefix_shortfall_256 (d : (int * bool) distr) t :
  is_lossless d => 1%r/7%r <= mu d snd => 0 <= t =>
  mu (dlist d (256*t)) (fun xs => count snd xs < 256) <= 256%r*(6%r/7%r)^t.
proof. by move=> hd hp ht; exact (grbt_prefix_shortfall_1m7 d 256 t hd hp _ ht). qed.

lemma grbt_prefix_shortfall_257 (d : (int * bool) distr) t :
  is_lossless d => 1%r/7%r <= mu d snd => 0 <= t =>
  mu (dlist d (257*t)) (fun xs => count snd xs < 257) <= 257%r*(6%r/7%r)^t.
proof. by move=> hd hp ht; exact (grbt_prefix_shortfall_1m7 d 257 t hd hp _ ht). qed.

lemma grbt_all_prefix_256_limit (d : (int * bool) distr) :
  is_lossless d => 0%r < mu d snd =>
  RealSeq.convergeto
    (fun length => mu (dlist d length) (fun xs => count snd xs < 256)) 0%r.
proof. by move=> hd hp; exact (grbt_all_prefix_shortfall_limit d snd 256 hd hp _). qed.

lemma grbt_all_prefix_257_limit (d : (int * bool) distr) :
  is_lossless d => 0%r < mu d snd =>
  RealSeq.convergeto
    (fun length => mu (dlist d length) (fun xs => count snd xs < 257)) 0%r.
proof. by move=> hd hp; exact (grbt_all_prefix_shortfall_limit d snd 257 hd hp _). qed.
