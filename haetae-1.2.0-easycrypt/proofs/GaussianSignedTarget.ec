require import AllCore IntDiv List Distr DBool DProd RealSeries SDist StdRing StdOrder.
require import Gaussian76Spec Gaussian76Properties Gaussian76Rounding.
import RField RealOrder.

(* The sign is restored after rounding the absolute value.  In particular,
   the two halfway inputs round away from zero. *)
op gst_round_signed (k : int) : int =
  if k < 0 then -g76_round_absolute k else g76_round_absolute k.
op gst_target : int distr = dmap g76_distr gst_round_signed.

op gst_apply (bit : bool) (magnitude : int) : int =
  if bit then -magnitude else magnitude.
op gst_signed_distribution (d : int distr) : int distr =
  dmap (dbool `*` d) (fun (br : bool * int) => gst_apply br.`1 br.`2).

lemma gst_apply_zero bit : gst_apply bit 0 = 0.
proof. rewrite /gst_apply; case bit; trivial. qed.

lemma gst_negation_mass (d : int distr) (r : int) :
  mu1 (dmap d (fun k : int => -k)) r = mu1 d (-r).
proof.
  apply (dmap1E_can d (fun k : int => -k) (fun k : int => -k) r); smt().
qed.

lemma gst_signed_ll (d : int distr) : is_lossless d =>
  is_lossless (gst_signed_distribution d).
proof.
  move=> hd; rewrite /gst_signed_distribution; apply dmap_ll; apply dprod_ll_auto.
  + exact dbool_ll.
  exact hd.
qed.

lemma gst_signed_event (d : int distr) (event : int -> bool) :
  mu (gst_signed_distribution d) event =
    (mu d event + mu d (fun k => event (-k))) / 2%r.
proof.
  rewrite /gst_signed_distribution dmap_dprodE dletE RealSeries.sum_bool /=.
  rewrite !dbool1E !dmapE /(\o) /gst_apply /=.
  have he : (fun k : int => event k) = event by apply fun_ext; trivial.
  rewrite he; ring.
qed.

lemma gst_signed_mass (d : int distr) (r : int) :
  mu1 (gst_signed_distribution d) r = (mu1 d r + mu1 d (-r)) / 2%r.
proof.
  rewrite (gst_signed_event d (pred1 r)).
  have he : mu d (fun k => pred1 r (-k)) = mu1 d (-r).
  + apply mu_eq => k; rewrite /pred1; smt().
  by rewrite he.
qed.

lemma gst_signed_symmetric (d : int distr) :
  dmap d (fun k : int => -k) = d => gst_signed_distribution d = d.
proof.
  move=> hd; apply eq_distr => r.
  have he : mu1 d (-r) = mu1 d r by rewrite -(gst_negation_mass d r) hd.
  rewrite gst_signed_mass he; field; trivial.
qed.

(* A fair sign erases the original sign of any integer.  The zero case
   needs no special mass correction because both coin outcomes give zero. *)
lemma gst_signed_absolute (d : int distr) :
  gst_signed_distribution (dmap d (fun k : int => `|k|)) = gst_signed_distribution d.
proof.
  rewrite /gst_signed_distribution !dmap_dprodE_swap dlet_dmap.
  apply eq_dlet => // k /=.
  apply eq_distr => r; rewrite !dmap1E !dboolE /(\o) /pred1 /gst_apply /=.
  case (0 <= k) => hk.
  + have -> : `|k| = k by smt().
    trivial.
  have -> : `|k| = -k by smt().
  smt().
qed.

lemma gst_gaussian_reflection :
  dmap g76_distr (fun k : int => -k) = g76_distr.
proof.
  apply eq_distr => k; rewrite gst_negation_mass !g76_distr_mu1 /g76_pmf.
  by rewrite g76_rho_symmetry.
qed.

lemma gst_round_signed_zero : gst_round_signed 0 = 0.
proof. by rewrite /gst_round_signed /g76_round_absolute /g76_round_magnitude. qed.

lemma gst_round_signed_odd (k : int) : gst_round_signed (-k) = -gst_round_signed k.
proof.
  case (k=0) => hk; first by rewrite hk /= gst_round_signed_zero.
  have he : g76_round_absolute (-k) = g76_round_absolute k.
  + rewrite /g76_round_absolute; congr; smt().
  rewrite /gst_round_signed he.
  case (k<0); case (-k<0); smt().
qed.

lemma gst_round_signed_absolute (k : int) : `|gst_round_signed k| = g76_round_absolute k.
proof.
  have h := g76_round_absolute_nonnegative k.
  rewrite /gst_round_signed; case (k<0); smt().
qed.

lemma gst_round_signed_ties :
  gst_round_signed 32767 = 0 /\ gst_round_signed (-32767) = 0 /\
  gst_round_signed 32768 = 1 /\ gst_round_signed (-32768) = -1.
proof. by rewrite /gst_round_signed /g76_round_absolute /g76_round_magnitude. qed.

lemma gst_target_reflection : dmap gst_target (fun r : int => -r) = gst_target.
proof.
  have h := congr1 (fun d => dmap d gst_round_signed) _ _ gst_gaussian_reflection.
  rewrite /= dmap_comp in h.
  rewrite /gst_target dmap_comp -h.
  apply eq_dmap => k; by rewrite /(\o) /= gst_round_signed_odd.
qed.

lemma gst_target_absolute :
  dmap gst_target (fun r : int => `|r|) = g76_rounded.
proof.
  rewrite /gst_target /g76_rounded dmap_comp.
  apply eq_dmap => k; by rewrite /(\o) /= gst_round_signed_absolute.
qed.

lemma gst_target_eq : gst_target = gst_signed_distribution g76_rounded.
proof.
  have hs := gst_signed_symmetric gst_target gst_target_reflection.
  have ha := gst_signed_absolute gst_target.
  rewrite gst_target_absolute in ha; smt().
qed.

lemma gst_target_ll : is_lossless gst_target.
proof. rewrite /gst_target; apply dmap_ll; exact g76_distr_ll. qed.

lemma gst_target_symmetry (r : int) : mu1 gst_target (-r) = mu1 gst_target r.
proof. by rewrite -(gst_negation_mass gst_target r) gst_target_reflection. qed.

lemma gst_target_zero_mass : mu1 gst_target 0 = mu1 g76_rounded 0.
proof. rewrite gst_target_eq gst_signed_mass /=; field; trivial. qed.

lemma gst_target_nonzero_mass (r : int) : r <> 0 =>
  mu1 gst_target r = mu1 g76_rounded (`|r|) / 2%r.
proof.
  move=> hr; rewrite gst_target_eq gst_signed_mass.
  case (0 <= r) => hp.
  + have hn : -r < 0 by smt().
    have he : `|r| = r by smt().
    by rewrite (g76_rounded_negative (-r) hn) he /=.
  have hn : r < 0 by smt().
  have he : `|r| = -r by smt().
  by rewrite (g76_rounded_negative r hn) he /=.
qed.

lemma gst_signed_contraction (d e : int distr) :
  sdist (gst_signed_distribution d) (gst_signed_distribution e) <= sdist d e.
proof.
  have h := sdist_dmap (dbool `*` d) (dbool `*` e)
    (fun (br : bool * int) => gst_apply br.`1 br.`2).
  by move: h; rewrite (sdist_dprodC dbool dbool d e) sdist_dprod2r dbool_ll /=.
qed.

lemma gst_target_contraction (d : int distr) :
  sdist (gst_signed_distribution d) gst_target <= sdist d g76_rounded.
proof. rewrite gst_target_eq; exact (gst_signed_contraction d g76_rounded). qed.
