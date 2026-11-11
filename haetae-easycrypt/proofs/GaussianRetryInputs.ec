require import AllCore IntDiv List Distr DInterval DList StdRing StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 SigmaSpec SigmaCorrectness SigmaRejection48Bridge
  SigmaNoise72Bridge SigmaCDT83Patch SigmaRawNoiseSpec Rejection48Spec
  CDTDistributionBridge SigmaConditionalSpec GaussianTraceSpec
  GaussianTraceProperties GaussianStreamSequence.
import RField RealOrder.

(* Three independent inputs encode 203 bits in a 26-byte candidate. The
   unused high five bits of the CDT encoding are zero on its support;
   this is not a uniform law on all 208-bit arrays. *)
op gr_candidate_patch (p : BArray26.t) (u y v : int) : BArray26.t =
  sigma_rejection48_patch (sigma_noise72_patch (sj_cdt83_patch p u) y) v.

op gr_candidate_distribution (p : BArray26.t) : BArray26.t distr =
  dlet (dinter 0 (cdt83_modulus-1)) (fun u =>
    dlet sr_noise_uniform (fun y =>
      dmap rejection48_uniform (fun v => gr_candidate_patch p u y v))).

op gr_event_pair (event : gauss_event) : int * bool =
  (W64.to_uint event.`1, event.`4 = W64.one).

op gr_candidate_observer (p : BArray26.t) : int * bool =
  (W64.to_uint (sigma76_spec p).`1, (sigma76_spec p).`4 = W64.one).

lemma gr_candidate_patch_observer p u y v : 0 <= v < 281474976710656 =>
  gr_candidate_observer (gr_candidate_patch p u y v) =
    let q = sigma_noise72_patch (sj_cdt83_patch p u) y in
    (W64.to_uint (sigma_rejection48_rounded q),
      rejection48_word (W64.of_int v) (sigma_rejection48_threshold q)
        (sigma_rejection48_rounded q) = W64.one).
proof.
  move=> hv; pose q := sigma_noise72_patch (sj_cdt83_patch p u) y.
  have hr := sigma_rejection48_patch_rounded q v.
  rewrite /sigma_rejection48_rounded in hr.
  have ha := sigma_rejection48_patched_acceptance q v hv.
  by rewrite /gr_candidate_observer /gr_candidate_patch -/q ha hr /sigma_rejection48_rounded.
qed.

lemma gr_candidate_distribution_pair p :
  dmap (gr_candidate_distribution p) gr_candidate_observer = sc_actual_pair p.
proof.
  rewrite /gr_candidate_distribution /sc_actual_pair dmap_dlet.
  apply eq_dlet => // u /=.
  rewrite dmap_dlet; apply eq_dlet => // y /=.
  rewrite dmap_comp; apply eq_dmap_in => v hv /=.
  have hvr : 0 <= v < 281474976710656 by
    move: hv; rewrite /rejection48_uniform supp_dinter; smt().
  exact (gr_candidate_patch_observer p u y v hvr).
qed.

lemma gr_candidate_distribution_ll p : is_lossless (gr_candidate_distribution p).
proof.
  rewrite /gr_candidate_distribution; apply dlet_ll.
  + apply dinter_ll; have h := cdt83_modulus_positive; smt().
  move=> u _; apply dlet_ll; first exact sr_noise_uniform_ll.
  move=> y _; apply dmap_ll.
  rewrite /rejection48_uniform; apply dinter_ll; trivial.
qed.

(* A finite list determines its continuous candidate-byte prefix. The
   witness value outside that prefix is only a total-function convention;
   no random law on infinite functions or concrete SHAKE is asserted. *)
op gr_candidate_stream (candidates : BArray26.t list) (j : int) : W8.t =
  BArray26.get8 (nth witness candidates (j %/ 26)) (j %% 26).

lemma gr_candidate_stream_chunk candidates i :
  BArray26.init (fun j => gr_candidate_stream candidates (26*i+j)) =
    nth witness candidates i.
proof.
  apply BArray26.ext_eq => j hj.
  rewrite BArray26.initiE 1:hj /gr_candidate_stream.
  have hd : (26*i+j) %/ 26 = i by rewrite divz_eqP //; smt().
  have hm : (26*i+j) %% 26 = j by
    rewrite (mulzC 26 i) modzMDl modz_small; smt().
  by rewrite /= hd hm.
qed.

lemma gr_candidate_stream_event candidates i :
  gauss_stream_event (gr_candidate_stream candidates) i =
    sigma76_spec (nth witness candidates i).
proof. by rewrite /gauss_stream_event gr_candidate_stream_chunk. qed.

lemma gr_candidate_stream_events candidates :
  gauss_stream_events (gr_candidate_stream candidates) (size candidates) =
    map sigma76_spec candidates.
proof.
  have hn := map_nth_range (witness<:BArray26.t>) candidates.
  have he : map (gauss_stream_event (gr_candidate_stream candidates))
      (iota_ 0 (size candidates)) =
    map sigma76_spec (map (fun i => nth witness candidates i) (iota_ 0 (size candidates))).
  + rewrite -map_comp; apply eq_in_map => i hi /=.
    exact (gr_candidate_stream_event candidates i).
  by move: he; rewrite hn /gauss_stream_events.
qed.

lemma gr_candidate_stream_prefix candidates k : 0 <= k <= size candidates =>
  gauss_stream_events (gr_candidate_stream candidates) k =
    map sigma76_spec (take k candidates).
proof.
  move=> [hk hks].
  have hm : 0 <= size candidates-k by smt().
  have h := gauss_stream_events_take (gr_candidate_stream candidates)
    k (size candidates-k) hk hm.
  have he : k+(size candidates-k) = size candidates by ring.
  by move: h; rewrite he gr_candidate_stream_events map_take => ->.
qed.

lemma gr_candidate_stream_pairs candidates :
  map gr_event_pair
    (gauss_stream_events (gr_candidate_stream candidates) (size candidates)) =
    map gr_candidate_observer candidates.
proof.
  rewrite gr_candidate_stream_events -map_comp.
  apply eq_in_map => p hp; by rewrite /(\o) /gr_event_pair /gr_candidate_observer.
qed.

lemma gr_candidate_event_accept p :
  gauss_event_accepted (sigma76_spec p) = (gr_candidate_observer p).`2.
proof.
  by rewrite /gauss_event_accepted /gr_candidate_observer /= W64.to_uint_eq W64.to_uint1.
qed.

lemma gr_candidate_stream_accepted candidates :
  map W64.to_uint (gauss_accepted_values
    (gauss_stream_events (gr_candidate_stream candidates) (size candidates))) =
  map fst (filter snd (map gr_candidate_observer candidates)).
proof.
  rewrite gr_candidate_stream_events /gauss_accepted_values.
  elim: candidates => [|p tail ih] //=.
  rewrite gr_candidate_event_accept.
  case ((gr_candidate_observer p).`2) => ha /=; rewrite ih;
    by rewrite /gr_candidate_observer /=.
qed.

lemma gr_candidate_stream_accept_count candidates :
  count gauss_event_accepted
    (gauss_stream_events (gr_candidate_stream candidates) (size candidates)) =
  count snd (map gr_candidate_observer candidates).
proof.
  have h := congr1 List.size _ _ (gr_candidate_stream_accepted candidates).
  by move: h; rewrite /gauss_accepted_values !size_map !size_filter.
qed.

lemma gr_candidate_pairs_iid p t :
  dmap (dlist (gr_candidate_distribution p) t) (map gr_candidate_observer) =
    dlist (sc_actual_pair p) t.
proof. by rewrite -dlist_dmap gr_candidate_distribution_pair. qed.

lemma gr_candidate_stream_pairs_iid p t : 0 <= t =>
  dmap (dlist (gr_candidate_distribution p) t)
    (fun candidates => map gr_event_pair
      (gauss_stream_events (gr_candidate_stream candidates) t)) =
    dlist (sc_actual_pair p) t.
proof.
  move=> ht; rewrite -(gr_candidate_pairs_iid p t).
  apply eq_dmap_in => candidates hc /=.
  have hs := supp_dlist_size (gr_candidate_distribution p) t candidates ht hc.
  by rewrite -hs gr_candidate_stream_pairs.
qed.

lemma gr_candidate_stream_accepted_iid p t : 0 <= t =>
  dmap (dlist (gr_candidate_distribution p) t)
    (fun candidates => map W64.to_uint (gauss_accepted_values
      (gauss_stream_events (gr_candidate_stream candidates) t))) =
  dmap (dlist (sc_actual_pair p) t) (fun pairs => map fst (filter snd pairs)).
proof.
  move=> ht; rewrite -(gr_candidate_pairs_iid p t) dmap_comp.
  apply eq_dmap_in => candidates hc /=.
  have hs := supp_dlist_size (gr_candidate_distribution p) t candidates ht hc.
  by rewrite -hs gr_candidate_stream_accepted.
qed.
