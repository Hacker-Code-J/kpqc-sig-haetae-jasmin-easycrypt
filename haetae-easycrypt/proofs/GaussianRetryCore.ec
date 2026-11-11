require import AllCore Distr Dexcepted StdRing StdOrder.
import RField RealOrder.

op gr_accept (r : int * bool) : bool = r.`2.
op gr_reject (d : (int * bool) distr) (r : int * bool) : bool = !gr_accept r.
op gr_draw_distribution (d : (int * bool) distr) : (int * bool) distr = d.

op [opaque] gr_output (d : (int * bool) distr) : int distr =
  dmap (dcond d gr_accept) (fun (r : int * bool) => r.`1).

(* Every abstract parameter of the standard rejection-loop theorem is
   instantiated with a concrete type or an explicitly defined operation. *)
clone Dexcepted.WhileSampling as GRWhile with
  type input <- (int * bool) distr,
  type t <- int * bool,
  op dt <- gr_draw_distribution.

(* This is the executable unbounded retry loop. Conditioning occurs only
   in its proved output specification, never in a draw performed here. *)
module GaussianRetry = {
  proc sample(d : (int * bool) distr) : int = {
    var r : int * bool;
    r <$ d;
    while (!r.`2) {
      r <$ d;
    }
    return r.`1;
  }
}.

lemma gr_excepted_conditioned (d : (int * bool) distr) :
  d \ (gr_reject d) = dcond d gr_accept.
proof. by rewrite /(\) /dcond /predC /gr_reject /gr_accept /=. qed.

lemma gr_output_ll (d : (int * bool) distr) :
  0%r < mu d gr_accept => is_lossless (gr_output d).
proof.
  move=> ha; rewrite /gr_output; apply dmap_ll.
  exact (dcond_ll d gr_accept ha).
qed.

lemma gr_retry_clone_equiv :
  equiv [GaussianRetry.sample ~ GRWhile.SampleW.sample :
    d{1} = i{2} /\ test{2} = gr_reject ==> res{1} = res{2}.`1].
proof.
  proc; inline GRWhile.SampleWi.sample; wp.
  while (d{1} = i{2} /\ d{1} = i0{2} /\ r{1} = r0{2} /\
    test0{2} = gr_reject).
  + by auto => />; rewrite /gr_reject /gr_accept /gr_draw_distribution.
  by auto => />; rewrite /gr_reject /gr_accept /gr_draw_distribution.
qed.

lemma gr_retry_clone_law (d : (int * bool) distr) (event : int -> bool) &m :
  Pr[GaussianRetry.sample(d) @ &m : event res] =
  Pr[GRWhile.SampleW.sample(d, gr_reject) @ &m : event res.`1].
proof. by byequiv gr_retry_clone_equiv. qed.

lemma gr_retry_law (d : (int * bool) distr) (event : int -> bool) &m :
  is_lossless d => 0%r < mu d gr_accept =>
  Pr[GaussianRetry.sample(d) @ &m : event res] = mu (gr_output d) event.
proof.
  move=> hd ha.
  rewrite gr_retry_clone_law (GRWhile.pr_sampleW &m d gr_reject
    (fun (r : int * bool) => event r.`1)) 1:hd.
  by rewrite /gr_draw_distribution gr_excepted_conditioned /gr_output dmapE /(\o).
qed.

lemma gr_retry_phoare (d0 : (int * bool) distr) (event : int -> bool) :
  is_lossless d0 => 0%r < mu d0 gr_accept =>
  phoare [GaussianRetry.sample : d = d0 ==> event res] = (mu (gr_output d0) event).
proof.
  move=> hd ha; bypr => &m ->.
  exact (gr_retry_law d0 event &m hd ha).
qed.

lemma gr_retry_total (d0 : (int * bool) distr) :
  is_lossless d0 => 0%r < mu d0 gr_accept =>
  phoare [GaussianRetry.sample : d = d0 ==> true] = 1%r.
proof.
  move=> hd ha.
  have h := gr_retry_phoare d0 (fun _ => true) hd ha.
  have hw : mu (gr_output d0) (fun _ => true) = 1%r by exact (gr_output_ll d0 ha).
  by move: h; rewrite hw.
qed.

lemma gr_retry_lossless :
  phoare [GaussianRetry.sample :
    is_lossless d /\ 0%r < mu d gr_accept ==> true] = 1%r.
proof.
  bypr => &m [hd ha].
  rewrite (gr_retry_law d{m} (fun _ => true) &m hd ha).
  exact (gr_output_ll d{m} ha).
qed.
