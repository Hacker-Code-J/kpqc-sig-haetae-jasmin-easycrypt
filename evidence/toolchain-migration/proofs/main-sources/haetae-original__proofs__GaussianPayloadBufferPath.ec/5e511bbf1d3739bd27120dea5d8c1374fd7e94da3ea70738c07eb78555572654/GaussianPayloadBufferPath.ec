require import AllCore IntDiv List Distr DList.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianIidBufferPath GaussianIidNormalization
  GaussianIidTermination GaussianIidDistribution GaussianIidProgress
  GaussianUniformBytes GaussianRetryInputs GaussianTraceProperties GaussianBlockSampling
  GaussianPayloadSpec GaussianPayloadBufferSpec.

lemma gpb_observer_accept (candidate : BArray26.t) :
  (gpd_observer candidate).`2 = (gr_candidate_observer candidate).`2.
proof.
  by rewrite /gpd_observer /gr_candidate_observer /gauss_event_accepted /=
    W64.to_uint_eq W64.to_uint1.
qed.

lemma gpb_observer_count (candidates : BArray26.t list) :
  size (filter snd (map gpd_observer candidates)) =
  size (filter snd (map gr_candidate_observer candidates)).
proof.
  elim: candidates => [|candidate tail ih]; first trivial.
  rewrite /= gpb_observer_accept.
  by case ((gr_candidate_observer candidate).`2); rewrite /= ih.
qed.

lemma gpb_scan_size n history pending :
  size history <= n => size pending <= 8192 =>
  size (gpd_scan n history pending) = min n (size history+size (gib_accepted pending)).
proof.
  move=> hh hp.
  have hn : 0 <= n by smt(size_ge0).
  have hc : size (filter snd (map gpd_observer (gbc_chunks (size pending %/ 26) pending))) =
      size (gib_accepted pending).
  + by rewrite (gip_accepted_chunks pending hp) size_map gpb_observer_count.
  by rewrite /gpd_scan (gbs_scan_filter n history _ hh)
    size_take 1:hn size_cat size_map hc.
qed.

lemma gpb_scan_bounds n history pending :
  size history <= n => size history <= size (gpd_scan n history pending) <= n.
proof.
  move=> hh; rewrite /gpd_scan; exact (gbs_scan_size n history _ hh).
qed.

lemma gpb_consume_count values squares count pending n history dummy offset :
  size history <= n <= 512 => size pending <= 8192 =>
  size (gpd_scan n history pending) = size history +
    W64.to_uint (BArray8.get64
      (gib_consume values squares count pending (n-size history) dummy offset).`3 0).
proof.
  move=> hn hp.
  have hreq : 0 <= n-size history <= 512 by smt(size_ge0).
  have hh : size history <= n by smt().
  rewrite (gpb_scan_size n history pending hh hp)
    (gib_consume_count values squares count pending (n-size history) dummy offset hreq).
  rewrite /min; smt().
qed.

lemma gpb_initial_size (bytes : W8.t list) : bytes \in gbc_bytes 6664 =>
  size (drop 32 bytes) = 6632.
proof.
  move=> hb; have hs := supp_dlist_size W8.dword 6664 bytes _ hb; first trivial.
  by rewrite size_drop 1:// hs.
qed.

lemma gpb_refill_size pending bytes : bytes \in gib_block =>
  136 <= size (gib_remainder pending ++ bytes) <= 161.
proof.
  move=> hb; have hs := gib_block_size bytes hb.
  have [hr hbnd] := gib_remainder_size pending.
  rewrite size_cat hs; smt().
qed.

lemma gpb_uniform_projection :
  equiv [GaussianIidBufferUniform.sample ~ GaussianPayloadBuffer.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} ==> res{1}=res{2}.`1].
proof.
  proc.
  while (={rp,signsp,sqsump,n,sample_offset,sign_offset,count,pending,accepted}).
  + by wp; rnd; wp; skip; auto.
  by wp; rnd; wp; skip; auto.
qed.

lemma gpb_functional_projection :
  equiv [GaussianIidBufferFunctional.sample ~ GaussianPayloadBuffer.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} ==> res{1}=res{2}.`1].
proof.
  transitivity GaussianIidBufferUniform.sample
    (={rp,signsp,sqsump,n,sample_offset,sign_offset} ==> ={res})
    (={rp,signsp,sqsump,n,sample_offset,sign_offset} ==> res{1}=res{2}.`1).
  + move=> &1 &2 h; exists (rp{2},signsp{2},sqsump{2},n{2},sample_offset{2},sign_offset{2}); smt().
  + smt().
  + exact gid_functional_uniform.
  exact gpb_uniform_projection.
qed.

lemma gpb_actual_projection :
  equiv [GaussianIidBuffer.sample ~ GaussianPayloadBuffer.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} /\
    gib_bounds n{1} sample_offset{1} sign_offset{1} ==> res{1}=res{2}.`1].
proof.
  transitivity GaussianIidBufferFunctional.sample
    (={rp,signsp,sqsump,n,sample_offset,sign_offset} /\
     gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res})
    (={rp,signsp,sqsump,n,sample_offset,sign_offset} ==> res{1}=res{2}.`1).
  + move=> &1 &2 h; exists (rp{2},signsp{2},sqsump{2},n{2},sample_offset{2},sign_offset{2}); smt().
  + smt().
  + exact gib_actual_functional.
  exact gpb_functional_projection.
qed.

lemma gpb_history_projection :
  equiv [GaussianPayloadBuffer.sample ~ GaussianPayloadHistory.sample :
    n{1}=n{2} /\ 0 <= n{1} <= 512 ==> res{1}.`2=res{2}].
proof.
  proc.
  while (={n,pending,history} /\ accepted{1}=size history{2} /\
    0 <= accepted{1} <= n{1} /\ n{1} <= 512 /\ size pending{1} <= 8192).
  + wp; rnd; wp; skip; auto => />.
    move=> &1 &2 hh0 hhn hn512 hp hguard bytes hbytes.
    have hs := gpb_refill_size pending{2} bytes hbytes.
    have hc : size history{2} <= n{2} <= 512 by smt().
    have hb : size (gib_remainder pending{2} ++ bytes) <= 8192 by smt().
    have hcount := gpb_consume_count rp{1} sqsump{1} count{1}
      (gib_remainder pending{2} ++ bytes) n{2} history{2} (n{2}=257)
      (sample_offset{1}+size history{2}) hc hb.
    have hrange := gpb_scan_bounds n{2} history{2}
      (gib_remainder pending{2} ++ bytes) hhn.
    smt().
  wp; rnd; wp; skip; auto => />.
  move=> &1 &2 hn0 hn512 pending hpending.
  have hs := gpb_initial_size pending hpending.
  have hc : 0 <= n{2} <= 512 by smt().
  have hb : size (drop 32 pending) <= 8192 by smt().
  have hcount := gpb_consume_count rp{1} sqsump{1} witness (drop 32 pending)
    n{2} [] (n{2}=257) sample_offset{1} hc hb.
  have hh : 0 <= n{2} by smt().
  have hrange := gpb_scan_bounds n{2} [] (drop 32 pending) hh.
  rewrite /= in hcount; rewrite /= in hrange.
  smt().
qed.

lemma gpb_functional_projection_law initial initial_signs initial_squares n offset signoff
    (event : gib_result -> bool) &m :
  Pr[GaussianIidBufferFunctional.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event res] =
  Pr[GaussianPayloadBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event res.`1].
proof. by byequiv gpb_functional_projection. qed.

lemma gpb_actual_projection_law initial initial_signs initial_squares n offset signoff
    (event : gib_result -> bool) &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event res] =
  Pr[GaussianPayloadBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event res.`1].
proof. move=> hb; by byequiv gpb_actual_projection. qed.

lemma gpb_buffer_terminates initial initial_signs initial_squares n offset signoff &m :
  0 <= n <= 512 =>
  Pr[GaussianPayloadBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : true] = 1%r.
proof.
  move=> hn.
  have he := gpb_functional_projection_law initial initial_signs initial_squares n offset signoff
    (fun _ => true) &m.
  rewrite /= in he; rewrite -he.
  by byphoare (git_functional_range_total n hn).
qed.

lemma gpb_buffer_lossless :
  phoare [GaussianPayloadBuffer.sample : 0 <= n <= 512 ==> true] = 1%r.
proof.
  bypr => &m hn.
  exact (gpb_buffer_terminates rp{m} signsp{m} sqsump{m} n{m}
    sample_offset{m} sign_offset{m} &m hn).
qed.

lemma gpb_history_projection_law initial initial_signs initial_squares n offset signoff
    (event : int list -> bool) &m :
  0 <= n <= 512 =>
  Pr[GaussianPayloadBuffer.sample(initial,initial_signs,initial_squares,n,offset,signoff)
    @ &m : event res.`2] =
  Pr[GaussianPayloadHistory.sample(n) @ &m : event res].
proof. move=> hn; by byequiv gpb_history_projection. qed.

lemma gpb_history_terminates n &m : 0 <= n <= 512 =>
  Pr[GaussianPayloadHistory.sample(n) @ &m : true] = 1%r.
proof.
  move=> hn.
  have he := gpb_history_projection_law witness witness witness n 0 0 (fun _ => true) &m hn.
  rewrite /= in he; rewrite -he.
  exact (gpb_buffer_terminates witness witness witness n 0 0 &m hn).
qed.

lemma gpb_history_lossless :
  phoare [GaussianPayloadHistory.sample : 0 <= n <= 512 ==> true] = 1%r.
proof. bypr => &m hn; exact (gpb_history_terminates n{m} &m hn). qed.

lemma gpb_history_total n0 : 0 <= n0 <= 512 =>
  phoare [GaussianPayloadHistory.sample : n=n0 ==> true] = 1%r.
proof. move=> hn; by conseq gpb_history_lossless => />. qed.

lemma gpb_history_size_correct n0 : 0 <= n0 =>
  hoare [GaussianPayloadHistory.sample : n=n0 ==> size res=n0].
proof.
  move=> hn; proc.
  while (n=n0 /\ size history <= n0).
  + wp; rnd; wp; skip; auto => />; smt(gpb_scan_bounds).
  wp; rnd; wp; skip; auto => />; smt(gpb_scan_bounds).
qed.

lemma gpb_history_size_total n0 : 0 <= n0 <= 512 =>
  phoare [GaussianPayloadHistory.sample : n=n0 ==> size res=n0] = 1%r.
proof.
  move=> hn; conseq gpb_history_lossless (gpb_history_size_correct n0 _) => //; smt().
qed.

lemma gpb_buffer_size_total n0 : 0 <= n0 <= 512 =>
  phoare [GaussianPayloadBuffer.sample : n=n0 ==> size res.`2=n0] = 1%r.
proof.
  move=> hn; bypr => &m hn0.
  have he := gpb_history_projection_law rp{m} signsp{m} sqsump{m} n0
    sample_offset{m} sign_offset{m} (fun history => size history=n0) &m hn.
  rewrite hn0 he.
  by byphoare (gpb_history_size_total n0 hn).
qed.
