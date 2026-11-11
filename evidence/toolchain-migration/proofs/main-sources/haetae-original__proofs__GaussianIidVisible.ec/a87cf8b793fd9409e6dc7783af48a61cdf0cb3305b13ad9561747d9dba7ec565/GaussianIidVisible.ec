require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianIidBufferPath GaussianTraceSpec
  GaussianTraceProperties GaussianSequenceCorrectness GaussianStreamComposition
  GaussianWindowSpec GaussianIidProgress GaussianBlockSampling
  GaussianRetryInputs GaussianUniformBytes.

lemma giv_size values offset accepted : 0 <= accepted =>
  size (gib_visible values offset accepted) = min accepted 256.
proof. move=> ha; rewrite /gib_visible size_map size_iota; smt(). qed.

lemma giv_nth values offset accepted j : 0 <= j < min accepted 256 =>
  nth 0 (gib_visible values offset accepted) j =
    W64.to_uint (BArray32768.get64 values (offset+j)).
proof.
  move=> hj; rewrite /gib_visible (nth_map 0) 1:size_iota 1:/# nth_iota 1:/# /=.
  trivial.
qed.

lemma giv_empty values offset : gib_visible values offset 0 = [].
proof. by rewrite /gib_visible /= iota0. qed.

lemma giv_terminal (result : gib_result) offset accepted : 256 <= accepted =>
  gib_visible result.`1 offset accepted = gib_magnitudes result offset.
proof. move=> h; rewrite /gib_visible /gib_magnitudes; congr; smt(). qed.

lemma giv_local_limit n accepted : (n=256 \/ n=257) => 0 <= accepted < n =>
  gauss_visible_limit (n-accepted) (n=257) = 256-accepted.
proof. rewrite /gauss_visible_limit; smt(). qed.

lemma giv_old_prefix values squares count pending n accepted offset j :
  (n=256 \/ n=257) => 0 <= accepted < n =>
  0 <= offset => offset+n <= 4096 => 0 <= j < accepted =>
  BArray32768.get64
    (gib_consume values squares count pending (n-accepted) (n=257) (offset+accepted)).`1
    (offset+j) = BArray32768.get64 values (offset+j).
proof.
  move=> hn ha ho hcap hj.
  rewrite /gib_consume /= gib_commit_get 1:/# 1:/# 1:/# 1:/#.
  smt().
qed.

lemma giv_new_value values squares count pending n accepted offset j :
  (n=256 \/ n=257) => 0 <= accepted < n =>
  0 <= offset => offset+n <= 4096 =>
  let result = gib_consume values squares count pending (n-accepted) (n=257) (offset+accepted) in
  let q = W64.to_uint (BArray8.get64 result.`3 0) in
  accepted <= j < min (accepted+q) 256 =>
  W64.to_uint (BArray32768.get64 result.`1 (offset+j)) =
    nth 0 (gib_accepted pending) (j-accepted).
proof.
  move=> hn ha ho hcap /= hj.
  pose local_result := gauss_trace_result (BArray8192.of_list pending) (n-accepted)
    (size pending) (n=257) (gauss_output_window values (offset+accepted)) squares count.
  pose q := W64.to_uint (BArray8.get64 local_result.`3 0).
  have hreq : 0 <= n-accepted <= 512 by smt().
  have hav := size_ge0 pending.
  have hc := gib_consume_count values squares count pending (n-accepted) (n=257)
    (offset+accepted) hreq.
  have hq : q = min (n-accepted) (size (gib_accepted pending)) by
    move: hc; rewrite /gib_consume /= /q /local_result.
  have hj' : accepted <= j < min (accepted+q) 256 by
    move: hj; rewrite /gib_consume /= /q /local_result.
  have hv := giv_local_limit n accepted hn ha.
  have hidx : 0 <= j-accepted < min q (gauss_visible_limit (n-accepted) (n=257)) by
    rewrite hv; smt().
  have hval := gs_trace_value_at (BArray8192.of_list pending) (n-accepted)
    (size pending) (n=257) (gauss_output_window values (offset+accepted)) squares count
    (j-accepted) hreq hav hidx.
  have hsize : j-accepted < size (gauss_accepted_values
    (gauss_events (BArray8192.of_list pending) (size pending %/ 26))) by
    move: hq; rewrite /gib_accepted size_map; smt().
  rewrite /gib_consume /= -/local_result gib_commit_get 1:/# 1:hreq 1:/# 1:/#.
  have hin : offset+accepted <= offset+j < offset+accepted+(n-accepted) by smt().
  rewrite hin /=.
  have he : offset+j-(offset+accepted) = j-accepted by ring.
  rewrite he hval nth_take 1:/# 1:/#.
  by rewrite /gib_accepted (nth_map W64.zero) 1:/#.
qed.

(* The visible demand is256 even when the actual request includes a
   257th accepted dummy. Speculative rejected writes stay outside this list. *)
lemma giv_consume values squares count pending n accepted offset :
  (n=256 \/ n=257) => 0 <= accepted < n =>
  0 <= offset => offset+n <= 4096 =>
  let result = gib_consume values squares count pending (n-accepted) (n=257) (offset+accepted) in
  let q = W64.to_uint (BArray8.get64 result.`3 0) in
  q = min (n-accepted) (size (gib_accepted pending)) /\
  gib_visible result.`1 offset (accepted+q) =
    take 256 (gib_visible values offset accepted ++ gib_accepted pending).
proof.
  move=> hn ha ho hcap /=.
  pose result := gib_consume values squares count pending (n-accepted) (n=257) (offset+accepted).
  pose q := W64.to_uint (BArray8.get64 result.`3 0).
  have hreq : 0 <= n-accepted <= 512 by smt().
  have hq : q = min (n-accepted) (size (gib_accepted pending)) by
    exact (gib_consume_count values squares count pending (n-accepted) (n=257) (offset+accepted) hreq).
  have hz := size_ge0 (gib_accepted pending).
  have hqbounds : 0 <= q <= n-accepted by smt().
  have hbefore : size (gib_visible values offset accepted) = accepted by
    rewrite giv_size 1:/#; smt().
  split; first exact hq.
  apply (List.eq_from_nth 0).
  + rewrite giv_size 1:/# size_take 1:// size_cat hbefore; smt().
  move=> j hj.
  have hj' : 0 <= j < min (accepted+q) 256 by move: hj; rewrite giv_size 1:/#.
  rewrite giv_nth 1:hj' nth_take 1:/# 1:/# nth_cat hbefore.
  case (j < accepted) => hpart.
  + rewrite giv_nth 1:/#.
    have hjold : 0 <= j < accepted by smt().
    have hp := giv_old_prefix values squares count pending n accepted offset j hn ha ho hcap hjold.
    exact (congr1 W64.to_uint _ _ hp).
  have hjnew : accepted <= j < min (accepted+q) 256 by smt().
  exact (giv_new_value values squares count pending n accepted offset j hn ha ho hcap hjnew).
qed.

lemma giv_consume_scan values squares count pending n accepted offset :
  (n=256 \/ n=257) => 0 <= accepted < n =>
  0 <= offset => offset+n <= 4096 => size pending <= 8192 =>
  let result = gib_consume values squares count pending (n-accepted) (n=257) (offset+accepted) in
  let q = W64.to_uint (BArray8.get64 result.`3 0) in
  gib_visible result.`1 offset (accepted+q) =
    gbs_scan 256 (gib_visible values offset accepted)
      (map gr_candidate_observer (gbc_chunks (size pending %/ 26) pending)).
proof.
  move=> hn ha ho hcap hbytes /=.
  have [_ hv] := giv_consume values squares count pending n accepted offset hn ha ho hcap.
  have hsize : size (gib_visible values offset accepted) <= 256 by
    rewrite giv_size 1:/#; smt().
  rewrite gbs_scan_filter 1:hsize -(gip_accepted_chunks pending hbytes).
  exact hv.
qed.

lemma giv_consume_fold values squares count pending n accepted offset :
  (n=256 \/ n=257) => 0 <= accepted < n =>
  0 <= offset => offset+n <= 4096 => size pending <= 8192 =>
  let result = gib_consume values squares count pending (n-accepted) (n=257) (offset+accepted) in
  let q = W64.to_uint (BArray8.get64 result.`3 0) in
  gib_visible result.`1 offset (accepted+q) =
    foldl (fun vs candidate => gbs_step 256 vs (gr_candidate_observer candidate))
      (gib_visible values offset accepted) (gbc_chunks (size pending %/ 26) pending).
proof.
  move=> hn ha ho hcap hbytes /=.
  have h := giv_consume_scan values squares count pending n accepted offset hn ha ho hcap hbytes.
  by move: h; rewrite /gbs_scan foldl_map.
qed.
