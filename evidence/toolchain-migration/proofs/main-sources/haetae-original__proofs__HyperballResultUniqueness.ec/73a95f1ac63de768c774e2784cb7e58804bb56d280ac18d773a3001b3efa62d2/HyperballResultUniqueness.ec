require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import HyperballSpec HyperballBatchCorrectness HyperballGaussianBounds
  HyperballHistoryCorrectness HyperballScaleSpec GaussianStreamSpec GaussianStreamBuffer
  GaussianStreamAccumulator GaussianTraceSpec GaussianTraceProperties.
import HyperballScaleSpec.

lemma hb_poly_events_complete_unique seed base i block1 block2 :
  49 <= block1 => 49 <= block2 =>
  size (hb_poly_events seed base i block1) = hb_request i =>
  size (hb_poly_events seed base i block2) = hb_request i =>
  hb_poly_events seed base i block1 = hb_poly_events seed base i block2.
proof.
  move=> hb1 hb2 hc1 hc2.
  have ha1 := gs_stream_bounds block1 hb1.
  have ha2 := gs_stream_bounds block2 hb2.
  have hn := hb_request_shape i.
  rewrite /hb_poly_events in hc1.
  rewrite /hb_poly_events in hc2.
  rewrite /hb_poly_events.
  apply gs_selected_complete_unique; smt().
qed.

lemma hb_batch_sum_prefix_extensional seed base blocks1 blocks2 k :
  size blocks1 = size blocks2 =>
  (forall i, 0 <= i < size blocks1 =>
    hb_poly_events seed base i (nth 0 blocks1 i) =
      hb_poly_events seed base i (nth 0 blocks2 i)) =>
  0 <= k => k <= size blocks1 =>
  hb_batch_sum seed base (take k blocks1) = hb_batch_sum seed base (take k blocks2).
proof.
  move=> hsize hevents hk; elim: k hk => [|k hk ih] hkle.
  + by rewrite !take0 !hb_batch_sum_nil.
  have hk1 : 0 <= k < size blocks1 by smt().
  have hk2 : 0 <= k < size blocks2 by smt().
  have hs1 : size (take k blocks1) = k by apply size_takel; smt().
  have hs2 : size (take k blocks2) = k by apply size_takel; smt().
  have hprefix := ih _; first smt().
  rewrite (take_nth 0 k blocks1 hk1) (take_nth 0 k blocks2 hk2)
    -!cats1 !hb_batch_sum_append hs1 hs2 hprefix (hevents k hk1).
  trivial.
qed.

lemma hb_batch_sum_extensional seed base blocks1 blocks2 :
  size blocks1 = size blocks2 =>
  (forall i, 0 <= i < size blocks1 =>
    hb_poly_events seed base i (nth 0 blocks1 i) =
      hb_poly_events seed base i (nth 0 blocks2 i)) =>
  hb_batch_sum seed base blocks1 = hb_batch_sum seed base blocks2.
proof.
  move=> hsize hevents.
  have hsum := hb_batch_sum_prefix_extensional seed base blocks1 blocks2
    (size blocks1) hsize hevents (size_ge0 blocks1) _; first trivial.
  have ht2 : take (size blocks1) blocks2 = blocks2 by apply take_oversize; smt().
  by move: hsum; rewrite take_size ht2.
qed.

(* A completed draw does not determine unused sample/sign scratch tails.
   It does determine every entry consumed by scaling, and its entire norm. *)
lemma hb_batch_complete_unique seed base m (draw1 draw2 : hb_draw) :
  hb_batch_complete seed base m draw1 => hb_batch_complete seed base m draw2 =>
  (forall j, 0 <= j < 256 * m =>
    BArray32768.get64 draw1.`1 j = BArray32768.get64 draw2.`1 j) /\
  (forall j, 0 <= j < 32 * m =>
    BArray512.get8 draw1.`2 j = BArray512.get8 draw2.`2 j) /\
  draw1.`3 = draw2.`3.
proof.
  move=> [blocks1 [hlen1 hp1]] [blocks2 [hlen2 hp2]].
  have [hr1 [hpoly1 [hcanonical1 hvalue1]]] := hp1.
  have [hr2 [hpoly2 [hcanonical2 hvalue2]]] := hp2.
  have hsize : size blocks1 = size blocks2 by smt().
  have hevents : forall i, 0 <= i < size blocks1 =>
    hb_poly_events seed base i (nth 0 blocks1 i) =
      hb_poly_events seed base i (nth 0 blocks2 i).
  + move=> i hi.
    have hi2 : 0 <= i < size blocks2 by smt().
    have [hb1 [hc1 _]] := hpoly1 i hi.
    have [hb2 [hc2 _]] := hpoly2 i hi2.
    exact (hb_poly_events_complete_unique seed base i _ _ hb1 hb2 hc1 hc2).
  split.
  + move=> j hj.
    have hq : 0 <= j %/ 256 < m by apply divz_cmp; smt().
    have hr := modz_cmp j 256.
    have hd := divz_eq j 256.
    have hi1 : 0 <= j %/ 256 < size blocks1 by smt().
    have hi2 : 0 <= j %/ 256 < size blocks2 by smt().
    have [_ [_ [hv1 _]]] := hpoly1 (j %/ 256) hi1.
    have [_ [_ [hv2 _]]] := hpoly2 (j %/ 256) hi2.
    have hrem : 0 <= j %% 256 < 256 by smt().
    have h1 := hv1 (j %% 256) hrem.
    have h2 := hv2 (j %% 256) hrem.
    have he := hevents (j %/ 256) hi1.
    have hindex : 256 * (j %/ 256) + j %% 256 = j by smt().
    move: h1 h2; rewrite hindex he; smt().
  split.
  + move=> j hj.
    have hq : 0 <= j %/ 32 < m by apply divz_cmp; smt().
    have hr := modz_cmp j 32.
    have hd := divz_eq j 32.
    have hi1 : 0 <= j %/ 32 < size blocks1 by smt().
    have hi2 : 0 <= j %/ 32 < size blocks2 by smt().
    have [_ [_ [_ hs1]]] := hpoly1 (j %/ 32) hi1.
    have [_ [_ [_ hs2]]] := hpoly2 (j %/ 32) hi2.
    have hrem : 0 <= j %% 32 < 32 by smt().
    have h1 := hs1 (j %% 32) hrem.
    have h2 := hs2 (j %% 32) hrem.
    have hindex : 32 * (j %/ 32) + j %% 32 = j by smt().
    move: h1 h2; rewrite hindex; smt().
  have hc1 := hb_cumulative_canonical _ _ hcanonical1.
  have hc2 := hb_cumulative_canonical _ _ hcanonical2.
  have hsum := hb_batch_sum_extensional seed base blocks1 blocks2 hsize hevents.
  apply gs_canonical_square_unique; smt().
qed.

lemma hb_attempt_outputs_unique seed base initial1 initial2 l k cube three scale
    (draw1 draw2 : hb_draw) :
  hb_shape l k =>
  hb_batch_complete seed base (l + k) draw1 => hb_batch_complete seed base (l + k) draw2 =>
  hb_attempt_outputs initial1 initial2 draw1 l k cube three scale =
    hb_attempt_outputs initial1 initial2 draw2 l k cube three scale.
proof.
  move=> hshape hd1 hd2.
  have [hsamples [hsigns hsquares]] := hb_batch_complete_unique seed base (l + k) draw1 draw2 hd1 hd2.
  have hscale : hb_draw_scale draw1 cube three scale = hb_draw_scale draw2 cube three scale
    by rewrite /hb_draw_scale hsquares.
  rewrite /hb_attempt_outputs hscale.
  apply hb_scale_result_extensional.
  + exact (hb_shape_scale_bounds l k hshape).
  + exact hsamples.
  + move=> j hj; apply hsigns; smt().
  + by move=> j hj.
  by move=> j hj.
qed.

lemma hb_attempt_accept_unique seed base initial1 initial2 l k cube three scale bound
    (draw1 draw2 : hb_draw) :
  hb_shape l k =>
  hb_batch_complete seed base (l + k) draw1 => hb_batch_complete seed base (l + k) draw2 =>
  hb_attempt_accept initial1 initial2 draw1 l k cube three scale bound =
    hb_attempt_accept initial1 initial2 draw2 l k cube three scale bound.
proof.
  move=> hshape hd1 hd2.
  by rewrite /hb_attempt_accept
    (hb_attempt_outputs_unique seed base initial1 initial2 l k cube three scale draw1 draw2 hshape hd1 hd2).
qed.

lemma hb_history_accepts_last seed base l k cube three scale bound initial1 initial2
    history current1 current2 :
  0 < size history =>
  hb_history seed base l k cube three scale bound initial1 initial2 history
    current1 current2 W64.one =>
  hb_attempt_accept initial1 initial2 (nth witness history (size history - 1))
    l k cube three scale bound.
proof.
  move=> hsize [hcomplete [hrejected hlast]].
  have hne : history <> [] by smt(size_eq0).
  have hflag : W64.of_int (b2i (hb_attempt_accept initial1 initial2
      (last witness history) l k cube three scale bound)) = W64.one by smt().
  move: hflag; rewrite hb_boolean_word_one nth_last; trivial.
qed.

lemma hb_accepted_history_length_unique seed base l k cube three scale bound initial1 initial2
    history1 history2 current11 current12 current21 current22 :
  hb_shape l k => 0 < size history1 => 0 < size history2 =>
  hb_history seed base l k cube three scale bound initial1 initial2 history1
    current11 current12 W64.one =>
  hb_history seed base l k cube three scale bound initial1 initial2 history2
    current21 current22 W64.one => size history1 = size history2.
proof.
  move=> hshape hs1 hs2 hh1 hh2.
  have hlast1 := hb_history_accepts_last seed base l k cube three scale bound
    initial1 initial2 history1 current11 current12 hs1 hh1.
  have hlast2 := hb_history_accepts_last seed base l k cube three scale bound
    initial1 initial2 history2 current21 current22 hs2 hh2.
  have [hc1 [hr1 _]] := hh1.
  have [hc2 [hr2 _]] := hh2.
  case (size history1 < size history2) => hlt.
  + have hd1 := hc1 (size history1 - 1) _; first smt().
    have hd2 := hc2 (size history1 - 1) _; first smt().
    have hreject := hr2 (size history1 - 1) _; first smt().
    have he := hb_attempt_accept_unique seed
      (hb_nonce base ((l + k) * (size history1 - 1))) initial1 initial2 l k
      cube three scale bound (nth witness history1 (size history1 - 1))
      (nth witness history2 (size history1 - 1)) hshape hd1 hd2.
    smt().
  case (size history2 < size history1) => hgt; last smt().
  have hd1 := hc1 (size history2 - 1) _; first smt().
  have hd2 := hc2 (size history2 - 1) _; first smt().
  have hreject := hr1 (size history2 - 1) _; first smt().
  have he := hb_attempt_accept_unique seed
    (hb_nonce base ((l + k) * (size history2 - 1))) initial1 initial2 l k
    cube three scale bound (nth witness history1 (size history2 - 1))
    (nth witness history2 (size history2 - 1)) hshape hd1 hd2.
  smt().
qed.

(* Valid finite histories must end at the same first accepting attempt.
   The nonce word may wrap; no injectivity assumption on nonce arithmetic
   is needed because the same attempt index has the same concrete nonce. *)
lemma hb_result_unique seed base l k cube three scale bound initial1 initial2
    current11 current12 byte1 counter1 current21 current22 byte2 counter2 :
  hb_shape l k =>
  hb_result seed base l k cube three scale bound initial1 initial2
    current11 current12 byte1 counter1 =>
  hb_result seed base l k cube three scale bound initial1 initial2
    current21 current22 byte2 counter2 =>
  current11 = current21 /\ current12 = current22 /\ byte1 = byte2 /\ counter1 = counter2.
proof.
  move=> hshape [history1 [hs1 [hh1 [hbyte1 hcounter1]]]]
    [history2 [hs2 [hh2 [hbyte2 hcounter2]]]].
  have hlength := hb_accepted_history_length_unique seed base l k cube three scale bound
    initial1 initial2 history1 history2 current11 current12 current21 current22
    hshape hs1 hs2 hh1 hh2.
  have [hc1 [hr1 hout1]] := hh1.
  have [hc2 [hr2 hout2]] := hh2.
  have hne1 : history1 <> [] by smt(size_eq0).
  have hne2 : history2 <> [] by smt(size_eq0).
  have hpair1 : (current11, current12) = hb_attempt_outputs initial1 initial2
      (last witness history1) l k cube three scale by smt().
  have hpair2 : (current21, current22) = hb_attempt_outputs initial1 initial2
      (last witness history2) l k cube three scale by smt().
  have hd1 := hc1 (size history1 - 1) _; first smt().
  rewrite nth_last in hd1.
  have hindex2 : nth witness history2 (size history1 - 1) = last witness history2
    by rewrite hlength nth_last.
  have hd2 := hc2 (size history1 - 1) _; first smt().
  rewrite hindex2 in hd2.
  have hout := hb_attempt_outputs_unique seed
    (hb_nonce base ((l + k) * (size history1 - 1))) initial1 initial2 l k
    cube three scale (last witness history1) (last witness history2) hshape hd1 hd2.
  have hbytes : byte1 = byte2.
  + apply BArray1.ext_eq => j hj.
    have -> : j = 0 by smt().
    by rewrite hbyte1 hbyte2 hlength.
  have hcounters : counter1 = counter2.
  + apply BArray8.ext_eq64 => j hj.
    have -> : j = 0 by smt().
    by rewrite hcounter1 hcounter2 hlength.
  smt().
qed.
