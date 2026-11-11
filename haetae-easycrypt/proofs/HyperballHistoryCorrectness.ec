require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import HyperballSpec HyperballScaleSpec HyperballFixedPointSpec HyperballNormSpec.
import HyperballScaleSpec.

lemma hb_shape_scale_bounds l k : hb_shape l k =>
  hb_scale_bounds (256 * l) (256 * (l + k)).
proof. rewrite /hb_shape /hb_scale_bounds; smt(). qed.

lemma hb_boolean_word_zero (b : bool) :
  (W64.of_int (b2i b) = W64.zero) = !b.
proof. by case: b; rewrite /b2i W64.to_uint_eq W64.of_uintK W64.to_uint0 /=. qed.

lemma hb_boolean_word_one (b : bool) :
  (W64.of_int (b2i b) = W64.one) = b.
proof. by case: b; rewrite /b2i W64.to_uint_eq W64.of_uintK W64.to_uint1 /=. qed.

lemma hb_history_initial seed base l k cube three scale bound initial1 initial2 :
  hb_history seed base l k cube three scale bound initial1 initial2 []
    initial1 initial2 W64.zero.
proof. rewrite /hb_history /=; smt(). qed.

lemma hb_history_frames seed base l k cube three scale bound initial1 initial2 history
    current1 current2 accepted :
  hb_shape l k =>
  hb_history seed base l k cube three scale bound initial1 initial2 history
    current1 current2 accepted =>
  hb_output_frame initial1 current1 (256 * l) /\
  hb_output_frame initial2 current2 (256 * k).
proof.
  move=> hshape [hcomplete [hrejected hlast]].
  have hbounds := hb_shape_scale_bounds l k hshape.
  case (history = []) => he.
  + rewrite /hb_output_frame; smt().
  have hout : (current1, current2) = hb_attempt_outputs initial1 initial2
      (last witness history) l k cube three scale by smt().
  have [_ [_ [hf1 hf2]]] := hb_scale_result_layout initial1 initial2
    (last witness history).`1 (last witness history).`2
    (hb_draw_scale (last witness history) cube three scale)
    (256 * l) (256 * (l + k)) hbounds.
  have hcount : 256 * (l + k) - 256 * l = 256 * k by ring.
  move: hf2; rewrite hcount => hf2.
  rewrite /hb_attempt_outputs in hout.
  smt().
qed.

lemma hb_scale_rebase initial1 initial2 current1 current2 samples signs scalep l k bound :
  hb_shape l k =>
  hb_output_frame initial1 current1 (256 * l) =>
  hb_output_frame initial2 current2 (256 * k) =>
  hb_scale_check_result current1 current2 samples signs scalep
    (256 * l) (256 * (l + k)) bound =
  hb_scale_check_result initial1 initial2 samples signs scalep
    (256 * l) (256 * (l + k)) bound.
proof.
  move=> hshape hf1 hf2.
  have hbounds := hb_shape_scale_bounds l k hshape.
  have he : hb_scale_result current1 current2 samples signs scalep
      (256 * l) (256 * (l + k)) =
    hb_scale_result initial1 initial2 samples signs scalep
      (256 * l) (256 * (l + k)).
  + apply hb_scale_result_extensional => //.
    move=> j hj; apply hf2; smt().
  by rewrite /hb_scale_check_result /hb_scale_norm he.
qed.

lemma hb_history_rejected seed base l k cube three scale bound initial1 initial2 history
    current1 current2 :
  hb_history seed base l k cube three scale bound initial1 initial2 history
    current1 current2 W64.zero =>
  forall j, 0 <= j < size history =>
    !hb_attempt_accept initial1 initial2 (nth witness history j) l k cube three scale bound.
proof.
  move=> [hcomplete [hrejected hlast]] j hj.
  case (j < size history - 1) => hprev; first by apply hrejected; smt().
  have hne : history <> [] by smt(size_eq0).
  have hjlast : j = size history - 1 by smt().
  have heq : W64.of_int (b2i (hb_attempt_accept initial1 initial2 (last witness history)
      l k cube three scale bound)) = W64.zero by smt().
  have hn := hb_boolean_word_zero (hb_attempt_accept initial1 initial2 (last witness history)
    l k cube three scale bound).
  rewrite hjlast nth_last.
  smt().
qed.

lemma hb_history_append seed base l k cube three scale bound initial1 initial2 history
    current1 current2 (draw : hb_draw) (result : BArray8192.t * BArray8192.t * W64.t) :
  hb_shape l k =>
  hb_history seed base l k cube three scale bound initial1 initial2 history
    current1 current2 W64.zero =>
  hb_batch_complete seed (hb_nonce base ((l + k) * size history)) (l + k) draw =>
  result = hb_scale_check_result current1 current2 draw.`1 draw.`2
    (hb_draw_scale draw cube three scale) (256 * l) (256 * (l + k)) bound =>
  hb_history seed base l k cube three scale bound initial1 initial2 (rcons history draw)
    result.`1 result.`2 result.`3.
proof.
  move=> hshape hh hdraw hresult.
  have [hf1 hf2] := hb_history_frames seed base l k cube three scale bound initial1 initial2
    history current1 current2 W64.zero hshape hh.
  have hbase := hb_scale_rebase initial1 initial2 current1 current2 draw.`1 draw.`2
    (hb_draw_scale draw cube three scale) l k bound hshape hf1 hf2.
  have hcanonical : result = hb_scale_check_result initial1 initial2 draw.`1 draw.`2
      (hb_draw_scale draw cube three scale) (256 * l) (256 * (l + k)) bound by smt().
  have [hcomplete [_ _]] := hh.
  have hrejected := hb_history_rejected seed base l k cube three scale bound initial1 initial2
    history current1 current2 hh.
  rewrite /hb_history size_rcons last_rcons.
  have hne : rcons history draw <> [] by smt(size_rcons size_ge0).
  rewrite hne /=.
  split.
  + move=> j hj.
    case (j < size history) => hprev.
    + rewrite nth_rcons hprev /=; apply hcomplete; smt().
    have -> : j = size history by smt().
    rewrite nth_rcons; smt().
  split.
  + move=> j hj.
    have hprev : j < size history by smt().
    rewrite nth_rcons hprev /=; apply hrejected; smt().
  rewrite hcanonical /hb_scale_check_result /hb_scale_norm /hb_attempt_outputs
    /hb_attempt_accept /=.
  have -> : 256 * (l + k) - 256 * l = 256 * k by ring.
  trivial.
qed.

lemma hb_history_finish seed base l k cube three scale bound initial1 initial2 history
    current1 current2 accepted byte_result counter_result :
  hb_history seed base l k cube three scale bound initial1 initial2 history
    current1 current2 accepted =>
  accepted <> W64.zero =>
  BArray1.get8 byte_result 0 = hb_stream seed (hb_nonce base ((l + k) * size history)) 0 =>
  BArray8.get64 counter_result 0 = hb_nonce base ((l + k) * size history) =>
  hb_result seed base l k cube three scale bound initial1 initial2 current1 current2
    byte_result counter_result.
proof.
  move=> hh haccept hbyte hcounter.
  have [hc [hr hlast]] := hh.
  have hnonempty : history <> [] by smt().
  have hbit := hb_boolean_word_zero
    (hb_attempt_accept initial1 initial2 (last witness history) l k cube three scale bound).
  have hone := hb_boolean_word_one
    (hb_attempt_accept initial1 initial2 (last witness history) l k cube three scale bound).
  have haccept1 : accepted = W64.one by smt().
  rewrite /hb_result; exists history.
  have hsize : 0 < size history by smt(size_ge0 size_eq0).
  smt().
qed.
