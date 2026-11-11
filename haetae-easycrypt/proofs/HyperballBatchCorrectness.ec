require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import HyperballSpec HyperballGaussianBounds GaussianStreamCorrectness
  GaussianStreamSpec GaussianStreamBuffer GaussianStreamAccumulator
  GaussianTraceSpec GaussianTraceProperties GaussianWindowSpec.

lemma hb_batch_fold_first seed base blocks : forall (state : int * int),
  (foldl (hb_batch_acc seed base) state blocks).`1 = state.`1 + size blocks.
proof.
  elim: blocks => [|block blocks ih] state //=.
  rewrite ih /hb_batch_acc /=; smt().
qed.

lemma hb_batch_fold_index seed base blocks :
  (hb_batch_fold seed base blocks).`1 = size blocks.
proof. by rewrite /hb_batch_fold hb_batch_fold_first /=. qed.

lemma hb_batch_sum_nil seed base : hb_batch_sum seed base [] = 0.
proof. by rewrite /hb_batch_sum /hb_batch_fold /=. qed.

lemma hb_batch_sum_append seed base blocks block :
  hb_batch_sum seed base (blocks ++ [block]) = hb_batch_sum seed base blocks +
    gauss_event_value_sum (hb_poly_events seed base (size blocks) block).
proof.
  by rewrite /hb_batch_sum /hb_batch_fold foldl_cat /= /hb_batch_acc /=
    -/(hb_batch_fold seed base blocks) hb_batch_fold_index.
qed.

lemma hb_request_shape i : hb_request i = 256 \/ hb_request i = 257.
proof. rewrite /hb_request; smt(). qed.

lemma hb_draw_count_zero : hb_draw_count 0 = 0.
proof. by rewrite /hb_draw_count. qed.

lemma hb_draw_count_step i : 0 <= i =>
  hb_draw_count (i + 1) = hb_draw_count i + hb_request i.
proof. rewrite /hb_draw_count /hb_request; smt(). qed.

lemma hb_draw_count_bounds i : 0 <= i <= 11 => 0 <= hb_draw_count i <= 2818.
proof. rewrite /hb_draw_count; smt(). qed.

lemma hb_next_budget i : 0 <= i < 11 => hb_draw_count i + hb_request i <= 2818.
proof.
  move=> hi; rewrite -(hb_draw_count_step i _) 1:/#.
  have := hb_draw_count_bounds (i + 1) _; smt().
qed.

lemma hb_batch_call_offsets i : 0 <= i < 11 =>
  0 <= 256 * i /\ 256 * i + hb_request i <= 4096 /\
  0 <= 32 * i /\ 32 * i + 32 <= 512.
proof. rewrite /hb_request; smt(). qed.

lemma hb_nonce_step base i : hb_nonce base (i + 1) = hb_nonce base i + W64.one.
proof. rewrite /hb_nonce W64.of_intD; ring. qed.

lemma hb_batch_progress_initial seed base samples signs squares :
  BArray16.get64 squares 0 = W64.zero => BArray16.get64 squares 1 = W64.zero =>
  hb_batch_progress seed base [] samples signs squares.
proof.
  move=> h0 h1.
  have hc := hb_cumulative_zero squares h0 h1.
  have hv : gauss_stream_value squares = 0 by
    move: hc; rewrite /hb_cumulative_square_bound; smt().
  rewrite /hb_batch_progress /= hb_draw_count_zero hb_batch_sum_nil; smt().
qed.

lemma hb_old_samples_preserved (before after : BArray32768.t) i h j n :
  0 <= i <= 11 => 0 <= h < i => 0 <= j < 256 =>
  gauss_big_output_frame before after (256 * i) n =>
  BArray32768.get64 after (256 * h + j) = BArray32768.get64 before (256 * h + j).
proof. rewrite /gauss_big_output_frame; smt(). qed.

lemma hb_old_signs_preserved stream (before after : BArray512.t) i h j :
  0 <= i <= 11 => 0 <= h < i => 0 <= j < 32 =>
  gs_signs_result stream before after (32 * i) =>
  BArray512.get8 after (32 * h + j) = BArray512.get8 before (32 * h + j).
proof. rewrite /gs_signs_result; smt(). qed.

lemma hb_new_signs stream (before after : BArray512.t) i j :
  0 <= i < 11 => 0 <= j < 32 => gs_signs_result stream before after (32 * i) =>
  BArray512.get8 after (32 * i + j) = stream j.
proof. rewrite /gs_signs_result; smt(). qed.

lemma hb_batch_progress_append seed base blocks samples signs squares
    samples' signs' squares' block :
  hb_batch_progress seed base blocks samples signs squares =>
  0 <= size blocks < 11 => 49 <= block =>
  gs_signs_result (hb_stream seed (hb_nonce base (size blocks)))
    signs signs' (32 * size blocks) =>
  gs_progress (fun j => hb_stream seed (hb_nonce base (size blocks)) (32 + j))
    samples samples' squares squares' (hb_request (size blocks)) (256 * size blocks)
    (gs_stream_attempts block) (hb_request (size blocks)) =>
  hb_batch_progress seed base (blocks ++ [block]) samples' signs' squares'.
proof.
  move=> hold hi hblock hsign hnext.
  have [hlen [hprevious [hbudget hsumold]]] := hold.
  have hnextbudget := hb_next_budget (size blocks) hi.
  have hcum := hb_gs_progress_bound
    (fun j => hb_stream seed (hb_nonce base (size blocks)) (32 + j))
    samples samples' squares squares' (hb_request (size blocks)) (256 * size blocks)
    (gs_stream_attempts block) (hb_request (size blocks)) (hb_draw_count (size blocks))
    hbudget hnextbudget hnext.
  have [hn [ha [hc [hcount [hvalues [hframe [hdummy [hacc hsumnew]]]]]]]] := hnext.
  rewrite -/(hb_poly_events seed base (size blocks) block) in hcount.
  rewrite -/(hb_poly_events seed base (size blocks) block) in hvalues.
  rewrite -/(hb_poly_events seed base (size blocks) block) in hsumnew.
  have hstep := hb_draw_count_step (size blocks) _; first smt().
  have hcum' : hb_cumulative_square_bound (hb_draw_count (size blocks + 1)) squares'.
  + by rewrite hstep.
  rewrite /hb_batch_progress size_cat /=.
  split; first smt().
  split.
  + move=> h hh; rewrite !nth_cat.
    case (h < size blocks) => hbefore /=.
    - have hh' : 0 <= h < size blocks by smt().
      have [holdblock [holdcount [holdvalues holdsigns]]] := hprevious h hh'.
      split; first exact holdblock.
      split; first exact holdcount.
      split.
      + move=> j hj.
        rewrite (hb_old_samples_preserved samples samples' (size blocks) h j
          (hb_request (size blocks)) _ hh' hj hframe) 1:/#.
        exact (holdvalues j hj).
      move=> j hj.
      rewrite (hb_old_signs_preserved (hb_stream seed (hb_nonce base (size blocks)))
        signs signs' (size blocks) h j _ hh' hj hsign) 1:/#.
      exact (holdsigns j hj).
    have heq : h = size blocks by smt().
    rewrite heq subzz /=.
    split; first exact hblock.
    split; first smt().
    split.
    + have hmin : min (hb_request (size blocks)) 256 = 256 by smt(hb_request_shape).
      by move: hvalues; rewrite hmin.
    move=> j hj.
    exact (hb_new_signs (hb_stream seed (hb_nonce base (size blocks)))
      signs signs' (size blocks) j hi hj hsign).
  split; first exact hcum'.
  by rewrite hb_batch_sum_append hsumnew hsumold.
qed.

lemma hb_batch_call_correct (seed : BArray64.t) (base : W64.t) (blocks : int list)
    (samples : BArray32768.t) (signs : BArray512.t) (squares : BArray16.t) :
  hoare [GaussianStreamCorrectness.StreamSigner._sf_sample_gauss_N_full_at :
    seedp = seed /\ nonce = hb_nonce base (size blocks) /\
    len = W64.of_int (hb_request (size blocks)) /\
    W64.to_uint sampleoff = 256 * size blocks /\
    W64.to_uint signoff = 32 * size blocks /\
    rp = samples /\ signsp = signs /\ sqsump = squares /\
    hb_batch_progress seed base blocks samples signs squares /\ 0 <= size blocks < 11
    ==>
    exists block, 49 <= block /\
      hb_batch_progress seed base (blocks ++ [block]) res.`1 res.`2 res.`3].
proof.
  conseq (hb_sample_gauss_N_full_at_correct (hb_draw_count (size blocks)) seed
    (hb_nonce base (size blocks)) (hb_request (size blocks)) (256 * size blocks)
    (32 * size blocks) samples signs squares) => //.
  + move=> &m hpre.
    have hp : hb_batch_progress seed base blocks samples signs squares by smt().
    have hi : 0 <= size blocks < 11 by smt().
    have hshape := hb_request_shape (size blocks).
    have hoffsets := hb_batch_call_offsets (size blocks) hi.
    have hnext := hb_next_budget (size blocks) hi.
    move: hp; rewrite /hb_batch_progress; smt().
  move=> &m hpre result [hresult hbound].
  have hp : hb_batch_progress seed base blocks samples signs squares by smt().
  have hi : 0 <= size blocks < 11 by smt().
  move: hresult; rewrite -/(hb_stream seed (hb_nonce base (size blocks))).
  move=> [hsign [block [hblock hnext]]].
  exists block; split; first exact hblock.
  exact (hb_batch_progress_append seed base blocks samples signs squares
    result.`1 result.`2 result.`3 block hp hi hblock hsign hnext).
qed.
