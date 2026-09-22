require import AllCore IntDiv List Distr DList StdOrder.
from Jasmin require import JModel_x86.
require import HyperballIidPayloadSpec HyperballReferenceConstants
  GaussianIidBufferSpec GaussianIidDistribution GaussianPayloadSpec
  GaussianPayloadBufferSpec GaussianPayloadBufferPath GaussianStreamAccumulator
  GaussianAccumulatorCorrectness GaussianWindowSpec HyperballGaussianBounds
  GaussianPayloadDraw GaussianPayloadEncoding GaussianPayloadTrace GaussianPayloadBufferTrace.

lemma hip_mode_polys mode : hip_mode mode => 2 <= hip_polys mode <= 11.
proof.
  rewrite /hip_mode; move=> [-> | [-> | ->]];
    by rewrite /hip_polys /hb_ref_l /hb_ref_k.
qed.

lemma hip_requests_range index : 256 <= hip_requests index <= 257.
proof. by rewrite /hip_requests; case (index<2). qed.

lemma hip_prefix0 : hip_prefix_count 0=0.
proof. by rewrite /hip_prefix_count. qed.

lemma hip_prefix_step index : 0 <= index =>
  hip_prefix_count (index+1)=hip_prefix_count index+hip_requests index.
proof. rewrite /hip_prefix_count /hip_requests /min; smt(). qed.

lemma hip_prefix_bounds index : 0 <= index <= 11 => 0 <= hip_prefix_count index <= 2818.
proof. rewrite /hip_prefix_count /min; smt(). qed.

lemma hip_prefix_total mode : hip_mode mode => hip_prefix_count (hip_polys mode)=hip_total mode.
proof.
  move=> hm; have hp := hip_mode_polys mode hm.
  rewrite /hip_prefix_count /hip_total /hip_count /min; smt().
qed.

lemma hip_call_bounds mode index : hip_mode mode => 0 <= index < hip_polys mode =>
  gib_bounds (hip_requests index) (256*index) (32*index).
proof.
  move=> hm hi; have hp := hip_mode_polys mode hm.
  rewrite /gib_bounds /hip_requests; case (index<2); smt().
qed.

lemma hip_payload_index_block index j : 0 <= index => 0 <= j < 256 =>
  hip_payload_index (256*index+j)=hip_prefix_count index+j.
proof. rewrite /hip_payload_index /hip_prefix_count /min; smt(). qed.

lemma hip_payload_index_prefix index k : 0 <= index => 0 <= k < 256*index =>
  0 <= hip_payload_index k < hip_prefix_count index.
proof. rewrite /hip_payload_index /hip_prefix_count /min; smt(). qed.

lemma hip_payload_index_dummy k : 0 <= k =>
  hip_payload_index k<>256 /\ hip_payload_index k<>513.
proof. rewrite /hip_payload_index; smt(). qed.

lemma hip_visible_size history : 514 <= size history =>
  size (hip_visible_payload history)=size history-2.
proof.
  move=> hs; rewrite /hip_visible_payload !size_cat !size_take 1..2://
    !size_drop 1..2:// /max; smt().
qed.

lemma hip_visible_nth history k : 514 <= size history => 0 <= k < size history-2 =>
  nth 0 (hip_visible_payload history) k=nth 0 history (hip_payload_index k).
proof.
  move=> hs hk.
  have hfirst : size (take 256 history)=256 by apply size_takel; smt().
  have hsecond : size (take 256 (drop 257 history))=256.
  + apply size_takel; rewrite size_drop 1:// /max; smt().
  rewrite /hip_visible_payload !nth_cat !size_cat hfirst hsecond /hip_payload_index.
  case (k<256) => h1 /=.
  + by rewrite ifT 1:/# nth_take 1:// 1:h1.
  case (k<512) => h2 /=.
  + have hk256 : k-256<256 by smt().
    have hk2560 : 0<=k-256 by smt().
    rewrite nth_take 1:// 1:hk256 nth_drop 1:// 1:hk2560.
    congr; ring.
  have hk512 : 0<=k-512 by smt().
  rewrite nth_drop 1:// 1:hk512.
  congr; ring.
qed.

lemma hip_squares0_word i : 0 <= i < 2 => BArray16.get64 hip_squares0 i=W64.zero.
proof.
  move=> hi; apply W8u8.wordP => j hj.
  rewrite BArray16.get64d_byte 1:hj /hip_squares0 BArray16.initiE 1:/# /=.
  rewrite W8u8.bits8E; apply W8.wordP => k hk.
  by rewrite W8.zerowE W8.initE hk /=.
qed.

lemma hip_squares0_cumulative : hb_cumulative_square_bound 0 hip_squares0.
proof. apply hb_cumulative_zero; apply hip_squares0_word; trivial. qed.

op [opaque] hip_state (index : int) (state : gib_result) (history : int list) : bool =
  size history=hip_prefix_count index /\
  hb_cumulative_square_bound (hip_prefix_count index) state.`3 /\
  gauss_stream_value state.`3=gpd_sum history /\
  (forall k, 0 <= k < 256*index =>
    W64.to_uint (BArray32768.get64 state.`1 k)=
      gpd_magnitude (nth 0 history (hip_payload_index k))).

lemma hip_state_initial : hip_state 0 hip_initial [].
proof.
  have hc := hip_squares0_cumulative.
  have hz : gauss_stream_value hip_squares0=0 by
    move: hc; rewrite /hb_cumulative_square_bound; smt().
  rewrite /hip_state hip_prefix0 /hip_initial /= hz /gpd_sum /=; smt().
qed.

lemma hip_gpt_coefficient previous initial_values initial_squares n offset history values squares j :
  gpt_state previous initial_values initial_squares n offset history values squares =>
  size history=n => 256 <= n => 0 <= j < 256 =>
  W64.to_uint (BArray32768.get64 values (offset+j))=gpd_magnitude (nth 0 history j).
proof.
  rewrite /gpt_state; move=> [_ [hvisible _]] hsize hn hj.
  have hm : min (size history) 256=256 by rewrite hsize /min; smt().
  have ht : size (take 256 history)=256 by apply size_takel; smt().
  have he := congr1 (fun (xs : int list) => nth 0 xs j) _ _ hvisible.
  move: he; rewrite /gib_visible hm /= (nth_map 0) 1:size_iota 1:/#
    nth_iota 1:hj /= (nth_map 0) 1:ht 1:hj nth_take 1:// 1:/#.
  trivial.
qed.

lemma hip_state_step index (state : gib_result) (history : int list)
    (following : gib_result) (payload : int list) :
  0 <= index < 11 => hip_state index state history =>
  size payload=hip_requests index =>
  gpt_state (hip_prefix_count index) state.`1 state.`3 (hip_requests index) (256*index)
    payload following.`1 following.`3 =>
  hip_state (index+1) following (history++payload).
proof.
  move=> hi hs hn hg.
  have hs0 := hs; rewrite /hip_state in hs0.
  have [hsize [hcumulative [hsum hcoeff]]] := hs0.
  have hg0 := hg; rewrite /gpt_state in hg0.
  have [_ [hvisible [hframe [hnextsum hvalue]]]] := hg0.
  rewrite /gauss_big_output_frame in hframe.
  have hi0 : 0<=index by smt().
  have hsize' : size (history++payload)=hip_prefix_count (index+1)
    by rewrite size_cat hsize hn (hip_prefix_step index hi0).
  have hcum : hb_cumulative_square_bound (hip_prefix_count (index+1)) following.`3.
  + move: hnextsum; rewrite hn (hip_prefix_step index hi0).
    trivial.
  have hsum' : gauss_stream_value following.`3=gpd_sum (history++payload)
    by rewrite gpt_sum_cat; smt().
  rewrite /hip_state; split; first exact hsize'.
  split; first exact hcum.
  split; first exact hsum'.
  move=> k hk; case (k<256*index) => hold.
  + have hkr : 0<=k<4096 by smt().
    have hko : !(256*index<=k<256*index+256) by smt().
    have hframek := hframe k hkr hko.
    have hkp : 0<=k<256*index by smt().
    have hind := hip_payload_index_prefix index k hi0 hkp.
    rewrite hframek (hcoeff k hkp) nth_cat hsize ifT 1:/#; trivial.
  have hj : 0<=k-256*index<256 by smt().
  have [hn256 _] := hip_requests_range index.
  have hv := hip_gpt_coefficient (hip_prefix_count index) state.`1 state.`3
    (hip_requests index) (256*index) payload following.`1 following.`3 (k-256*index)
    hg hn hn256 hj.
  have he : 256*index+(k-256*index)=k by ring.
  move: hv; rewrite he => hv.
  have hindex := hip_payload_index_block index (k-256*index) hi0 hj.
  rewrite he in hindex.
  rewrite hindex nth_cat hsize ifF 1:/#.
  have hdiff : hip_prefix_count index+(k-256*index)-hip_prefix_count index=k-256*index by ring.
  by rewrite hdiff hv.
qed.

lemma hip_actual_payload :
  equiv [HyperballIidGaussian.sample ~ HyperballIidPayload.sample :
    ={mode} /\ hip_mode mode{1} ==> res{1}=res{2}.`1].
proof.
  proc.
  while (={mode,index,state} /\ hip_mode mode{1} /\ 0 <= index{1} <= hip_polys mode{1}).
  + wp; call gpb_actual_projection; auto => />; smt(hip_call_bounds).
  auto => />; smt(hip_mode_polys).
qed.

module HIPPayloadTail = {
  proc sample(n : int) : int list = {
    var history, chunk : int list;
    var index : int;
    history <- [];
    index <- 0;
    while (index<n) {
      chunk <@ GaussianPayloadDraw.sample(256);
      history <- history++chunk;
      index <- index+1;
    }
    return history;
  }
}.

clone DList.Program as HIPPayloadChunks with
  type t <- int list,
  op d <- dlist gpd_accepted 256.

lemma hip_tail_chunks :
  equiv [HIPPayloadTail.sample ~ HIPPayloadChunks.LoopSnoc.sample :
    ={n} ==> res{1}=flatten res{2}].
proof.
  proc; inline GaussianPayloadDraw.sample.
  while (={n} /\ index{1}=i{2} /\ history{1}=flatten l{2}).
  + wp; rnd; wp; skip; auto => />.
    move=> &2 hindex chunk hc.
    by rewrite flatten_cat flatten_cons flatten_nil cats0.
  by auto.
qed.

lemma hip_tail_law n0 (event : int list -> bool) &m : 0 <= n0 =>
  Pr[HIPPayloadTail.sample(n0) @ &m : event res]=mu (dlist gpd_accepted (256*n0)) event.
proof.
  move=> hn.
  have he : Pr[HIPPayloadTail.sample(n0) @ &m : event res]=
    Pr[HIPPayloadChunks.LoopSnoc.sample(n0) @ &m : event (flatten res)] by
    byequiv hip_tail_chunks.
  have hs : Pr[HIPPayloadChunks.Sample.sample(n0) @ &m : event (flatten res)]=
    Pr[HIPPayloadChunks.LoopSnoc.sample(n0) @ &m : event (flatten res)] by
    byequiv HIPPayloadChunks.Sample_LoopSnoc_eq.
  rewrite he -hs.
  have hd : mu (dlist (dlist gpd_accepted 256) n0) (fun chunks => event (flatten chunks))=
      mu (dlist gpd_accepted (256*n0)) event.
  + rewrite -(dmapE _ flatten event) dlist_dlist 1:// 1:hn; congr; ring.
  rewrite -hd.
  by byphoare (_ : n=n0 ==> event (flatten res)) => //; proc; rnd; skip; auto.
qed.

lemma hip_tail_draw :
  equiv [HIPPayloadTail.sample ~ GaussianPayloadDraw.sample :
    0 <= n{1} /\ n{2}=256*n{1} ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 history [hn he].
  by rewrite (hip_tail_law n{1} (pred1 history) &1 hn)
    (gpd_draw_law n{2} (pred1 history) &2) he.
qed.

module HIPPayloadConcat = {
  proc sample(a b : int) : int list = {
    var first, second : int list;
    first <@ GaussianPayloadDraw.sample(a);
    second <@ GaussianPayloadDraw.sample(b);
    return first++second;
  }
}.

lemma hip_concat_law a0 b0 (event : int list -> bool) &m : 0 <= a0 => 0 <= b0 =>
  Pr[HIPPayloadConcat.sample(a0,b0) @ &m : event res]=
    mu (dlist gpd_accepted (a0+b0)) event.
proof.
  move=> ha hb; byphoare (_ : a=a0 /\ b=b0 ==> event res) => //.
  proc; inline GaussianPayloadDraw.sample; wp; rndsem* 0.
  rnd (fun (parts : int list*int list) => event (parts.`1++parts.`2)).
  skip; auto => />.
  rewrite -dprod_dlet -(dmapE _ (fun (parts : int list*int list) => parts.`1++parts.`2) event).
  by rewrite -(dlist_add gpd_accepted a0 b0 ha hb).
qed.

lemma hip_concat_draw :
  equiv [HIPPayloadConcat.sample ~ GaussianPayloadDraw.sample :
    0 <= a{1} /\ 0 <= b{1} /\ n{2}=a{1}+b{1} ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 history [ha [hb hn]].
  by rewrite (hip_concat_law a{1} b{1} (pred1 history) &1 ha hb)
    (gpd_draw_law n{2} (pred1 history) &2) hn.
qed.

module HIPPayloadSeparated = {
  proc sample(mode : int) : int list = {
    var first, second, tail : int list;
    first <@ GaussianPayloadDraw.sample(257);
    second <@ GaussianPayloadDraw.sample(257);
    tail <@ HIPPayloadTail.sample(hip_polys mode-2);
    return first++second++tail;
  }
}.

lemma hip_payload_separated :
  equiv [HyperballIidPayload.sample ~ HIPPayloadSeparated.sample :
    ={mode} /\ hip_mode mode{1} ==> res{1}.`2=res{2}].
proof.
  proc.
  rcondt{1} 4.
  + auto => />; smt(hip_mode_polys).
  seq 4 1 : (={mode} /\ hip_mode mode{1} /\ index{1}=0 /\
    history{1}=[] /\ step{1}.`2=first{2}).
  + call gpd_buffer_draw; auto => />; by rewrite /hip_requests.
  rcondt{1} 4.
  + auto => />; smt(hip_mode_polys).
  seq 4 1 : (={mode} /\ hip_mode mode{1} /\ index{1}=1 /\
    history{1}=first{2} /\ step{1}.`2=second{2}).
  + call gpd_buffer_draw; auto => />; by rewrite /hip_requests.
  inline HIPPayloadTail.sample; wp.
  while (={mode} /\ hip_mode mode{1} /\ n{2}=hip_polys mode{1}-2 /\
    index{1}=index{2}+2 /\ 0<=index{2} /\
    history{1}=first{2}++second{2}++history{2}).
  + wp; call gpd_buffer_draw; auto => />.
    rewrite /hip_requests; smt(catA).
  auto => />; smt().
qed.

module HIPPayloadCombined = {
  proc sample(mode : int) : int list = {
    var prefix, tail : int list;
    prefix <@ HIPPayloadConcat.sample(257,257);
    tail <@ GaussianPayloadDraw.sample(256*(hip_polys mode-2));
    return prefix++tail;
  }
}.

lemma hip_separated_combined :
  equiv [HIPPayloadSeparated.sample ~ HIPPayloadCombined.sample :
    ={mode} /\ hip_mode mode{1} ==> ={res}].
proof.
  proc; inline{2} HIPPayloadConcat.sample.
  wp; call hip_tail_draw.
  inline GaussianPayloadDraw.sample.
  wp; rnd; wp; rnd; wp; skip; auto => />; smt(hip_mode_polys).
qed.

lemma hip_combined_concat :
  equiv [HIPPayloadCombined.sample ~ HIPPayloadConcat.sample :
    hip_mode mode{1} /\ a{2}=514 /\ b{2}=256*(hip_polys mode{1}-2) ==> ={res}].
proof.
  proc; wp.
  call (_ : ={n} ==> ={res}); first by proc; rnd; skip; auto.
  call hip_concat_draw; auto => />.
qed.

lemma hip_separated_law mode (event : int list -> bool) &m : hip_mode mode =>
  Pr[HIPPayloadSeparated.sample(mode) @ &m : event res]=
    mu (dlist gpd_accepted (hip_total mode)) event.
proof.
  move=> hm; have hp := hip_mode_polys mode hm.
  have he : Pr[HIPPayloadSeparated.sample(mode) @ &m : event res]=
    Pr[HIPPayloadCombined.sample(mode) @ &m : event res] by
    byequiv hip_separated_combined.
  have hj : Pr[HIPPayloadCombined.sample(mode) @ &m : event res]=
    Pr[HIPPayloadConcat.sample(514,256*(hip_polys mode-2)) @ &m : event res] by
    byequiv hip_combined_concat.
  have hn : 0 <= 256*(hip_polys mode-2) by smt().
  have h0 : 0 <= 514 by trivial.
  rewrite he hj (hip_concat_law 514 (256*(hip_polys mode-2)) event &m h0 hn).
  have hd : 514+256*(hip_polys mode-2)=hip_total mode by
    rewrite /hip_total /hip_count; ring.
  by rewrite hd.
qed.

lemma hip_batch_history_law mode (event : int list -> bool) &m : hip_mode mode =>
  Pr[HyperballIidPayload.sample(mode) @ &m : event res.`2]=
    mu (dlist gpd_accepted (hip_total mode)) event.
proof.
  move=> hm.
  have he : Pr[HyperballIidPayload.sample(mode) @ &m : event res.`2]=
    Pr[HIPPayloadSeparated.sample(mode) @ &m : event res] by
    byequiv hip_payload_separated.
  by rewrite he (hip_separated_law mode event &m hm).
qed.

lemma hip_payload_terminates mode &m : hip_mode mode =>
  Pr[HyperballIidPayload.sample(mode) @ &m : true]=1%r.
proof.
  move=> hm; have he := hip_batch_history_law mode (fun _ => true) &m hm.
  rewrite /= in he; rewrite he.
  exact (dlist_ll gpd_accepted (hip_total mode) gpd_accepted_ll).
qed.

lemma hip_payload_lossless :
  phoare [HyperballIidPayload.sample : hip_mode mode ==> true] = 1%r.
proof. bypr => &m hm; exact (hip_payload_terminates mode{m} &m hm). qed.

lemma hip_actual_terminates mode &m : hip_mode mode =>
  Pr[HyperballIidGaussian.sample(mode) @ &m : true]=1%r.
proof.
  move=> hm; have he : Pr[HyperballIidGaussian.sample(mode) @ &m : true]=
    Pr[HyperballIidPayload.sample(mode) @ &m : true] by byequiv hip_actual_payload.
  by rewrite he (hip_payload_terminates mode &m hm).
qed.

lemma hip_payload_call_total mode0 index0 history0 :
  phoare [GaussianPayloadBuffer.sample :
    hip_mode mode0 /\ 0 <= index0 < hip_polys mode0 /\
    n=hip_requests index0 /\ sample_offset=256*index0 /\ sign_offset=32*index0 /\
    hip_state index0 (rp,signsp,sqsump) history0 ==>
    hip_state (index0+1) res.`1 (history0++res.`2)] = 1%r.
proof.
  bypr => &m [hm [hi [hn [ho [hsign hstate]]]]].
  have hpolys := hip_mode_polys mode0 hm.
  have hi11 : 0<=index0<11 by smt().
  have hib : 0<=index0+1<=11 by smt().
  have hi0 : 0<=index0 by smt().
  have [hprefix0 hprefixmax] := hip_prefix_bounds (index0+1) hib.
  have hb := hip_call_bounds mode0 index0 hm hi.
  have hc : hb_cumulative_square_bound (hip_prefix_count index0) sqsump{m} by
    move: hstate; rewrite /hip_state /=; smt().
  have hbudget : hip_prefix_count index0+hip_requests index0<=2818 by
    rewrite -(hip_prefix_step index0 hi0); exact hprefixmax.
  have ht := gpt_buffer_total (hip_prefix_count index0) rp{m} signsp{m} sqsump{m}
    (hip_requests index0) (256*index0) (32*index0) hb hc hbudget.
  have hstep : forall (out : gpb_result),
      size out.`2=hip_requests index0 /\
      gpt_state (hip_prefix_count index0) rp{m} sqsump{m} (hip_requests index0)
        (256*index0) out.`2 out.`1.`1 out.`1.`3 =>
      hip_state (index0+1) out.`1 (history0++out.`2).
  + move=> out [hsize hg].
    exact (hip_state_step index0 (rp{m},signsp{m},sqsump{m}) history0 out.`1 out.`2
      hi11 hstate hsize hg).
  rewrite hn ho hsign.
  byphoare (_ : rp=rp{m} /\ signsp=signsp{m} /\ sqsump=sqsump{m} /\
    n=hip_requests index0 /\ sample_offset=256*index0 /\ sign_offset=32*index0 ==>
    hip_state (index0+1) res.`1 (history0++res.`2)) => //.
  have hge : phoare [GaussianPayloadBuffer.sample :
    rp=rp{m} /\ signsp=signsp{m} /\ sqsump=sqsump{m} /\
    n=hip_requests index0 /\ sample_offset=256*index0 /\ sign_offset=32*index0 ==>
    size res.`2=hip_requests index0 /\
    gpt_state (hip_prefix_count index0) rp{m} sqsump{m} (hip_requests index0)
      (256*index0) res.`2 res.`1.`1 res.`1.`3] >= 1%r by conseq ht.
  conseq (_ : _ ==> _ : >= 1%r) => //.
  conseq hge => //.
qed.

lemma hip_payload_call_correct mode0 index0 history0 :
  hoare [GaussianPayloadBuffer.sample :
    hip_mode mode0 /\ 0 <= index0 < hip_polys mode0 /\
    n=hip_requests index0 /\ sample_offset=256*index0 /\ sign_offset=32*index0 /\
    hip_state index0 (rp,signsp,sqsump) history0 ==>
    hip_state (index0+1) res.`1 (history0++res.`2)].
proof. by conseq (hip_payload_call_total mode0 index0 history0). qed.

lemma hip_payload_state_correct mode0 : hip_mode mode0 =>
  hoare [HyperballIidPayload.sample : mode=mode0 ==>
    hip_state (hip_polys mode0) res.`1 res.`2].
proof.
  move=> hm; have hp := hip_mode_polys mode0 hm.
  proc.
  while (mode=mode0 /\ 0<=index<=hip_polys mode0 /\ hip_state index state history).
  + wp; ecall (hip_payload_call_correct mode0 index history).
    auto => />; smt().
  auto => />; smt(hip_state_initial).
qed.

lemma hip_state_observe mode (state : gib_result) history : hip_mode mode =>
  hip_state (hip_polys mode) state history =>
  hip_observe mode state=hip_projection history /\
  hb_cumulative_square_bound (hip_total mode) state.`3.
proof.
  move=> hm hs.
  have hp := hip_mode_polys mode hm.
  have hs0 := hs; rewrite /hip_state in hs0.
  have [hsize [hcumulative [hsum hcoeff]]] := hs0.
  rewrite (hip_prefix_total mode hm) in hsize.
  rewrite (hip_prefix_total mode hm) in hcumulative.
  have hcount : 0<=hip_count mode by rewrite /hip_count; smt().
  have hfull : 514<=size history by rewrite hsize /hip_total /hip_count; smt().
  have hvisible : size (hip_visible_payload history)=hip_count mode by
    rewrite (hip_visible_size history hfull) hsize /hip_total; ring.
  have he : map (fun i => W64.to_uint (BArray32768.get64 state.`1 i))
      (iota_ 0 (hip_count mode)) = map gpd_magnitude (hip_visible_payload history).
  + apply (List.eq_from_nth 0).
    + rewrite !size_map size_iota hvisible; smt().
    move=> k hk.
    have hk0 : 0<=k<hip_count mode by move: hk; rewrite size_map size_iota; smt().
    rewrite (nth_map 0) 1:size_iota 1:/# nth_iota 1:hk0 /=
      (nth_map 0) 1:hvisible 1:hk0 (hip_visible_nth history k hfull _) 1:/#.
    apply hcoeff; by move: hk0; rewrite /hip_count.
  by rewrite /hip_observe /hip_projection he hsum.
qed.

lemma hip_payload_observe mode0 : hip_mode mode0 =>
  hoare [HyperballIidPayload.sample : mode=mode0 ==>
    hip_observe mode0 res.`1=hip_projection res.`2 /\
    hb_cumulative_square_bound (hip_total mode0) res.`1.`3].
proof.
  move=> hm.
  conseq (hip_payload_state_correct mode0 hm) => //.
  smt(hip_state_observe).
qed.

lemma hip_payload_observe_total mode0 : hip_mode mode0 =>
  phoare [HyperballIidPayload.sample : mode=mode0 ==>
    hip_observe mode0 res.`1=hip_projection res.`2 /\
    hb_cumulative_square_bound (hip_total mode0) res.`1.`3] = 1%r.
proof.
  move=> hm.
  have hll : phoare [HyperballIidPayload.sample : mode=mode0 ==> true] = 1%r.
  + bypr => &m ->; exact (hip_payload_terminates mode0 &m hm).
  by conseq hll (hip_payload_observe mode0 hm).
qed.
