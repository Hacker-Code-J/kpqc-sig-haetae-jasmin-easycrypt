require import AllCore IntDiv List Distr DList DProd StdOrder.
from Jasmin require import JModel_x86.
require import GaussianPayloadSpec GaussianPayloadEncoding GaussianUniformBytes
  GaussianIidBufferSpec HyperballIidPayloadSpec HyperballIidPayloadBatch
  HyperballGaussianBounds HyperballRenyiBatch HyperballRenyiBuffer HyperballRenyiSchedule.

op hrj_step (acc : gib_result * int) (block : hrj_block) : gib_result * int =
  (hrb_result acc.`1 (256*acc.`2) (32*acc.`2) block.`1 block.`2,acc.`2+1).

op [opaque] hrj_fold (initial : gib_result) (index : int) (blocks : hrj_block list) : gib_result =
  (foldl hrj_step (initial,index) blocks).`1.

op [opaque] hrj_reconstruct (input : hrj_input) : gib_result =
  hrj_fold hip_initial 0 (hrj_blocks input).

lemma hrj_fold_index blocks (initial : gib_result) index :
  (foldl hrj_step (initial,index) blocks).`2=index+size blocks.
proof.
  elim: blocks initial index => [|block blocks ih] initial index.
  + by rewrite /=.
  rewrite /= /hrj_step /= ih; smt().
qed.

lemma hrj_fold_snoc initial index blocks block :
  hrj_fold initial index (blocks++[block])=
    hrb_result (hrj_fold initial index blocks)
      (256*(index+size blocks)) (32*(index+size blocks)) block.`1 block.`2.
proof.
  by rewrite /hrj_fold foldl_cat /= /hrj_step /= hrj_fold_index.
qed.

module HyperballRenyiBufferCall = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result * hrj_block = {
    var block : hrj_block;
    block <$ hrj_blockd gpd_accepted n;
    return (hrb_result (rp,signsp,sqsump) sample_offset sign_offset block.`1 block.`2,block);
  }
}.

lemma hrj_draw_call :
  equiv [HyperballRenyiBufferDraw.sample ~ HyperballRenyiBufferCall.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} ==> res{1}=res{2}.`1].
proof.
  proc; rnd : *0 *0; auto => /> &2.
  by rewrite dmap_id /hrj_blockd dprod_dlet.
qed.

lemma hrj_call_block :
  equiv [HyperballRenyiBufferCall.sample ~ HyperballRenyiBlockDraw.sample :
    ={n} ==> res{1}.`2=res{2}].
proof. proc; rnd; auto. qed.

module HyperballRenyiTrace = {
  proc sample(mode : int) : gib_result * hrj_block list = {
    var state : gib_result;
    var step : gib_result * hrj_block;
    var blocks : hrj_block list;
    var index : int;
    state <- hip_initial;
    blocks <- [];
    index <- 0;
    while (index<hip_polys mode) {
      step <@ HyperballRenyiBufferCall.sample(state.`1,state.`2,state.`3,
        hip_requests index,256*index,32*index);
      state <- step.`1;
      blocks <- blocks++[step.`2];
      index <- index+1;
    }
    return (state,blocks);
  }
}.

lemma hrj_trace_fold :
  hoare [HyperballRenyiTrace.sample : true ==>
    res.`1=hrj_fold hip_initial 0 res.`2].
proof.
  proc.
  while (state=hrj_fold hip_initial 0 blocks /\ index=size blocks).
  + inline HyperballRenyiBufferCall.sample; wp; rnd; wp; skip; auto => />.
    move=> &hr _ block _.
    by rewrite hrj_fold_snoc /= size_cat /=.
  by auto => />; rewrite /hrj_fold /=.
qed.

lemma hrj_trace_blocks :
  equiv [HyperballRenyiTrace.sample ~ HyperballRenyiSourceDraw.sample :
    ={mode} /\ hip_mode mode{1} ==> res{1}.`2=hrj_blocks res{2}].
proof.
  proc.
  rcondt{1} 4.
  + auto => />; smt(hip_mode_polys).
  seq 4 1 : (={mode} /\ hip_mode mode{1} /\ index{1}=0 /\
    blocks{1}=[] /\ step{1}.`2=first{2}).
  + call hrj_call_block; auto => />; by rewrite /hip_requests.
  rcondt{1} 4.
  + auto => />; smt(hip_mode_polys).
  seq 4 1 : (={mode} /\ hip_mode mode{1} /\ index{1}=1 /\
    blocks{1}=[first{2}] /\ step{1}.`2=second{2}).
  + call hrj_call_block; auto => />; by rewrite /hip_requests.
  inline HyperballRenyiTail.sample; wp.
  while (={mode} /\ hip_mode mode{1} /\ n{2}=hip_polys mode{1}-2 /\
    index{1}=index{2}+2 /\ 0<=index{2} /\
    blocks{1}=first{2}::second{2}::blocks{2}).
  + wp; call hrj_call_block; auto => />.
    rewrite /hip_requests; smt(catA).
  auto => />; rewrite /hrj_blocks /=; smt().
qed.

lemma hrj_buffer_call previous n0 :
  equiv [GaussianIidBuffer.sample ~ HyperballRenyiBufferCall.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} /\ n{1}=n0 /\
    gib_bounds n{1} sample_offset{1} sign_offset{1} /\
    hb_cumulative_square_bound previous sqsump{1} /\ previous+n0<=2818 ==>
    res{1}=res{2}.`1 /\ hb_cumulative_square_bound (previous+n0) res{1}.`3].
proof.
  transitivity HyperballRenyiBufferDraw.sample
    (={rp,signsp,sqsump,n,sample_offset,sign_offset} /\ n{1}=n0 /\
      gib_bounds n{1} sample_offset{1} sign_offset{1} /\
      hb_cumulative_square_bound previous sqsump{1} /\ previous+n0<=2818 ==>
      ={res} /\ hb_cumulative_square_bound (previous+n0) res{1}.`3)
    (={rp,signsp,sqsump,n,sample_offset,sign_offset} ==> res{1}=res{2}.`1).
  + move=> &1 &2 h; exists (rp{2},signsp{2},sqsump{2},n{2},sample_offset{2},sign_offset{2}); smt().
  + smt().
  + conseq (hrb_actual_draw previous n0) => />; smt().
  exact hrj_draw_call.
qed.

lemma hrj_actual_trace :
  equiv [HyperballIidGaussian.sample ~ HyperballRenyiTrace.sample :
    ={mode} /\ hip_mode mode{1} ==> res{1}=res{2}.`1].
proof.
  proc.
  while (={mode,index,state} /\ hip_mode mode{1} /\
    0<=index{1}<=hip_polys mode{1} /\
    hb_cumulative_square_bound (hip_prefix_count index{1}) state{1}.`3).
  + wp; ecall (hrj_buffer_call (hip_prefix_count index{1}) (hip_requests index{1})).
    auto => /> &2 hm hi0 hit hpref0 hprefmax hlo hvalue0 hvaluehi hactive.
    have hb := hip_call_bounds mode{2} index{2} hm _; first smt().
    rewrite /gib_bounds in hb.
    have hp := hip_mode_polys mode{2} hm.
    have hs := hip_prefix_step index{2} hi0.
    have hbudget := hip_prefix_bounds (index{2}+1) _; first smt().
    smt().
  auto => />; rewrite hip_prefix0 /hip_initial /=.
  smt(hip_mode_polys hip_squares0_cumulative).
qed.

lemma hrj_trace_blocks_phoare mode0 (event : hrj_block list -> bool) : hip_mode mode0 =>
  phoare [HyperballRenyiTrace.sample : mode=mode0 ==> event res.`2] =
    (mu (hrj_source gpd_accepted mode0) (fun input => event (hrj_blocks input))).
proof.
  move=> hm; bypr => &m ->.
  have he : Pr[HyperballRenyiTrace.sample(mode0) @ &m : event res.`2] =
    Pr[HyperballRenyiSourceDraw.sample(mode0) @ &m : event (hrj_blocks res)]
    by byequiv hrj_trace_blocks => //; smt().
  rewrite he; exact (hrj_source_law mode0 (fun input => event (hrj_blocks input)) &m).
qed.

lemma hrj_trace_phoare mode0 (event : gib_result -> bool) : hip_mode mode0 =>
  phoare [HyperballRenyiTrace.sample : mode=mode0 ==> event res.`1] =
    (mu (hrj_source gpd_accepted mode0) (fun input => event (hrj_reconstruct input))).
proof.
  move=> hm; rewrite /hrj_reconstruct.
  conseq (hrj_trace_blocks_phoare mode0 (fun blocks => event (hrj_fold hip_initial 0 blocks)) hm)
    hrj_trace_fold => />; smt().
qed.

op hrj_actual_state mode : gib_result distr =
  dmap (hrj_source gpd_accepted mode) hrj_reconstruct.

lemma hrj_actual_law mode (event : gib_result -> bool) &m : hip_mode mode =>
  Pr[HyperballIidGaussian.sample(mode) @ &m : event res] =
    (mu (hrj_actual_state mode) event).
proof.
  move=> hm; rewrite /hrj_actual_state dmapE /(\o).
  have he : Pr[HyperballIidGaussian.sample(mode) @ &m : event res] =
    Pr[HyperballRenyiTrace.sample(mode) @ &m : event res.`1]
    by byequiv hrj_actual_trace => //; smt().
  rewrite he; by byphoare (hrj_trace_phoare mode event hm).
qed.
