require import AllCore IntDiv List Distr DList DProd StdOrder.
from Jasmin require import JModel_x86.
require import GaussianPayloadSpec GaussianPayloadEncoding GaussianUniformBytes
  GaussianIidBufferSpec HyperballIidPayloadSpec HyperballIidPayloadBatch
  HyperballGaussianBounds HyperballRenyiBatch.

module HyperballRenyiBlockDraw = {
  proc sample(n : int) : hrj_block = {
    var block : hrj_block;
    block <$ hrj_blockd gpd_accepted n;
    return block;
  }
}.

module HyperballRenyiTail = {
  proc sample(n : int) : hrj_block list = {
    var blocks : hrj_block list;
    var block : hrj_block;
    var index : int;
    blocks <- [];
    index <- 0;
    while (index<n) {
      block <@ HyperballRenyiBlockDraw.sample(256);
      blocks <- blocks++[block];
      index <- index+1;
    }
    return blocks;
  }
}.

clone DList.Program as HyperballRenyiChunks with
  type t <- hrj_block,
  op d <- hrj_blockd gpd_accepted 256.

lemma hrj_tail_chunks :
  equiv [HyperballRenyiTail.sample ~ HyperballRenyiChunks.LoopSnoc.sample :
    ={n} ==> ={res}].
proof.
  proc; inline HyperballRenyiBlockDraw.sample.
  while (={n} /\ index{1}=i{2} /\ blocks{1}=l{2}).
  + wp; rnd; auto.
  by auto.
qed.

lemma hrj_tail_law n0 (event : hrj_block list -> bool) &m :
  Pr[HyperballRenyiTail.sample(n0) @ &m : event res]=
    mu (dlist (hrj_blockd gpd_accepted 256) n0) event.
proof.
  have he : Pr[HyperballRenyiTail.sample(n0) @ &m : event res]=
    Pr[HyperballRenyiChunks.LoopSnoc.sample(n0) @ &m : event res]
    by byequiv hrj_tail_chunks.
  have hs : Pr[HyperballRenyiChunks.Sample.sample(n0) @ &m : event res]=
    Pr[HyperballRenyiChunks.LoopSnoc.sample(n0) @ &m : event res]
    by byequiv HyperballRenyiChunks.Sample_LoopSnoc_eq.
  rewrite he -hs.
  byphoare (_ : n=n0 ==> event res) => //.
  proc; rnd; skip; auto.
qed.

module HyperballRenyiSourceDraw = {
  proc sample(mode : int) : hrj_input = {
    var first, second : hrj_block;
    var tail : hrj_block list;
    first <@ HyperballRenyiBlockDraw.sample(257);
    second <@ HyperballRenyiBlockDraw.sample(257);
    tail <@ HyperballRenyiTail.sample(hip_polys mode-2);
    return (first,(second,tail));
  }
}.

module HyperballRenyiSourceSample = {
  proc sample(mode : int) : hrj_input = {
    var input : hrj_input;
    input <$ hrj_source gpd_accepted mode;
    return input;
  }
}.

lemma hrj_tail_draw :
  equiv [HyperballRenyiTail.sample ~ HyperballRenyiChunks.Sample.sample :
    ={n} ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 blocks hn.
  rewrite (hrj_tail_law n{1} (pred1 blocks) &1) hn.
  byphoare (_ : n=n{2} ==> res=blocks) => //.
  proc; rnd; skip; auto.
qed.

module HyperballRenyiSourceDirect = {
  proc sample(mode : int) : hrj_input = {
    var first, second : hrj_block;
    var tail : hrj_block list;
    var output : hrj_input;
    first <@ HyperballRenyiBlockDraw.sample(257);
    second <@ HyperballRenyiBlockDraw.sample(257);
    tail <@ HyperballRenyiChunks.Sample.sample(hip_polys mode-2);
    output <- (first,(second,tail));
    return output;
  }
}.

lemma hrj_source_direct :
  equiv [HyperballRenyiSourceDraw.sample ~ HyperballRenyiSourceDirect.sample :
    ={mode} ==> ={res}].
proof.
  proc; wp; call hrj_tail_draw; inline HyperballRenyiBlockDraw.sample.
  by wp; rnd; wp; rnd; auto.
qed.

lemma hrj_source_sequential (payload : int distr) (mode : int) :
  hrj_source payload mode =
    dlet (hrj_blockd payload 257) (fun (first : hrj_block) =>
      dlet (hrj_blockd payload 257) (fun (second : hrj_block) =>
        dmap (dlist (hrj_blockd payload 256) (hip_polys mode-2))
          (fun tail => (first,(second,tail))))).
proof.
  rewrite /hrj_source dprod_dlet.
  apply eq_dlet => // block1.
  rewrite dprod_dlet dlet_dlet.
  apply eq_dlet => // block2.
  rewrite dlet_dlet /dmap /(\o).
  apply eq_dlet => // rest.
  by rewrite dlet_unit.
qed.

lemma hrj_direct_sample :
  equiv [HyperballRenyiSourceDirect.sample ~ HyperballRenyiSourceSample.sample :
    ={mode} ==> ={res}].
proof.
  proc; inline HyperballRenyiBlockDraw.sample HyperballRenyiChunks.Sample.sample.
  rnd : *0 *0; auto => /> &2.
  by rewrite dmap_id (hrj_source_sequential gpd_accepted mode{2}).
qed.

lemma hrj_source_law (mode0 : int) (event : hrj_input -> bool) &m :
  Pr[HyperballRenyiSourceDraw.sample(mode0) @ &m : event res] =
    mu (hrj_source gpd_accepted mode0) event.
proof.
  have h1 : Pr[HyperballRenyiSourceDraw.sample(mode0) @ &m : event res] =
    Pr[HyperballRenyiSourceDirect.sample(mode0) @ &m : event res] by
    byequiv hrj_source_direct.
  have h2 : Pr[HyperballRenyiSourceDirect.sample(mode0) @ &m : event res] =
    Pr[HyperballRenyiSourceSample.sample(mode0) @ &m : event res] by
    byequiv hrj_direct_sample.
  rewrite h1 h2.
  byphoare (_ : mode=mode0 ==> event res) => //.
  proc; rnd; skip; auto.
qed.

lemma hrj_source_draw_sample :
  equiv [HyperballRenyiSourceDraw.sample ~ HyperballRenyiSourceSample.sample :
    ={mode} ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 value hmode.
  rewrite (hrj_source_law mode{1} (pred1 value) &1) hmode.
  byphoare (_ : mode=mode{2} ==> res=value) => //.
  proc; rnd; skip; auto.
qed.

lemma hrj_source_phoare (mode0 : int) (event : hrj_input -> bool) :
  phoare [HyperballRenyiSourceDraw.sample : mode=mode0 ==> event res] =
    (mu (hrj_source gpd_accepted mode0) event).
proof.
  bypr => &m ->; exact (hrj_source_law mode0 event &m).
qed.

lemma hrj_source_draw_ll : islossless HyperballRenyiSourceDraw.sample.
proof.
  bypr => &m _; rewrite (hrj_source_law mode{m} (fun _ => true) &m).
  exact (hrj_source_ll gpd_accepted mode{m} gpd_accepted_ll).
qed.
