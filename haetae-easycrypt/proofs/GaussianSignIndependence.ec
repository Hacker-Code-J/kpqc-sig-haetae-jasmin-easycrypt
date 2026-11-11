require import AllCore IntDiv List Distr DList DProd DBool RealSeries StdOrder.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianIidBufferPath GaussianIidNormalization
  GaussianIidDistribution GaussianIidTermination GaussianUniformBytes GaussianSignBits.
require import IndependentSignSampling.
import RField RealOrder.

type gsi_state = BArray32768.t * BArray16.t.
op gsi_unsigned (result : gib_result) : gsi_state = (result.`1, result.`3).

module GSIInitialFull = {
  proc draw() : W8.t list * W8.t list = {
    var bytes : W8.t list;
    bytes <$ gbc_bytes 6664;
    return (take 32 bytes, drop 32 bytes);
  }
}.

module GSIInitialSplit = {
  proc draw() : W8.t list * W8.t list = {
    var signs, pending : W8.t list;
    var output : W8.t list * W8.t list;
    signs <$ gbc_bytes 32;
    pending <$ gbc_bytes 6632;
    output <- (signs, pending);
    return output;
  }
}.

module GSIArrayInitialFull = {
  proc draw(signsp : BArray512.t, sign_offset : int) : BArray512.t * W8.t list = {
    var pending : W8.t list;
    pending <$ gbc_bytes 6664;
    signsp <- gib_signs signsp sign_offset pending;
    pending <- drop 32 pending;
    return (signsp, pending);
  }
}.

module GSIArrayInitialSplit = {
  proc draw(signsp : BArray512.t, sign_offset : int) : BArray512.t * W8.t list = {
    var bytes, pending : W8.t list;
    bytes <$ gbc_bytes 32;
    signsp <- gib_signs signsp sign_offset bytes;
    pending <$ gbc_bytes 6632;
    return (signsp, pending);
  }
}.

(* The complete unsigned state, including the square buffer, is returned.
   No sign bytes or sign-array argument occur in this procedure. *)
module GaussianUnsignedLoop = {
  proc run(rp : BArray32768.t, sqsump : BArray16.t, count : BArray8.t,
      pending : W8.t list, n : int, sample_offset : int) : gsi_state = {
    var bytes : W8.t list;
    var accepted : int;
    (rp, sqsump, count) <- gib_consume rp sqsump count pending n (n = 257) sample_offset;
    accepted <- W64.to_uint (BArray8.get64 count 0);
    while (accepted < n) {
      pending <- gib_remainder pending;
      bytes <$ gib_block;
      pending <- pending ++ bytes;
      (rp, sqsump, count) <- gib_consume rp sqsump count pending (n - accepted)
        (n = 257) (sample_offset + accepted);
      accepted <- accepted + W64.to_uint (BArray8.get64 count 0);
    }
    return (rp, sqsump);
  }
}.

module GaussianUnsignedIid = {
  proc sample(rp : BArray32768.t, sqsump : BArray16.t,
      n : int, sample_offset : int) : gsi_state = {
    var count : BArray8.t;
    var pending : W8.t list;
    var state : gsi_state;
    count <- witness;
    pending <$ gbc_bytes 6632;
    state <@ GaussianUnsignedLoop.run(rp, sqsump, count, pending, n, sample_offset);
    return state;
  }
}.

module GaussianIidSignFront = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result = {
    var count : BArray8.t;
    var pending : W8.t list;
    var state : gsi_state;
    count <- witness;
    (signsp, pending) <@ GSIArrayInitialSplit.draw(signsp, sign_offset);
    state <@ GaussianUnsignedLoop.run(rp, sqsump, count, pending, n, sample_offset);
    return (state.`1, signsp, state.`2);
  }
}.

module GSIFrontBySample = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result = {
    var bytes : W8.t list;
    var state : gsi_state;
    bytes <$ gbc_bytes 32;
    signsp <- gib_signs signsp sign_offset bytes;
    state <@ GaussianUnsignedIid.sample(rp, sqsump, n, sample_offset);
    return (state.`1, signsp, state.`2);
  }
}.

module GaussianIidSignFactor = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result = {
    var bytes : W8.t list;
    var state : gsi_state;
    state <@ GaussianUnsignedIid.sample(rp, sqsump, n, sample_offset);
    bytes <$ gbc_bytes 32;
    signsp <- gib_signs signsp sign_offset bytes;
    return (state.`1, signsp, state.`2);
  }
}.

(* This public wrapper exposes the independent final sign draw while retaining
   the entire result of the actual iid-buffer computation. *)
module GaussianIidSignRedraw = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result = {
    var result : gib_result;
    var bytes : W8.t list;
    result <@ GaussianIidBuffer.sample(rp, signsp, sqsump, n, sample_offset, sign_offset);
    bytes <$ gbc_bytes 32;
    signsp <- gib_signs result.`2 sign_offset bytes;
    return (result.`1, signsp, result.`3);
  }
}.

module GSIRepeatSigns = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result = {
    var result : gib_result;
    var bytes : W8.t list;
    result <@ GaussianIidSignFactor.sample(rp, signsp, sqsump, n, sample_offset, sign_offset);
    bytes <$ gbc_bytes 32;
    signsp <- gib_signs result.`2 sign_offset bytes;
    return (result.`1, signsp, result.`3);
  }
}.

lemma gsi_signs_take before offset bytes :
  gib_signs before offset (take 32 bytes) = gib_signs before offset bytes.
proof.
  rewrite /gib_signs; apply BArray512.init_ext => j hj /=.
  case (offset <= j < offset + 32) => hpart //.
  by rewrite nth_take 1:/# 1:/#.
qed.

lemma gsi_signs_overwrite before offset old_bytes new_bytes :
  gib_signs (gib_signs before offset old_bytes) offset new_bytes =
  gib_signs before offset new_bytes.
proof.
  rewrite /gib_signs; apply BArray512.init_ext => j hj /=.
  case (offset <= j < offset + 32) => hpart //.
  by rewrite BArray512.initiE 1:hj /= hpart.
qed.

lemma gsi_initial_full_law (event : W8.t list * W8.t list -> bool) &m :
  Pr[GSIInitialFull.draw() @ &m : event res] =
  mu (gbc_bytes 32 `*` gbc_bytes 6632) event.
proof.
  rewrite -(gbc_bytes_split 32 6632 _ _) 1,2:// /= dmapE.
  byphoare (_ : true ==> event res) => //.
  proc; rnd; skip; auto.
qed.

lemma gsi_initial_split_law (event : W8.t list * W8.t list -> bool) &m :
  Pr[GSIInitialSplit.draw() @ &m : event res] =
  mu (gbc_bytes 32 `*` gbc_bytes 6632) event.
proof.
  byphoare (_ : true ==> event res) => //.
  proc; rndsem* 0; rnd; skip; auto => />.
  by rewrite dprod_dlet.
qed.

lemma gsi_initial_equiv :
  equiv [GSIInitialFull.draw ~ GSIInitialSplit.draw : true ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 result.
  by rewrite (gsi_initial_full_law (pred1 result) &1)
    (gsi_initial_split_law (pred1 result) &2).
qed.

lemma gsi_array_full_law before offset (event : BArray512.t * W8.t list -> bool) &m :
  Pr[GSIArrayInitialFull.draw(before, offset) @ &m : event res] =
  mu (gbc_bytes 32 `*` gbc_bytes 6632)
    (fun (pair : W8.t list * W8.t list) => event (gib_signs before offset pair.`1, pair.`2)).
proof.
  rewrite -(gsi_initial_full_law
    (fun (pair : W8.t list * W8.t list) => event (gib_signs before offset pair.`1, pair.`2)) &m).
  byequiv (_ : signsp{1} = before /\ sign_offset{1} = offset ==>
    res{1} = (gib_signs before offset res{2}.`1, res{2}.`2)) => //.
  proc; wp; rnd; skip; auto => />.
  move=> bytes hb; by rewrite gsi_signs_take.
qed.

lemma gsi_array_split_law before offset (event : BArray512.t * W8.t list -> bool) &m :
  Pr[GSIArrayInitialSplit.draw(before, offset) @ &m : event res] =
  mu (gbc_bytes 32 `*` gbc_bytes 6632)
    (fun (pair : W8.t list * W8.t list) => event (gib_signs before offset pair.`1, pair.`2)).
proof.
  rewrite -(gsi_initial_split_law
    (fun (pair : W8.t list * W8.t list) => event (gib_signs before offset pair.`1, pair.`2)) &m).
  byequiv (_ : signsp{1} = before /\ sign_offset{1} = offset ==>
    res{1} = (gib_signs before offset res{2}.`1, res{2}.`2)) => //.
  by proc; wp; rnd; wp; rnd; skip; auto.
qed.

lemma gsi_array_initial_equiv :
  equiv [GSIArrayInitialFull.draw ~ GSIArrayInitialSplit.draw :
    ={signsp, sign_offset} ==> ={res}].
proof.
  bypr (res{1}) (res{2}) => //= &1 &2 result [hs ho].
  rewrite (gsi_array_full_law signsp{1} sign_offset{1} (pred1 result) &1)
    (gsi_array_split_law signsp{2} sign_offset{2} (pred1 result) &2).
  by rewrite hs ho.
qed.

lemma gsi_uniform_front :
  equiv [GaussianIidBufferUniform.sample ~ GaussianIidSignFront.sample :
    ={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res}].
proof.
  proc.
  outline {1} [5 .. 7] ~ GaussianUnsignedLoop.run.
  outline {1} [2 .. 4] ~ GSIArrayInitialFull.draw.
  seq 2 2 : (={rp, signsp, sqsump, n, sample_offset, sign_offset, count, pending}).
  + call gsi_array_initial_equiv; by auto.
  wp; call (_ : ={rp, sqsump, count, pending, n, sample_offset} ==> ={res}); first by sim.
  skip; auto.
qed.

lemma gsi_front_factor :
  equiv [GaussianIidSignFront.sample ~ GaussianIidSignFactor.sample :
    ={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res}].
proof.
  transitivity GSIFrontBySample.sample
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res})
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res}).
  + move=> &1 &2 h; exists (rp{2}, signsp{2}, sqsump{2}, n{2}, sample_offset{2}, sign_offset{2}); smt().
  + smt().
  + proc; inline {1} GSIArrayInitialSplit.draw; inline {2} GaussianUnsignedIid.sample.
    wp; call (_ : ={rp, sqsump, count, pending, n, sample_offset} ==> ={res}); first by sim.
    wp; rnd; wp; rnd; wp; skip; auto.
  proc; swap {1} [1 .. 2] 1; by sim.
qed.

lemma gsi_uniform_factor :
  equiv [GaussianIidBufferUniform.sample ~ GaussianIidSignFactor.sample :
    ={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res}].
proof.
  transitivity GaussianIidSignFront.sample
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res})
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res}).
  + move=> &1 &2 h; exists (rp{2}, signsp{2}, sqsump{2}, n{2}, sample_offset{2}, sign_offset{2}); smt().
  + smt().
  + exact gsi_uniform_front.
  exact gsi_front_factor.
qed.

lemma gsi_actual_factor :
  equiv [GaussianIidBuffer.sample ~ GaussianIidSignFactor.sample :
    ={rp, signsp, sqsump, n, sample_offset, sign_offset} /\
    gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res}].
proof.
  transitivity GaussianIidBufferFunctional.sample
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} /\
      gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res})
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res}).
  + move=> &1 &2 h; exists (rp{2}, signsp{2}, sqsump{2}, n{2}, sample_offset{2}, sign_offset{2}); smt().
  + smt().
  + exact gib_actual_functional.
  transitivity GaussianIidBufferUniform.sample
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res})
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res}).
  + move=> &1 &2 h; exists (rp{2}, signsp{2}, sqsump{2}, n{2}, sample_offset{2}, sign_offset{2}); smt().
  + smt().
  + exact gid_functional_uniform.
  exact gsi_uniform_factor.
qed.

lemma gsi_redraw_repeat :
  equiv [GaussianIidSignRedraw.sample ~ GSIRepeatSigns.sample :
    ={rp, signsp, sqsump, n, sample_offset, sign_offset} /\
    gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res}].
proof. proc; wp; rnd; call gsi_actual_factor; skip; auto. qed.

lemma gsi_repeat_factor :
  equiv [GSIRepeatSigns.sample ~ GaussianIidSignFactor.sample :
    ={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res}].
proof.
  proc; inline {1} GaussianIidSignFactor.sample.
  wp; rnd; wp; rnd {1}.
  call (_ : ={rp, sqsump, n, sample_offset} ==> ={res}); first by sim.
  wp; skip; auto => />.
  smt(gbc_bytes_ll gsi_signs_overwrite).
qed.

lemma gsi_actual_redraw :
  equiv [GaussianIidBuffer.sample ~ GaussianIidSignRedraw.sample :
    ={rp, signsp, sqsump, n, sample_offset, sign_offset} /\
    gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res}].
proof.
  transitivity GaussianIidSignFactor.sample
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} /\
      gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res})
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} /\
      gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res}).
  + move=> &1 &2 h; exists (rp{2}, signsp{2}, sqsump{2}, n{2}, sample_offset{2}, sign_offset{2}); smt().
  + smt().
  + exact gsi_actual_factor.
  symmetry.
  transitivity GSIRepeatSigns.sample
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} /\
      gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res})
    (={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res}).
  + move=> &1 &2 h; exists (rp{2}, signsp{2}, sqsump{2}, n{2}, sample_offset{2}, sign_offset{2}); smt().
  + smt().
  + exact gsi_redraw_repeat.
  exact gsi_repeat_factor.
qed.

type gsi_input = BArray32768.t * BArray512.t * BArray16.t * int * int * int.
clone IndependentSign as GSIIndependent with
  type input <- gsi_input,
  type output <- gib_result,
  type sign <- W8.t list.

(* Observe the fresh bits and retain both unsigned arrays. The generic
   wrapper calls the actual iid-buffer procedure before sampling signs. *)
lemma gsi_redraw_observer (signoff0 : int) :
  equiv [GaussianIidSignRedraw.sample ~ GSIIndependent.Wrapper(GaussianIidBuffer).sample :
    x{2} = (rp{1}, signsp{1}, sqsump{1}, n{1}, sample_offset{1}, sign_offset{1}) /\
    d{2} = gbc_bytes 32 /\ sign_offset{1} = signoff0 /\
    0 <= signoff0 /\ signoff0 + 32 <= 512 ==>
    (gsb_result_bits res{1} signoff0, gsi_unsigned res{1}) =
    (gsb_bits res{2}.`1, gsi_unsigned res{2}.`2)].
proof.
  proc; wp; rnd.
  call (_ : ={rp, signsp, sqsump, n, sample_offset, sign_offset} ==> ={res}); first by sim.
  skip; auto => />.
  move=> hlo hhi result bytes hb.
  have hsize := supp_dlist_size W8.dword 32 bytes _ hb; first trivial.
  have hbits := gsb_signs_decode32 result.`1 result.`2 result.`3 signoff0 bytes hlo hhi hsize.
  exact hbits.
qed.

(* An arbitrary joint event may inspect every sample-array byte and both
   square words, not only the visible magnitudes. *)
lemma gsi_actual_independent_joint initial initial_signs initial_squares n offset signoff
    (event : bool list * gsi_state -> bool) &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial, initial_signs, initial_squares, n, offset, signoff)
    @ &m : event (gsb_result_bits res signoff, gsi_unsigned res)] =
  Pr[GSIIndependent.Wrapper(GaussianIidBuffer).sample
      ((initial, initial_signs, initial_squares, n, offset, signoff), gbc_bytes 32)
    @ &m : event (gsb_bits res.`1, gsi_unsigned res.`2)].
proof.
  move=> hb.
  have he :
    Pr[GaussianIidBuffer.sample(initial, initial_signs, initial_squares, n, offset, signoff)
      @ &m : event (gsb_result_bits res signoff, gsi_unsigned res)] =
    Pr[GaussianIidSignRedraw.sample(initial, initial_signs, initial_squares, n, offset, signoff)
      @ &m : event (gsb_result_bits res signoff, gsi_unsigned res)] by
    byequiv gsi_actual_redraw.
  rewrite he.
  by byequiv (gsi_redraw_observer signoff) => //; move: hb; rewrite /gib_bounds; smt().
qed.

lemma gsi_sign_state_independent initial initial_signs initial_squares n offset signoff
    (sign_event : bool list -> bool) (state_event : gsi_state -> bool) &m :
  gib_bounds n offset signoff =>
  Pr[GaussianIidBuffer.sample(initial, initial_signs, initial_squares, n, offset, signoff)
    @ &m : sign_event (gsb_result_bits res signoff) /\ state_event (gsi_unsigned res)] =
  mu (dlist dbool 256) sign_event *
  Pr[GaussianIidBuffer.sample(initial, initial_signs, initial_squares, n, offset, signoff)
    @ &m : state_event (gsi_unsigned res)].
proof.
  move=> hb.
  have he := gsi_actual_independent_joint initial initial_signs initial_squares n offset signoff
    (fun (observation : bool list * gsi_state) => sign_event observation.`1 /\ state_event observation.`2)
    &m hb.
  rewrite /= in he; rewrite he.
  rewrite (GSIIndependent.rectangle GaussianIidBuffer
    (initial, initial_signs, initial_squares, n, offset, signoff) (gbc_bytes 32)
    (fun bytes => sign_event (gsb_bits bytes)) (fun result => state_event (gsi_unsigned result)) &m).
  have hbits : mu (gbc_bytes 32) (fun bytes => sign_event (gsb_bits bytes)) =
    mu (dlist dbool 256) sign_event by
    rewrite -(dmapE (gbc_bytes 32) gsb_bits sign_event) gsb_uniform256.
  by rewrite hbits.
qed.
