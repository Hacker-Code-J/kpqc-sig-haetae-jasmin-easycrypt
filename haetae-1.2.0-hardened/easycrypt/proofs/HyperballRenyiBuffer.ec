require import AllCore IntDiv List Distr DList DProd.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianIidBufferPath GaussianIidVisible
  GaussianUniformBytes GaussianSignIndependence GaussianPayloadSpec GaussianPayloadEncoding
  GaussianPayloadBufferSpec GaussianPayloadBufferPath GaussianPayloadBufferTrace
  GaussianPayloadTrace GaussianPayloadDraw GaussianWindowSpec GaussianStreamSpec
  GaussianStreamAccumulator GaussianAccumulatorCorrectness HyperballGaussianBounds.

(* Every stored word is replaced, while the unwritten dummy contributes only
   to the canonical square sum. Bytes outside the two windows are retained. *)
op hrb_values (initial : BArray32768.t) (offset : int) (history : int list) : BArray32768.t =
  BArray32768.init (fun j =>
    if offset <= j %/ 8 < offset+256 then
      W64.of_int (nth 0 (map gpd_magnitude history) (j %/ 8-offset)) \bits8 (j %% 8)
    else BArray32768.get8 initial j).

op hrb_squares (value : int) : BArray16.t =
  BArray16.set64 (BArray16.set64 witness 0 (W64.of_int (value %% 281474976710656)))
    1 (W64.of_int (value %/ 281474976710656)).

op hrb_unsigned (initial_values : BArray32768.t) (initial_squares : BArray16.t)
    (offset : int) (history : int list) : gsi_state =
  (hrb_values initial_values offset history,
   hrb_squares (gauss_stream_value initial_squares+gpd_sum history)).

op hrb_result (initial : gib_result) (offset signoff : int)
    (history : int list) (bytes : W8.t list) : gib_result =
  let unsigned = hrb_unsigned initial.`1 initial.`3 offset history in
  (unsigned.`1,gib_signs initial.`2 signoff bytes,unsigned.`2).

lemma hrb_values_get initial offset history i : 0 <= i < 4096 =>
  BArray32768.get64 (hrb_values initial offset history) i =
    if offset <= i < offset+256 then W64.of_int (nth 0 (map gpd_magnitude history) (i-offset))
    else BArray32768.get64 initial i.
proof.
  move=> hi; apply W8u8.wordP => byte hb.
  rewrite BArray32768.get64d_byte 1:hb /hrb_values BArray32768.initiE 1:/# /=.
  have hd : (8*i+byte) %/ 8=i by rewrite divz_eqP //; smt().
  have hm : (8*i+byte) %% 8=byte by rewrite (mulzC 8 i) modzMDl modz_small; smt().
  rewrite hd hm.
  case (offset <= i < offset+256) => hin /=; first trivial.
  by rewrite BArray32768.get64d_byte.
qed.

lemma hrb_values_frame initial offset history :
  gauss_big_output_frame initial (hrb_values initial offset history) offset 256.
proof. move=> i hi hout; by rewrite hrb_values_get 1:hi hout. qed.

lemma hrb_squares_canonical value :
  W64.to_uint (BArray16.get64 (hrb_squares value) 0) < 281474976710656.
proof.
  have hr := modz_cmp value 281474976710656 _; first trivial.
  rewrite /hrb_squares /= W64.of_uintK modz_small; smt().
qed.

lemma hrb_squares_value value :
  0 <= value < 281474976710656*18446744073709551616 =>
  gauss_stream_value (hrb_squares value)=value.
proof.
  move=> hv.
  have hr := modz_cmp value 281474976710656 _; first trivial.
  have hd : 0 <= value %/ 281474976710656 < 18446744073709551616 by smt(divz_cmp).
  rewrite /gauss_stream_value /gauss_limb_value /hrb_squares /= !W64.of_uintK.
  rewrite (modz_small (value %% 281474976710656) W64.modulus) 1:/#.
  rewrite (modz_small (value %/ 281474976710656) W64.modulus) 1:/#.
  have he := divz_eq value 281474976710656; smt().
qed.

lemma hrb_state_reconstruct previous initial_values initial_squares n offset history values squares :
  n=256 \/ n=257 => size history=n =>
  gpt_state previous initial_values initial_squares n offset history values squares =>
  (values,squares)=hrb_unsigned initial_values initial_squares offset history /\
  hb_cumulative_square_bound (previous+n) squares.
proof.
  move=> hn hsize.
  move=> hstate.
  have [hcount [hvisible [hframe [hc hvalue]]]] :
    size history <= n /\
    gib_visible values offset (size history)=map gpd_magnitude (take 256 history) /\
    gauss_big_output_frame initial_values values offset 256 /\
    hb_cumulative_square_bound (previous+size history) squares /\
    gauss_stream_value squares=gauss_stream_value initial_squares+gpd_sum history
    by move: hstate; rewrite /gpt_state.

  rewrite hsize in hc.
  have hvalues : values=hrb_values initial_values offset history.
  + apply BArray32768.ext_eq64 => i hi.
    have hi' : 0 <= i < 4096 by smt().
    rewrite hrb_values_get 1:hi'.
    case (offset <= i < offset+256) => hin /=; last exact (hframe i hi' hin).
    have hj : 0 <= i-offset < min (size history) 256 by smt().
    have hv := giv_nth values offset (size history) (i-offset) hj.
    have ht : nth 0 (take 256 (map gpd_magnitude history)) (i-offset)=
        nth 0 (map gpd_magnitude history) (i-offset) by apply nth_take; smt().
    have hi0 : offset+(i-offset)=i by ring.
    move: hv; rewrite hvisible map_take ht hi0 => hv.
    by rewrite hv W64.to_uintK.
  have [hlo hhi] := hb_cumulative_canonical (previous+n) squares hc.
  have hfit : 0 <= gauss_stream_value squares < 281474976710656*18446744073709551616.
  + move: hc; rewrite /hb_cumulative_square_bound /hb_event_max; smt().
  have hsquares : squares=hrb_squares (gauss_stream_value initial_squares+gpd_sum history).
  + apply gs_canonical_square_unique; first exact hlo.
    + exact hrb_squares_canonical.
    by rewrite -hvalue hrb_squares_value.
  split; last exact hc.
  by rewrite /hrb_unsigned hvalues hsquares.
qed.

op hrb_sign_frame (before after : BArray512.t) (offset : int) : bool =
  forall j, 0 <= j < 512 => !(offset <= j < offset+32) =>
    BArray512.get8 after j=BArray512.get8 before j.

lemma hrb_signs_frame before offset bytes :
  hrb_sign_frame before (gib_signs before offset bytes) offset.
proof.
  move=> j hj hout; by rewrite /gib_signs BArray512.initiE 1:hj /= hout.
qed.

lemma hrb_signs_frame_overwrite before after offset bytes :
  hrb_sign_frame before after offset =>
  gib_signs after offset bytes=gib_signs before offset bytes.
proof.
  move=> hf; rewrite /gib_signs; apply BArray512.init_ext => j hj /=.
  case (offset <= j < offset+32) => hin //.
  exact (hf j hj hin).
qed.

lemma hrb_payload_sign_frame initial_signs signoff0 :
  hoare [GaussianPayloadBuffer.sample : signsp=initial_signs /\ sign_offset=signoff0 ==>
    hrb_sign_frame initial_signs res.`1.`2 signoff0].
proof.
  proc.
  while (hrb_sign_frame initial_signs signsp signoff0).
  + wp; rnd; wp; skip; auto.
  wp; rnd; wp; skip; auto => />.
  smt(hrb_signs_frame).
qed.

lemma hrb_payload_unsigned previous initial_values initial_signs initial_squares n0 offset0 signoff0 :
  gib_bounds n0 offset0 signoff0 =>
  hb_cumulative_square_bound previous initial_squares => previous+n0 <= 2818 =>
  hoare [GaussianPayloadBuffer.sample :
    rp=initial_values /\ signsp=initial_signs /\ sqsump=initial_squares /\
    n=n0 /\ sample_offset=offset0 /\ sign_offset=signoff0 ==>
    (res.`1.`1,res.`1.`3)=hrb_unsigned initial_values initial_squares offset0 res.`2 /\
    hb_cumulative_square_bound (previous+n0) res.`1.`3].
proof.
  move=> hb hc hbudget.
  conseq (gpt_buffer_correct previous initial_values initial_signs initial_squares n0 offset0 signoff0
    hb hc hbudget) => //.
  move=> &m _ result [hsize hstate].
  apply (hrb_state_reconstruct previous initial_values initial_squares n0 offset0
    result.`2 result.`1.`1 result.`1.`3) => //.
  move: hb; rewrite /gib_bounds; smt().
qed.

module HyperballRenyiBufferDraw = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result = {
    var history : int list;
    var bytes : W8.t list;
    history <$ dlist gpd_accepted n;
    bytes <$ gbc_bytes 32;
    return hrb_result (rp,signsp,sqsump) sample_offset sign_offset history bytes;
  }
}.

module HRBPayloadRedraw = {
  proc sample(rp : BArray32768.t, signsp : BArray512.t, sqsump : BArray16.t,
      n : int, sample_offset : int, sign_offset : int) : gib_result = {
    var result : gpb_result;
    var bytes : W8.t list;
    result <@ GaussianPayloadBuffer.sample(rp,signsp,sqsump,n,sample_offset,sign_offset);
    bytes <$ gbc_bytes 32;
    signsp <- gib_signs result.`1.`2 sign_offset bytes;
    return (result.`1.`1,signsp,result.`1.`3);
  }
}.

lemma hrb_redraw_payload :
  equiv [GaussianIidSignRedraw.sample ~ HRBPayloadRedraw.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} /\
    gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res}].
proof. proc; wp; rnd; call gpb_actual_projection; skip; auto. qed.

lemma hrb_draw_lossless : islossless HyperballRenyiBufferDraw.sample.
proof. proc; rnd; rnd; skip; auto => />; smt(gbc_bytes_ll dlist_ll gpd_accepted_ll). qed.


lemma hrb_payload_draw_unsigned previous initial_values initial_signs initial_squares n0 offset0 signoff0 :
  gib_bounds n0 offset0 signoff0 =>
  hb_cumulative_square_bound previous initial_squares => previous+n0 <= 2818 =>
  equiv [GaussianPayloadBuffer.sample ~ GaussianPayloadDraw.sample :
    rp{1}=initial_values /\ signsp{1}=initial_signs /\ sqsump{1}=initial_squares /\
    n{1}=n0 /\ sample_offset{1}=offset0 /\ sign_offset{1}=signoff0 /\ n{2}=n0 ==>
    res{1}.`2=res{2} /\
    (res{1}.`1.`1,res{1}.`1.`3)=hrb_unsigned initial_values initial_squares offset0 res{2} /\
    hb_cumulative_square_bound (previous+n0) res{1}.`1.`3].
proof.
  move=> hb hc hbudget.
  conseq gpd_buffer_draw
    (hrb_payload_unsigned previous initial_values initial_signs initial_squares n0 offset0 signoff0
      hb hc hbudget) _ => />.
  + move: hb; rewrite /gib_bounds; smt().
qed.

lemma hrb_payload_draw_complete previous initial_values initial_signs initial_squares n0 offset0 signoff0 :
  gib_bounds n0 offset0 signoff0 =>
  hb_cumulative_square_bound previous initial_squares => previous+n0 <= 2818 =>
  equiv [GaussianPayloadBuffer.sample ~ GaussianPayloadDraw.sample :
    rp{1}=initial_values /\ signsp{1}=initial_signs /\ sqsump{1}=initial_squares /\
    n{1}=n0 /\ sample_offset{1}=offset0 /\ sign_offset{1}=signoff0 /\ n{2}=n0 ==>
    (res{1}.`1.`1,res{1}.`1.`3)=hrb_unsigned initial_values initial_squares offset0 res{2} /\
    hrb_sign_frame initial_signs res{1}.`1.`2 signoff0 /\
    hb_cumulative_square_bound (previous+n0) res{1}.`1.`3].
proof.
  move=> hb hc hbudget.
  conseq (hrb_payload_draw_unsigned previous initial_values initial_signs initial_squares n0 offset0 signoff0
    hb hc hbudget) (hrb_payload_sign_frame initial_signs signoff0) _ => />; smt().
qed.

lemma hrb_payload_redraw_draw_fixed previous initial_values initial_signs initial_squares n0 offset0 signoff0 :
  gib_bounds n0 offset0 signoff0 =>
  hb_cumulative_square_bound previous initial_squares => previous+n0 <= 2818 =>
  equiv [HRBPayloadRedraw.sample ~ HyperballRenyiBufferDraw.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} /\
    rp{1}=initial_values /\ signsp{1}=initial_signs /\ sqsump{1}=initial_squares /\
    n{1}=n0 /\ sample_offset{1}=offset0 /\ sign_offset{1}=signoff0 ==>
    ={res} /\ hb_cumulative_square_bound (previous+n0) res{1}.`3].
proof.
  move=> hb hc hbudget.
  proc; outline {2} [1 .. 1] ~ GaussianPayloadDraw.sample.
  wp; rnd.
  call (hrb_payload_draw_complete previous initial_values initial_signs initial_squares n0 offset0 signoff0
    hb hc hbudget).
  skip; auto => />; rewrite /hrb_result /=; smt(hrb_signs_frame_overwrite).
qed.


lemma hrb_actual_draw_fixed previous initial_values initial_signs initial_squares n0 offset0 signoff0 :
  gib_bounds n0 offset0 signoff0 =>
  hb_cumulative_square_bound previous initial_squares => previous+n0 <= 2818 =>
  equiv [GaussianIidBuffer.sample ~ HyperballRenyiBufferDraw.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} /\
    rp{1}=initial_values /\ signsp{1}=initial_signs /\ sqsump{1}=initial_squares /\
    n{1}=n0 /\ sample_offset{1}=offset0 /\ sign_offset{1}=signoff0 ==>
    ={res} /\ hb_cumulative_square_bound (previous+n0) res{1}.`3].
proof.
  move=> hb hc hbudget.
  transitivity GaussianIidSignRedraw.sample
    (={rp,signsp,sqsump,n,sample_offset,sign_offset} /\
      gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res})
    (={rp,signsp,sqsump,n,sample_offset,sign_offset} /\
      rp{1}=initial_values /\ signsp{1}=initial_signs /\ sqsump{1}=initial_squares /\
      n{1}=n0 /\ sample_offset{1}=offset0 /\ sign_offset{1}=signoff0 ==>
      ={res} /\ hb_cumulative_square_bound (previous+n0) res{1}.`3).
  + move=> &1 &2 h; exists (rp{2},signsp{2},sqsump{2},n{2},sample_offset{2},sign_offset{2}); smt().
  + smt().
  + exact gsi_actual_redraw.
  transitivity HRBPayloadRedraw.sample
    (={rp,signsp,sqsump,n,sample_offset,sign_offset} /\
      gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res})
    (={rp,signsp,sqsump,n,sample_offset,sign_offset} /\
      rp{1}=initial_values /\ signsp{1}=initial_signs /\ sqsump{1}=initial_squares /\
      n{1}=n0 /\ sample_offset{1}=offset0 /\ sign_offset{1}=signoff0 ==>
      ={res} /\ hb_cumulative_square_bound (previous+n0) res{1}.`3).
  + move=> &1 &2 h; exists (rp{2},signsp{2},sqsump{2},n{2},sample_offset{2},sign_offset{2}); smt().
  + smt().
  + exact hrb_redraw_payload.
  exact (hrb_payload_redraw_draw_fixed previous initial_values initial_signs initial_squares n0 offset0 signoff0
    hb hc hbudget).
qed.

lemma hrb_actual_draw previous n0 :
  equiv [GaussianIidBuffer.sample ~ HyperballRenyiBufferDraw.sample :
    ={rp,signsp,sqsump,n,sample_offset,sign_offset} /\ n{1}=n0 /\
    gib_bounds n0 sample_offset{1} sign_offset{1} /\
    hb_cumulative_square_bound previous sqsump{1} /\ previous+n0<=2818 ==>
    ={res} /\ hb_cumulative_square_bound (previous+n0) res{1}.`3].
proof.
  bypr (res{1},hb_cumulative_square_bound (previous+n0) res{1}.`3)
    (res{2},true) => //=.
  + smt().
  move=> &1 &2 observation hpre.
  have hb : gib_bounds n0 sample_offset{1} sign_offset{1} by smt().
  have hc : hb_cumulative_square_bound previous sqsump{1} by smt().
  have hbudget : previous+n0<=2818 by smt().
  by byequiv (hrb_actual_draw_fixed previous rp{1} signsp{1} sqsump{1} n0
    sample_offset{1} sign_offset{1} hb hc hbudget) => //; smt().
qed.

lemma hrb_draw_law (initial : gib_result) n0 offset0 signoff0 (event : gib_result -> bool) &m :
  Pr[HyperballRenyiBufferDraw.sample(initial.`1,initial.`2,initial.`3,n0,offset0,signoff0)
    @ &m : event res] =
  mu (dlist gpd_accepted n0 `*` gbc_bytes 32)
    (fun (block : int list * W8.t list) => event (hrb_result initial offset0 signoff0 block.`1 block.`2)).
proof.
  byphoare (_ : rp=initial.`1 /\ signsp=initial.`2 /\ sqsump=initial.`3 /\
    n=n0 /\ sample_offset=offset0 /\ sign_offset=signoff0 ==> event res) => //.
  proc; rndsem* 0.
  rnd (fun (block : int list * W8.t list) => event (hrb_result initial offset0 signoff0 block.`1 block.`2)).
  skip; auto => />.
  by rewrite dprod_dlet.
qed.

lemma hrb_actual_law previous (initial : gib_result) n0 offset0 signoff0
    (event : gib_result -> bool) &m :
  gib_bounds n0 offset0 signoff0 =>
  hb_cumulative_square_bound previous initial.`3 => previous+n0<=2818 =>
  Pr[GaussianIidBuffer.sample(initial.`1,initial.`2,initial.`3,n0,offset0,signoff0)
    @ &m : event res] =
  mu (dlist gpd_accepted n0 `*` gbc_bytes 32)
    (fun (block : int list * W8.t list) => event (hrb_result initial offset0 signoff0 block.`1 block.`2)).
proof.
  move=> hb hc hbudget.
  rewrite -(hrb_draw_law initial n0 offset0 signoff0 event &m).
  by byequiv (hrb_actual_draw previous n0) => //; smt().
qed.
