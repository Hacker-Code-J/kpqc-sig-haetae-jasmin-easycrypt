require import AllCore IntDiv List Distr DList.
from Jasmin require import JModel_x86.
require import GaussianIidBufferSpec GaussianTraceSpec GaussianTraceProperties
  GaussianWindowSpec GaussianOffsetBridge GaussianConsumerSpec GaussianConsumerCorrectness
  GaussianSequenceCorrectness GaussianStreamBuffer GaussianStreamComposition GaussianStreamCorrectness
  GaussianRefillCorrectness GaussianByteCarryDistribution GaussianRetryConsumerTotal.

op [opaque] gib_buffer (buf : BArray8192.t) (offset : int) (pending : W8.t list) : bool =
  forall j, 0 <= j < size pending =>
    BArray8192.get8 buf (offset + j) = nth W8.zero pending j.

lemma gib_buffer_get buf offset pending j :
  gib_buffer buf offset pending => 0 <= j < size pending =>
  BArray8192.get8 buf (offset + j) = nth W8.zero pending j.
proof. rewrite /gib_buffer => hp hj; exact (hp j hj). qed.

lemma gib_block_size bytes : bytes \in gib_block => size bytes = 136.
proof. exact (supp_dlist_size W8.dword 136 bytes _); trivial. qed.

lemma gib_block_ll : is_lossless gib_block.
proof. by rewrite /gib_block dlist_ll W8.dword_ll. qed.

lemma gib_buffer_empty buf offset : gib_buffer buf offset [].
proof. rewrite /gib_buffer /=; smt(). qed.

lemma gib_buffer_fill_append buf offset pending bytes :
  0 <= offset => offset + size pending + 136 <= 8192 => size bytes = 136 =>
  gib_buffer buf offset pending =>
  gib_buffer (gib_fill buf (offset + size pending) bytes) offset (pending ++ bytes).
proof.
  move=> ho hcap hsize; rewrite /gib_buffer => hp j.
  rewrite size_cat hsize => hj.
  rewrite /gib_fill BArray8192.initiE 1:/# nth_cat.
  case (j < size pending) => hpart.
  + have h := hp j _; first smt().
    smt().
  smt().
qed.

lemma gib_buffer_drop buf offset pending skipped :
  0 <= skipped <= size pending => gib_buffer buf offset pending =>
  gib_buffer buf (offset + skipped) (drop skipped pending).
proof.
  move=> hk; rewrite /gib_buffer => hp j hj.
  have hsize := size_ge0 pending.
  have hj' : 0 <= skipped + j < size pending by
    move: hj; rewrite size_drop; smt().
  have h := hp (skipped + j) hj'.
  rewrite nth_drop 1:/#; smt().
qed.

lemma gib_remainder_size pending :
  size (gib_remainder pending) = size pending %% 26 /\
  0 <= size (gib_remainder pending) < 26.
proof.
  have hs := size_ge0 pending.
  have hq : 0 <= size pending %/ 26 by rewrite divz_ge0.
  have hd := divz_eq (size pending) 26.
  have hr := modz_cmp (size pending) 26.
  rewrite /gib_remainder size_drop; smt().
qed.

lemma gib_counts_decode requested available :
  0 <= requested <= 512 => 0 <= available <= 8192 =>
  gauss_requested (gib_counts requested available) = requested /\
  gauss_available (gib_counts requested available) = available.
proof. by rewrite /gib_counts; apply gauss_counts_encode. qed.

lemma gib_counts_word requested available :
  0 <= requested <= 512 =>
  gib_counts requested available =
    (W64.of_int available `<<` W8.of_int 32) `|` W64.of_int requested.
proof.
  move=> hn; rewrite /gib_counts /(`<<`) W8.of_uintK /= gs_pack_counts_word 1:/#.
  trivial.
qed.

lemma gib_remainder_word available remaining :
  W64.to_uint remaining %% 26 = available %% 26 =>
  !(W64.of_int 26 \ule remaining) => remaining = W64.of_int (available %% 26).
proof. exact (gs_mod26_word_done available remaining). qed.

lemma gib_guard_word accepted requested :
  0 <= accepted <= requested => requested <= 512 =>
  (W64.of_int accepted \ult W64.of_int requested) = (accepted < requested).
proof. move=> hc hn; rewrite W64.ultE !W64.of_uintK /= !modz_small; smt(). qed.

lemma gib_remaining_word accepted requested :
  W64.of_int requested - W64.of_int accepted = W64.of_int (requested - accepted).
proof. by rewrite W64.of_intS. qed.

lemma gib_offset_word offset accepted :
  W64.of_int offset + W64.of_int accepted = W64.of_int (offset + accepted).
proof. by rewrite W64.of_intD. qed.

lemma gib_count_add_word accepted (got : W64.t) :
  0 <= accepted => accepted + W64.to_uint got <= 512 =>
  W64.to_uint (W64.of_int accepted + got) = accepted + W64.to_uint got.
proof.
  move=> ha hsum; have hg := W64.to_uint_cmp got.
  have hu : W64.to_uint (W64.of_int accepted) = accepted by
    rewrite W64.to_uint_small 1:/#.
  by rewrite W64.to_uintD_small 1:/# hu.
qed.

lemma gib_flag_word flag : (W64.of_int (b2i flag) <> W64.zero) = flag.
proof. case: flag; rewrite /b2i /=; smt(W64.to_uint1 W64.to_uint0). qed.

lemma gib_commit_get before offset requested values j :
  0 <= offset => 0 <= requested <= 512 => offset + requested <= 4096 =>
  0 <= j < 4096 =>
  BArray32768.get64 (gib_commit before offset requested values) j =
    if offset <= j < offset + requested then BArray4096.get64 values (j - offset)
    else BArray32768.get64 before j.
proof.
  move=> ho hn hcap hj; apply W8u8.wordP => k hk.
  rewrite BArray32768.get64d_byte 1:hk /gib_commit BArray32768.initiE 1:/# /=.
  have he : (8 * offset <= 8 * j + k < 8 * (offset + requested)) =
    (offset <= j < offset + requested) by smt().
  rewrite he; case (offset <= j < offset + requested) => hpart /=.
  + rewrite BArray4096.get64d_byte 1:hk; congr; ring.
  by rewrite BArray32768.get64d_byte.
qed.

lemma gib_commit_complete before after offset requested values :
  0 <= offset => 0 <= requested <= 512 => offset + requested <= 4096 =>
  gauss_output_window after offset = values =>
  gauss_big_output_frame before after offset requested =>
  after = gib_commit before offset requested values.
proof.
  move=> ho hn hcap hv hf; apply BArray32768.ext_eq64 => j hj.
  rewrite gib_commit_get 1:ho 1:hn 1:hcap 1:/#.
  case (offset <= j < offset + requested) => hpart.
  + rewrite -hv gauss_output_window_get 1:/#.
    congr; ring.
  have hj' : 0 <= j < 4096 by smt().
  exact (hf j hj' hpart).
qed.

lemma gib_input_trace buf offset pending requested dummy values squares count :
  0 <= size pending <= 8192 => gib_buffer buf offset pending =>
  gauss_trace_result (gauss_input_window buf offset) requested (size pending)
    dummy values squares count =
  gauss_trace_result (BArray8192.of_list pending) requested (size pending)
    dummy values squares count.
proof.
  move=> hs hp; apply gbc_trace_tail_irrelevant; first smt().
  move=> j hj.
  have hd := divz_eq (size pending) 26.
  have hr := modz_cmp (size pending) 26.
  have hj' : 0 <= j < size pending by smt().
  rewrite gauss_input_window_get 1:/# BArray8192.get_of_list 1:/#.
  exact (gib_buffer_get _ _ _ _ hp hj').
qed.

lemma gib_consume_count values squares count pending requested dummy offset :
  0 <= requested <= 512 =>
  W64.to_uint (BArray8.get64
    (gib_consume values squares count pending requested dummy offset).`3 0) =
  min requested (size (gib_accepted pending)).
proof.
  move=> hn; rewrite /gib_consume /= gauss_trace_result_count_exact 1:hn 1:(size_ge0 pending).
  by rewrite /gib_accepted /gauss_accepted_values !size_map size_take 1:/#.
qed.

lemma gib_signs_correct (before : BArray512.t) (buf : BArray8192.t)
    (bytes : W8.t list) (offset : int) :
  hoare [GIBSigner.__sample_gauss_N_copy_signs_at :
    signsp = before /\ bufp = buf /\ signbytes = W64.of_int 32 /\
    signoff = W64.of_int offset /\ 0 <= offset /\ offset + 32 <= 512 /\
    32 <= size bytes /\ gib_buffer buf 0 bytes ==>
    res = gib_signs before offset bytes].
proof.
  conseq (gs_copy_signs_correct (fun j => nth W8.zero bytes j) before buf offset) => //.
  + move=> &m hpre.
    have ho : 0 <= offset < 18446744073709551616 by smt().
    have hu : W64.to_uint (W64.of_int offset) = offset by
      rewrite W64.of_uintK /= modz_small.
    have hp : gib_buffer buf 0 bytes by smt().
    have hsegment : gs_buffer_segment (fun j => nth W8.zero bytes j) buf 0 0 32.
    - rewrite /gs_buffer_segment /= => j hj.
      have h := gib_buffer_get buf 0 bytes j hp _; first smt().
      by move: h; rewrite /=.
    smt().
  move=> &m hpre result hsigns.
  apply BArray512.ext_eq => j hj.
  rewrite /gib_signs BArray512.initiE 1:hj.
  exact (hsigns j hj).
qed.

lemma gib_carry_correct (before : BArray8192.t) (pending : W8.t list) (flag : bool) :
  hoare [GIBSigner._sample_gauss_N_carry :
    bufp = before /\ bytecnt = W64.of_int (size pending) /\
    signbytes = W64.of_int 32 /\ firstflag = W64.of_int (b2i flag) /\
    off = W64.of_int (size pending %% 26) /\
    size pending + (if flag then 32 else 0) <= 8192 /\
    gib_buffer before (if flag then 32 else 0) pending ==>
    gib_buffer res 0 (gib_remainder pending)].
proof.
  conseq (GaussianRefillCorrectness.gauss_carry_correct before (size pending)
    32 (size pending %% 26) flag) => //.
  + move=> &m hpre.
    have hs := size_ge0 pending.
    have hq : 0 <= size pending %/ 26 by rewrite divz_ge0.
    have hd := divz_eq (size pending) 26.
    have hr := modz_cmp (size pending) 26.
    have hf := gib_flag_word flag.
    smt().
  move=> &m hpre result hcarry.
  have hp : gib_buffer before (if flag then 32 else 0) pending by smt().
  have hs := size_ge0 pending.
  have hq : 0 <= size pending %/ 26 by rewrite divz_ge0.
  have hd := divz_eq (size pending) 26.
  have hr := modz_cmp (size pending) 26.
  have [hlen htail] := gib_remainder_size pending.
  rewrite /gib_buffer => j hj.
  have hj' : 0 <= j < size pending %% 26 by smt().
  have hc := hcarry j _; first smt().
  have hb := gib_buffer_get _ _ _ (26 * (size pending %/ 26) + j) hp _; first smt().
  rewrite /gib_remainder nth_drop 1:/# 1:/#.
  smt().
qed.

lemma gib_consume_correct (values : BArray32768.t) (squares : BArray16.t)
    (count : BArray8.t) (buf : BArray8192.t) (pending : W8.t list)
    (requested : int) (dummy : W64.t) (input_offset output_offset : int) :
  hoare [GIBSigner.__sample_gauss_at :
    rp = values /\ sqsump = squares /\ coefcntp = count /\ bufp = buf /\
    counts = gib_counts requested (size pending) /\ dont_write_last = dummy /\
    bufoff = W64.of_int input_offset /\ outoff = W64.of_int output_offset /\
    0 <= requested <= 512 /\ 0 <= input_offset /\
    input_offset + size pending <= 8192 /\
    0 <= output_offset /\ output_offset + requested <= 4096 /\
    gib_buffer buf input_offset pending ==>
    res = gib_consume values squares count pending requested
      (dummy <> W64.zero) output_offset].
proof.
  conseq (GaussianOffsetBridge.sample_gauss_at_trace_correct
    values buf requested (size pending) input_offset output_offset dummy squares count) => //.
  + move=> &m hpre.
    have hs := size_ge0 pending.
    have hn : 0 <= requested <= 512 by smt().
    have hb : 0 <= size pending <= 8192 by smt().
    have hd := gib_counts_decode requested (size pending) hn hb.
    have hi : W64.to_uint (W64.of_int input_offset) = input_offset by
      rewrite W64.of_uintK /= modz_small; smt().
    have ho : W64.to_uint (W64.of_int output_offset) = output_offset by
      rewrite W64.of_uintK /= modz_small; smt().
    smt().
  move=> &m hpre result [htrace hframe].
  have hs : 0 <= size pending <= 8192 by have h := size_ge0 pending; smt().
  have hp : gib_buffer buf input_offset pending by smt().
  have hinput := gib_input_trace buf input_offset pending requested
    (dummy <> W64.zero) (gauss_output_window values output_offset) squares count hs hp.
  move: htrace; rewrite hinput => htrace.
  pose local_result := gauss_trace_result (BArray8192.of_list pending) requested (size pending)
    (dummy <> W64.zero) (gauss_output_window values output_offset) squares count.
  have hw : gauss_output_window result.`1 output_offset = local_result.`1 by smt().
  have hc := gib_commit_complete values result.`1 output_offset requested local_result.`1
    _ _ _ hw hframe; first 3 smt().
  rewrite /gib_consume -/local_result.
  smt().
qed.

lemma gib_signs_total (before : BArray512.t) (buf : BArray8192.t)
    (bytes : W8.t list) (offset : int) :
  phoare [GIBSigner.__sample_gauss_N_copy_signs_at :
    signsp = before /\ bufp = buf /\ signbytes = W64.of_int 32 /\
    signoff = W64.of_int offset /\ 0 <= offset /\ offset + 32 <= 512 /\
    32 <= size bytes /\ gib_buffer buf 0 bytes ==>
    res = gib_signs before offset bytes] = 1%r.
proof.
  by conseq gs_copy_signs_lossless (gib_signs_correct before buf bytes offset).
qed.

lemma gib_carry_total (before : BArray8192.t) (pending : W8.t list) (flag : bool) :
  phoare [GIBSigner._sample_gauss_N_carry :
    bufp = before /\ bytecnt = W64.of_int (size pending) /\
    signbytes = W64.of_int 32 /\ firstflag = W64.of_int (b2i flag) /\
    off = W64.of_int (size pending %% 26) /\
    size pending + (if flag then 32 else 0) <= 8192 /\
    gib_buffer before (if flag then 32 else 0) pending ==>
    gib_buffer res 0 (gib_remainder pending)] = 1%r.
proof.
  by conseq GaussianRefillCorrectness.gauss_carry_lossless
    (gib_carry_correct before pending flag).
qed.

lemma gib_consume_total (values : BArray32768.t) (squares : BArray16.t)
    (count : BArray8.t) (buf : BArray8192.t) (pending : W8.t list)
    (requested : int) (dummy : W64.t) (input_offset output_offset : int) :
  phoare [GIBSigner.__sample_gauss_at :
    rp = values /\ sqsump = squares /\ coefcntp = count /\ bufp = buf /\
    counts = gib_counts requested (size pending) /\ dont_write_last = dummy /\
    bufoff = W64.of_int input_offset /\ outoff = W64.of_int output_offset /\
    0 <= requested <= 512 /\ 0 <= input_offset /\
    input_offset + size pending <= 8192 /\
    0 <= output_offset /\ output_offset + requested <= 4096 /\
    gib_buffer buf input_offset pending ==>
    res = gib_consume values squares count pending requested
      (dummy <> W64.zero) output_offset] = 1%r.
proof.
  conseq (gr_consumer_lossless
    values buf requested (size pending) input_offset output_offset)
    (gib_consume_correct values squares count buf pending requested dummy input_offset output_offset)
    => //.
  move=> &m hpre.
  have hs := size_ge0 pending.
  have hn : 0 <= requested <= 512 by smt().
  have hb : 0 <= size pending <= 8192 by smt().
  have hd := gib_counts_decode requested (size pending) hn hb.
  have hi : W64.to_uint (W64.of_int input_offset) = input_offset by
    rewrite W64.of_uintK /= modz_small; smt().
  have ho : W64.to_uint (W64.of_int output_offset) = output_offset by
    rewrite W64.of_uintK /= modz_small; smt().
  smt().
qed.

(* Coupling the same finite block draws suffices.  Termination is transferred
   separately from the iid functional controller; no adequate-prefix witness
   or randomness hypothesis about SHAKE occurs in this equivalence. *)
lemma gib_actual_functional :
  equiv [GaussianIidBuffer.sample ~ GaussianIidBufferFunctional.sample :
    ={rp, signsp, sqsump, n, sample_offset, sign_offset} /\
    gib_bounds n{1} sample_offset{1} sign_offset{1} ==> ={res}].
proof.
  proc.
  seq 4 4 :
    (={rp, signsp, sqsump, count, n, sample_offset, sign_offset} /\
     gib_bounds n{1} sample_offset{1} sign_offset{1} /\
     size pending{2} = 6664 /\ gib_buffer buf{1} 0 pending{2}).
  + while
      (={rp, signsp, sqsump, count, n, sample_offset, sign_offset, block} /\
       gib_bounds n{1} sample_offset{1} sign_offset{1} /\
       0 <= block{1} <= 49 /\ size pending{2} = 136 * block{1} /\
       gib_buffer buf{1} 0 pending{2}).
    - wp; rnd; auto => />.
      smt(gib_block_size gib_buffer_fill_append size_cat).
    auto => />; smt(gib_buffer_empty).
  while
    (={rp, signsp, sqsump, count, n, sample_offset, sign_offset, accepted} /\
     gib_bounds n{1} sample_offset{1} sign_offset{1} /\
     0 <= accepted{1} <= n{1} /\
     available{1} = size pending{2} /\ 0 <= available{1} <= 6664 /\
     available{1} + (if has_prefix{1} then 32 else 0) <= 8192 /\
     gib_buffer buf{1} (if has_prefix{1} then 32 else 0) pending{2}).
  + wp; ecall{1} (gib_consume_total rp{1} sqsump{1} count{1} buf{1}
      (pending{2} ++ bytes{2}) (n{1} - accepted{1})
      (W64.of_int (n{1} - 256)) 0 (sample_offset{1} + accepted{1})).
    wp; rnd; wp.
    ecall{1} (gib_carry_total buf{1} pending{2} has_prefix{1}).
    auto => />.
    move=> &1 &2 hn ho0 hoend hso0 hsoend hc0 hcn hb0 hbcap hwindow hp hlt
      carried hcarry bytesL hsupport.
    have hbytes := gib_block_size bytesL hsupport.
    have [hrem hrange] := gib_remainder_size pending{2}.
    have hsize : size (gib_remainder pending{2} ++ bytesL) = size pending{2} %% 26 + 136 by
      rewrite size_cat hbytes hrem.
    have hzero : 0 <= 0 by done.
    have hcapacity : 0 + size (gib_remainder pending{2}) + 136 <= 8192 by smt().
    have hfilled := gib_buffer_fill_append carried 0 (gib_remainder pending{2}) bytesL
      hzero hcapacity hbytes hcarry.
    move: hfilled; rewrite /= hrem => hfilled.
    have hnrem : 0 <= n{2} - accepted{2} <= 512 by smt().
    have hcount := gib_consume_count rp{2} sqsump{2} count{2}
      (gib_remainder pending{2} ++ bytesL) (n{2} - accepted{2})
      (n{2} = 257) (sample_offset{2} + accepted{2}) hnrem.
    have hnonneg := size_ge0 (gib_accepted (gib_remainder pending{2} ++ bytesL)).
    have hdummy := gs_dummy_word n{2} hn.
    rewrite hdummy hcount /min.
    smt().
  wp; ecall{1} (gib_consume_total rp{1} sqsump{1} count{1} buf{1}
    (drop 32 pending{2}) n{1} (W64.of_int (n{1} - 256)) 32 sample_offset{1}).
  wp; ecall{1} (gib_signs_total signsp{1} buf{1} pending{2} sign_offset{1}).
  auto => />.
  move=> &1 &2 hn ho0 hoend hso0 hsoend hbytes hp.
  have hsize : size (drop 32 pending{2}) = 6632 by
    rewrite size_drop 1:// hbytes /=.
  have hskip : 0 <= 32 <= size pending{2} by smt().
  have hdrop := gib_buffer_drop buf{1} 0 pending{2} 32 hskip hp.
  move: hdrop; rewrite /= => hdrop.
  have hn512 : 0 <= n{2} <= 512 by smt().
  have hcount := gib_consume_count rp{2} sqsump{2} count{2} (drop 32 pending{2})
    n{2} (n{2} = 257) sample_offset{2} hn512.
  have hnonneg := size_ge0 (gib_accepted (drop 32 pending{2})).
  have hdummy := gs_dummy_word n{2} hn.
  rewrite hdummy hcount /min.
  smt().
qed.
