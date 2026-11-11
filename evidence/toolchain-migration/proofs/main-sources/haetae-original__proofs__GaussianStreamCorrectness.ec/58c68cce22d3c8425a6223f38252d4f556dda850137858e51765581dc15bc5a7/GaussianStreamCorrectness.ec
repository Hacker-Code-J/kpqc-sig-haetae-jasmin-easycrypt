require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import ApiTarget GaussianConsumerSpec GaussianConsumerCorrectness
  GaussianOffsetBridge GaussianRefillCorrectness SHAKEBlockSpec SHAKEBlockCorrectness
  GaussianStreamSpec GaussianStreamBuffer GaussianStreamSequence GaussianStreamAccumulator
  GaussianStreamComposition GaussianWindowSpec SHAKEStreamSpec SHAKESeedInitCorrectness.
import SLH64.
import SHAKEStreamSpec SHAKEBlockSpec.Word.

module StreamSigner = GaussianOffsetBridge.Signer.

lemma gs_mode_arithmetic (n : int) :
  n = 256 \/ n = 257 =>
  0 < n <= 512 /\ n %/ 8 = 32 /\ 0 <= n - 256 <= 1 /\ n %% 256 = n - 256.
proof. by case=> ->. qed.

lemma gs_signbytes_word (n : int) :
  n = 256 \/ n = 257 =>
  W64.of_int n `>>>` 3 = W64.of_int 32.
proof. by case=> ->; rewrite W64.shrDP. qed.

lemma gs_word32_shift_roundtrip (n : int) :
  0 <= n < 4294967296 =>
  (W64.of_int n `<<<` 32) `>>>` 32 = W64.of_int n.
proof.
  move=> hn; apply W64.to_uint_eq.
  rewrite W64.to_uint_shr 1:// W64.to_uint_shl 1:// !W64.of_uintK /=.
  have hn64 : n %% 18446744073709551616 = n by apply modz_small; smt().
  rewrite hn64.
  rewrite modz_small 1:/# mulzK //.
qed.

lemma gs_pack_counts_word (n b : int) :
  0 <= n < 4294967296 =>
  ((W64.of_int b `<<<` 32) `|` W64.of_int n) =
    W64.of_int (b * 4294967296 + n).
proof.
  move=> hn.
  have hd : (W64.of_int b `<<<` 32) `&` W64.of_int n = W64.zero.
  + rewrite W64.andwC -(gs_word32_shift_roundtrip n hn).
    apply W64.shrw_shlw_disjoint; trivial.
  rewrite (W64.orw_disjoint _ _ hd) W64.shlMP 1:// /=.
  trivial.
qed.

lemma gs_pack_counts_decode (n b : int) :
  0 <= n <= 512 => 0 <= b <= 8192 =>
  gauss_requested ((W64.of_int b `<<<` 32) `|` W64.of_int n) = n /\
  gauss_available ((W64.of_int b `<<<` 32) `|` W64.of_int n) = b.
proof.
  move=> hn hb; rewrite gs_pack_counts_word 1:/#.
  exact (gauss_counts_encode n b hn hb).
qed.

lemma gs_refill_counts_decode (n : int) (count tail : W64.t) :
  0 <= W64.to_uint count <= n => n <= 512 => 0 <= W64.to_uint tail < 26 =>
  gauss_requested (((W64.of_int 136 + tail) `<<` W8.of_int 32) `|`
    (W64.of_int n - count)) = n - W64.to_uint count /\
  gauss_available (((W64.of_int 136 + tail) `<<` W8.of_int 32) `|`
    (W64.of_int n - count)) = 136 + W64.to_uint tail.
proof.
  move=> hc hn ht.
  have hb : W64.of_int 136 + tail = W64.of_int (136 + W64.to_uint tail) by
    rewrite W64.of_intD W64.to_uintK.
  have hr : W64.of_int n - count = W64.of_int (n - W64.to_uint count) by
    rewrite W64.of_intS W64.to_uintK.
  rewrite hb hr /(`<<`) W8.of_uintK /=.
  apply gs_pack_counts_decode; smt().
qed.

lemma gs_mod26_sub (x : int) : (x - 26) %% 26 = x %% 26.
proof.
  have -> : x - 26 = (-1) * 26 + x by ring.
  by rewrite modzMDl.
qed.

lemma gs_mod26_word_step (x : W64.t) :
  26 <= W64.to_uint x =>
  W64.to_uint (x - W64.of_int 26) = W64.to_uint x - 26 /\
  W64.to_uint (x - W64.of_int 26) %% 26 = W64.to_uint x %% 26.
proof. move=> hx; rewrite (gauss_bytes_subtract x hx) gs_mod26_sub; trivial. qed.

lemma gs_mod26_word_done (b : int) (x : W64.t) :
  W64.to_uint x %% 26 = b %% 26 => !(W64.of_int 26 \ule x) =>
  x = W64.of_int (b %% 26).
proof.
  move=> hm hdone.
  have hx0 := W64.to_uint_cmp x.
  have hx : W64.to_uint x < 26 by
    move: hdone; rewrite W64.uleE (W64.of_uintK 26) /=; smt().
  have heq : W64.to_uint x = b %% 26 by
    move: hm; rewrite modz_small 1:/#.
  by rewrite -heq W64.to_uintK.
qed.

lemma gs_total_advance (n c q : int) :
  n = 256 \/ n = 257 => 0 <= c <= n => 0 <= q <= n - c =>
  W64.of_int c + W64.of_int q = W64.of_int (c + q) /\
  W64.to_uint (W64.of_int c + W64.of_int q) = c + q /\ 0 <= c + q <= n.
proof.
  move=> hn hc hq; rewrite -W64.of_intD W64.of_uintK /=.
  rewrite modz_small 1:/#; smt().
qed.

lemma gs_remaining_word (n c : int) :
  W64.of_int n - W64.of_int c = W64.of_int (n - c).
proof. by rewrite -W64.of_intS. qed.

lemma gs_initial_offset_uint (block : W64.t) :
  W64.to_uint block <= 49 =>
  W64.to_uint (W64.of_int (136 * W64.to_uint block)) = 136 * W64.to_uint block.
proof.
  move=> hb; have h0 := W64.to_uint_cmp block.
  rewrite W64.of_uintK /=; apply modz_small; smt().
qed.

lemma gs_initial_offset_next (b : int) :
  W64.of_int (136 * b) + W64.of_int 136 = W64.of_int (136 * (b + 1)).
proof. by rewrite -W64.of_intD; congr; ring. qed.

lemma gs_dummy_step (n : int) (d : W64.t) :
  n = 256 \/ n = 257 =>
  (d = W64.of_int n \/ d = W64.of_int (n - 256)) =>
  W64.of_int 256 \ule d => d - W64.of_int 256 = W64.of_int (n - 256).
proof.
  by case=> ->; case=> ->; rewrite /=.
qed.

lemma gs_dummy_done (n : int) (d : W64.t) :
  n = 256 \/ n = 257 =>
  (d = W64.of_int n \/ d = W64.of_int (n - 256)) =>
  !(W64.of_int 256 \ule d) => d = W64.of_int (n - 256).
proof.
  by case=> ->; case=> ->; rewrite /=.
qed.

lemma gs_initial_candidates stream buf :
  gs_buffer_segment stream buf 0 0 6664 =>
  gs_buffer_segment (fun j => stream (32 + j)) buf 32 0 6632.
proof.
  rewrite /gs_buffer_segment => h j hj.
  have he := h (32 + j) _; first smt().
  by move: he; rewrite /=.
qed.

lemma gs_refill_candidates stream buf blocks :
  gs_buffer_segment stream buf 0 (136 * blocks - gs_stream_tail blocks)
    (136 + gs_stream_tail blocks) =>
  gs_buffer_segment (fun j => stream (32 + j)) buf 0
    (26 * gs_stream_attempts blocks) (136 + gs_stream_tail blocks).
proof.
  rewrite /gs_buffer_segment => h j hj.
  have he := h j hj.
  have hp := gs_stream_position blocks.
  have -> : 32 + (26 * gs_stream_attempts blocks + j) =
    136 * blocks - gs_stream_tail blocks + j by smt().
  exact he.
qed.

lemma gs_live_count_bounds f initial current initial_squares squares n oo attempts accepted :
  gs_progress f initial current initial_squares squares n oo attempts accepted =>
  0 <= accepted <= n.
proof. move=> [_ [_ [hc _]]]; exact hc. qed.

(* The final statement is deliberately Hoare partial correctness: no claim
   that every fixed seed eventually supplies the required accepted events. *)
lemma sample_gauss_N_full_at_correct
    (seed0 : BArray64.t) (nonce0 : W64.t) (n sample_offset sign_offset : int)
    (initial : BArray32768.t) (initial_signs : BArray512.t)
    (initial_squares : BArray16.t) :
  hoare [StreamSigner._sf_sample_gauss_N_full_at :
    seedp = seed0 /\ nonce = nonce0 /\ len = W64.of_int n /\
    W64.to_uint sampleoff = sample_offset /\ W64.to_uint signoff = sign_offset /\
    rp = initial /\ signsp = initial_signs /\ sqsump = initial_squares /\
    (n = 256 \/ n = 257) /\ 0 <= sample_offset /\ sample_offset + n <= 4096 /\
    0 <= sign_offset /\ sign_offset + 32 <= 512 /\
    W64.to_uint (BArray16.get64 initial_squares 0) < 281474976710656 /\
    W64.to_uint (BArray16.get64 initial_squares 1) < 281474976710656
    ==>
    gs_stream_result (shake_stream_byte (shake_initial_words seed0 nonce0))
      initial res.`1 initial_signs res.`2 initial_squares res.`3
      n sample_offset sign_offset].
proof.
  proc.
  seq 13 :
    (len = W64.of_int n /\ W64.to_uint sampleoff = sample_offset /\
     W64.to_uint signoff = sign_offset /\ rp = initial /\
     signsp = initial_signs /\ sqsump = initial_squares /\
     (n = 256 \/ n = 257) /\ 0 <= sample_offset /\ sample_offset + n <= 4096 /\
     0 <= sign_offset /\ sign_offset + 32 <= 512 /\
     W64.to_uint (BArray16.get64 initial_squares 0) < 281474976710656 /\
     W64.to_uint (BArray16.get64 initial_squares 1) < 281474976710656 /\
     gs_buffer_segment (shake_stream_byte (shake_initial_words seed0 nonce0))
       bufp 0 0 6664 /\
     word_state_of_barray sp_0 = shake_iterate (shake_initial_words seed0 nonce0) 49).
  + while (#pre /\ 0 <= W64.to_uint block <= 49 /\
      off = W64.of_int (136 * W64.to_uint block) /\
      word_state_of_barray sp_0 =
        shake_iterate (shake_initial_words seed0 nonce0) (W64.to_uint block) /\
      gs_buffer_segment (shake_stream_byte (shake_initial_words seed0 nonce0))
        bufp 0 0 (136 * W64.to_uint block)).
    - wp; ecall (SHAKESeedInitCorrectness.shake_block_stream_correct
        (shake_initial_words seed0 nonce0) (W64.to_uint block) bufp off sp_0).
      auto => />.
      move=> &hr hn hso0 hso hsign0 hsign hlo hhi hb0 hb49 hstate hbuf hguard.
      move: hguard; rewrite W64.ultE (W64.of_uintK 49) /= => hguard.
      rewrite (gs_initial_offset_uint block{hr} hb49).
      split; first smt().
      move=> hoff0 hoff result hbytes hframe hnewstate.
      rewrite /protect_64 /protect_ptr W64.to_uintD_small 1:/# W64.to_uint1
        gs_initial_offset_next.
      have hb : 0 <= W64.to_uint block{hr} < 49 by smt().
      have hnew := gs_initial_block_extend
        (shake_stream_byte (shake_initial_words seed0 nonce0))
        bufp{hr} result.`1 (W64.to_uint block{hr}) hb hbuf hbytes hframe.
      smt().
    wp; call (SHAKESeedInitCorrectness.seed_init_words_correct seed0 nonce0).
    auto => />.
    move=> &hr hn hso0 hso hsign0 hsign hlo hhi result hstate.
    split.
    - rewrite shake_iterate0.
      split; first exact hstate.
      apply gs_buffer_empty.
    move=> block0 bufp0 sampleoff0 signoff0 sp00 hdone hsample hsignoff hb0 hb49 hsp hbuf.
    move: hdone; rewrite W64.ultE (W64.of_uintK 49) /= => hdone.
    have hb : W64.to_uint block0 = 49 by smt().
    smt().
  seq 10 :
    (len = W64.of_int n /\ W64.to_uint sampleoff = sample_offset /\
     W64.to_uint signoff = sign_offset /\ rp = initial /\ sqsump = initial_squares /\
     (n = 256 \/ n = 257) /\ 0 <= sample_offset /\ sample_offset + n <= 4096 /\
     0 <= sign_offset /\ sign_offset + 32 <= 512 /\
     W64.to_uint (BArray16.get64 initial_squares 0) < 281474976710656 /\
     W64.to_uint (BArray16.get64 initial_squares 1) < 281474976710656 /\
     gs_buffer_segment (shake_stream_byte (shake_initial_words seed0 nonce0))
       bufp 0 0 6664 /\
     word_state_of_barray sp_0 = shake_iterate (shake_initial_words seed0 nonce0) 49 /\
     gs_signs_result (shake_stream_byte (shake_initial_words seed0 nonce0))
       initial_signs signsp sign_offset /\
     signbytes = W64.of_int 32 /\ bytecnt = W64.of_int 6632 /\
     gauss_requested counts = n /\ gauss_available counts = 6632 /\
     dont = W64.of_int (n - 256)).
  + while ((n = 256 \/ n = 257) /\
      (dont = W64.of_int n \/ dont = W64.of_int (n - 256))).
    - auto => />; smt(gs_dummy_step).
    wp; ecall (gs_copy_signs_correct
      (shake_stream_byte (shake_initial_words seed0 nonce0))
      initial_signs bufp sign_offset).
    auto => />.
    move=> &hr hn hso0 hso hsign0 hsign hlo hhi hbuf hstate.
    have hsignbytes := gs_signbytes_word n hn.
    have hprefix : gs_buffer_segment
      (shake_stream_byte (shake_initial_words seed0 nonce0)) bufp{hr} 0 0 32.
    - rewrite /gs_buffer_segment => j hj; apply hbuf; smt().
    have hn512 : 0 <= n <= 512 by smt().
    have hb6632 : 0 <= 6632 <= 8192 by done.
    have hdecode := gs_pack_counts_decode n 6632 hn512 hb6632.
    rewrite /(`>>`) /(`<<`) !W8.of_uintK /= hsignbytes /=.
    move: hdecode; rewrite /= => hdecode.
    smt(gs_dummy_done).
  while (exists blocks,
    49 <= blocks /\ len = W64.of_int n /\
    W64.to_uint sampleoff = sample_offset /\ W64.to_uint signoff = sign_offset /\
    signbytes = W64.of_int 32 /\ dont = W64.of_int (n - 256) /\
    (n = 256 \/ n = 257) /\ 0 <= sample_offset /\ sample_offset + n <= 4096 /\
    0 <= sign_offset /\ sign_offset + 32 <= 512 /\
    gs_signs_result (shake_stream_byte (shake_initial_words seed0 nonce0))
      initial_signs signsp sign_offset /\
    word_state_of_barray sp_0 = shake_iterate (shake_initial_words seed0 nonce0) blocks /\
    gs_tail_matches (shake_stream_byte (shake_initial_words seed0 nonce0))
      bufp (W64.to_uint bytecnt) (firstflag <> W64.zero) blocks /\
    gs_progress (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j))
      initial rp initial_squares sqsump n sample_offset (gs_stream_attempts blocks)
      (W64.to_uint total)).
  + elim * => blocks.
    wp; ecall (gs_progress_consume_correct
      (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j))
      initial rp initial_squares sqsump n sample_offset (gs_stream_attempts blocks)
      (W64.to_uint total) bufp (136 + gs_stream_tail blocks) 0 coefcntp).
    wp; ecall (SHAKESeedInitCorrectness.shake_block_stream_correct
      (shake_initial_words seed0 nonce0) blocks bufp (W64.of_int (gs_stream_tail blocks)) sp_0).
    ecall (GaussianRefillCorrectness.gauss_carry_correct bufp (W64.to_uint bytecnt)
      32 (gs_stream_tail blocks) (firstflag <> W64.zero)).
    while (0 <= W64.to_uint off <= W64.to_uint bytecnt /\
      W64.to_uint off %% 26 = W64.to_uint bytecnt %% 26).
    - auto => />.
      move=> &hr ho0 hob hm hguard.
      move: hguard; rewrite W64.uleE (W64.of_uintK 26) /= => hguard.
      have [hsub hrem] := gs_mod26_word_step off{hr} hguard.
      smt().
    auto => /=.
    move=> &hr [hinv hguard].
    have [hblocks [hlen [hsample [hsignoff [hsignbytes [hdont [hn
      [hso0 [hsoend [hsg0 [hsgend [hsigns [hstate [htail hprogress]]]]]]]]]]]]]] := hinv.
    have [hbounds [hcap [hmod [htbounds htle]]]] := gs_tail_carry_bounds
      (shake_stream_byte (shake_initial_words seed0 nonce0)) bufp{hr}
      (W64.to_uint bytecnt{hr}) (firstflag{hr} <> W64.zero) blocks htail.
    have hc := gs_live_count_bounds _ _ _ _ _ _ _ _ _ hprogress.
    have hn512 : n <= 512 by smt().
    have hnword : W64.to_uint (W64.of_int n) = n by
      rewrite W64.of_uintK /=; apply modz_small; smt().
    have hlt : W64.to_uint total{hr} < n by
      move: hguard; rewrite hlen W64.ultE hnword.
    have htword : W64.to_uint (W64.of_int (gs_stream_tail blocks)) =
      gs_stream_tail blocks by rewrite W64.of_uintK /=; apply modz_small; smt().
    rewrite /protect_64 /protect_ptr hlen hsignbytes hdont.
    split; first smt().
    move=> off0 hdone [hoRange hoMod].
    have hoff := gs_mod26_word_done (W64.to_uint bytecnt{hr}) off0 hoMod hdone.
    move: hoff; rewrite hmod => hoff.
    have hoffu : W64.to_uint off0 = gs_stream_tail blocks by rewrite hoff htword.
    split; first smt().
    move=> _ carried hcarry.
    split; first smt().
    move=> _ squeezed [hbytes [hframe hnewstate]].
    have hbytes' : forall j, 0 <= j < 136 =>
      BArray8192.get8 squeezed.`1 (gs_stream_tail blocks + j) =
      shake_stream_byte (shake_initial_words seed0 nonce0) (136 * blocks + j) by
      move=> j hj; have := hbytes j hj; rewrite htword.
    have hframe' : SHAKEBlockSpec.rate_block_frame carried squeezed.`1
      (gs_stream_tail blocks) 136 by move: hframe; rewrite htword.
    have [hcandidates htailnext] := gs_refill_buffer_ready
      (shake_stream_byte (shake_initial_words seed0 nonce0))
      bufp{hr} carried squeezed.`1 (W64.to_uint bytecnt{hr})
      (firstflag{hr} <> W64.zero) blocks hblocks htail hcarry hbytes' hframe'.
    have hoffbounds : 0 <= W64.to_uint off0 < 26 by smt().
    have hdecode := gs_refill_counts_decode n total{hr} off0 hc hn512 hoffbounds.
    move: hdecode; rewrite hoffu => hdecode.
    have hsbound : 0 <= W64.to_uint sampleoff{hr} <= 4096 by smt().
    have hcbound : 0 <= W64.to_uint total{hr} <= 512 by smt().
    have hindex := gauss_window_output_uint sampleoff{hr} total{hr} hsbound hcbound.
    move: hindex; rewrite hsample => hindex.
    split; first smt().
    move=> _ consumed hnextprogress.
    have hncount := gs_live_count_bounds _ _ _ _ _ _ _ _ _ hnextprogress.
    have htotal : W64.to_uint (total{hr} + BArray8.get64 consumed.`3 0) =
      W64.to_uint total{hr} + W64.to_uint (BArray8.get64 consumed.`3 0) by
      rewrite W64.to_uintD_small 1:/#.
    have hbytesnext : W64.to_uint (W64.of_int 136 + off0) =
      136 + gs_stream_tail blocks by
      rewrite W64.to_uintD (W64.of_uintK 136) /= hoffu modz_small 1:/#.
    have [hadvance _] := gs_stream_advance blocks.
    have hnextprogress' : gs_progress
      (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j))
      initial consumed.`1 initial_squares consumed.`2 n sample_offset
      (gs_stream_attempts (blocks + 1))
      (W64.to_uint total{hr} + W64.to_uint (BArray8.get64 consumed.`3 0)) by
      move: hnextprogress; rewrite -hadvance.
    exists (blocks + 1).
    rewrite hbytesnext htotal.
    smt().
  wp; ecall (gs_progress_consume_correct
    (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j))
    initial rp initial_squares sqsump n sample_offset 0 0 bufp 6632 32 coefcntp).
  auto => /=.
  move=> &hr hsetup.
  have [hlen [hsample [hsignoff [hrp [hsq [hn [hso0 [hsoend [hsg0 [hsgend
    [hlo [hhi [hbuf [hstate [hsigns [hsignbytes [hbytecnt [hrequested
    [havailable hdont]]]]]]]]]]]]]]]]]]] := hsetup.
  have hhi_le : W64.to_uint (BArray16.get64 initial_squares 1) <= 281474976710656 by smt().
  have hprogress0 := gs_progress_initial
    (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j))
    initial initial_squares n sample_offset hn hlo hhi_le.
  have hcandidates := gs_initial_candidates
    (shake_stream_byte (shake_initial_words seed0 nonce0)) bufp{hr} hbuf.
  have hsignu : W64.to_uint signbytes{hr} = 32 by
    rewrite hsignbytes W64.of_uintK /=.
  rewrite /protect_64 /protect_ptr.
  split; first smt().
  move=> _ result hprogress255.
  split.
  + exists 49.
    have htail0 := gs_initial_tail
      (shake_stream_byte (shake_initial_words seed0 nonce0)) bufp{hr} hbuf.
    have hbyteu : W64.to_uint bytecnt{hr} = 6632 by rewrite hbytecnt W64.of_uintK /=.
    have hfirst : W64.one <> W64.zero by
      rewrite W64.to_uint_eq W64.to_uint1 W64.to_uint0.
    have hattempts : gs_stream_attempts 49 = 255 by rewrite /gs_stream_attempts.
    smt().
  move=> bufp0 bytecnt0 dont0 firstflag0 len0 rp0 sampleoff0 signbytes0 signoff0
    signsp0 sp00 sqsump0 total0 hdone [blocks hinv].
  have [hblocks [hlen0 [hsample0 [hsignoff0 [hsignbytes0 [hdont0 [hn0
    [hsoL [hsoE [hsgL [hsgE [hsigns0 [hstate0 [htail0 hprogress]]]]]]]]]]]]]] := hinv.
  have hnword : W64.to_uint (W64.of_int n) = n by
    rewrite W64.of_uintK /=; apply modz_small; smt().
  have hge : n <= W64.to_uint total0 by
    move: hdone; rewrite hlen0 W64.ultE hnword; smt().
  exact (gs_stream_result_finish
    (shake_stream_byte (shake_initial_words seed0 nonce0)) initial rp0
    initial_signs signsp0 initial_squares sqsump0 n sample_offset sign_offset
    blocks (W64.to_uint total0) hblocks hsigns0 hprogress hge).
qed.
