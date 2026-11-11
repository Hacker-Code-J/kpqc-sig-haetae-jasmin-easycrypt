require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import GaussianRetryStreamBridge GaussianRetryRank GaussianRetryConsumerTotal GaussianRetryBufferTotal
  GaussianStreamSpec GaussianStreamBuffer GaussianStreamSequence GaussianStreamAccumulator
  GaussianStreamComposition GaussianStreamCorrectness GaussianOffsetBridge GaussianRefillCorrectness
  GaussianWindowSpec GaussianConsumerSpec SHAKEBlockSpec SHAKEStreamSpec SHAKESeedInitCorrectness.
import SLH64 SHAKEStreamSpec SHAKEBlockSpec.Word.

type grt_state = BArray32768.t * BArray16.t * BArray8192.t * BArray200.t * int * bool * int.

(* Compatibility need not identify a unique block count. The rank uses the
   maximum compatible count below the adequate-prefix cap, not a ghost
   counter inserted into the production program. *)
op [opaque] grt_compatible (initial_words : word_state)
    (initial : BArray32768.t) (initial_squares : BArray16.t) (n oo : int)
    (state : grt_state) (blocks : int) : bool =
  word_state_of_barray state.`4 = shake_iterate initial_words blocks /\
  gs_tail_matches (shake_stream_byte initial_words) state.`3 state.`5 state.`6 blocks /\
  gs_progress (fun j => shake_stream_byte initial_words (32 + j))
    initial state.`1 initial_squares state.`2 n oo (gs_stream_attempts blocks) state.`7.

lemma grt_compatible_parts initial_words initial initial_squares n oo state blocks :
  grt_compatible initial_words initial initial_squares n oo state blocks =>
  word_state_of_barray state.`4 = shake_iterate initial_words blocks /\
  gs_tail_matches (shake_stream_byte initial_words) state.`3 state.`5 state.`6 blocks /\
  gs_progress (fun j => shake_stream_byte initial_words (32 + j))
    initial state.`1 initial_squares state.`2 n oo (gs_stream_attempts blocks) state.`7.
proof. by rewrite /grt_compatible. qed.

lemma grt_compatible_below_cap initial_words initial initial_squares n oo state attempts blocks :
  gr_adequate (fun j => shake_stream_byte initial_words (32 + j)) n attempts =>
  grt_compatible initial_words initial initial_squares n oo state blocks =>
  state.`7 < n => blocks < gr_block_cap attempts.
proof.
  move=> had hcompat hguard.
  have hp : gs_progress (fun j => shake_stream_byte initial_words (32 + j))
    initial state.`1 initial_squares state.`2 n oo (gs_stream_attempts blocks) state.`7.
  + move: hcompat; rewrite /grt_compatible; smt().
  exact (gr_progress_below_cap _ _ _ _ _ _ _ _ _ _ had hp hguard).
qed.

lemma grt_rank_positive initial_words initial initial_squares n oo state attempts :
  gr_adequate (fun j => shake_stream_byte initial_words (32 + j)) n attempts =>
  (exists b, 49 <= b <= gr_block_cap attempts /\
    grt_compatible initial_words initial initial_squares n oo state b) =>
  state.`7 < n =>
  0 < grr_rank (grt_compatible initial_words initial initial_squares n oo state)
    (gr_block_cap attempts).
proof.
  move=> had hsome hguard.
  have [hb hp] := grr_index_witness
    (grt_compatible initial_words initial initial_squares n oo state)
    (gr_block_cap attempts) hsome.
  have hlt := grt_compatible_below_cap _ _ _ _ _ _ _ _ had hp hguard.
  rewrite /grr_rank; smt().
qed.

lemma grt_dont_decrease (d : W64.t) : W64.of_int 256 \ule d =>
  W64.to_uint (d - W64.of_int 256) < W64.to_uint d.
proof. move=> hd; rewrite W64.to_uintB 1:// W64.of_uintK /=; smt(). qed.

lemma grt_seed_words_total (seed0 : BArray64.t) (nonce0 : W64.t) :
  phoare [SHAKESeedInitCorrectness.Signer._sf_shake256_init_seed64 :
    seedp = seed0 /\ nonce = nonce0 ==>
    word_state_of_barray res = shake_initial_words seed0 nonce0] = 1%r.
proof.
  by conseq SHAKESeedInitCorrectness.seed_init_ll
    (SHAKESeedInitCorrectness.seed_init_words_correct seed0 nonce0).
qed.

lemma grt_copy_signs_total stream before offset :
  phoare [GS_Signer.__sample_gauss_N_copy_signs_at :
    signsp = before /\ signbytes = W64.of_int 32 /\
    W64.to_uint signoff = offset /\ 0 <= offset /\ offset + 32 <= 512 /\
    gs_buffer_segment stream bufp 0 0 32 ==>
    gs_signs_result stream before res offset] = 1%r.
proof.
  exists* bufp; elim* => buf0.
  by conseq (gs_copy_signs_total stream before buf0 offset) => //.
qed.

lemma gr_sample_gauss_N_adequate_lossless
    (seed0 : BArray64.t) (nonce0 : W64.t) (n sample_offset sign_offset attempts : int)
    (initial : BArray32768.t) (initial_signs : BArray512.t) (initial_squares : BArray16.t) :
  phoare [StreamSigner._sf_sample_gauss_N_full_at :
    seedp = seed0 /\ nonce = nonce0 /\ len = W64.of_int n /\
    W64.to_uint sampleoff = sample_offset /\ W64.to_uint signoff = sign_offset /\
    rp = initial /\ signsp = initial_signs /\ sqsump = initial_squares /\
    (n = 256 \/ n = 257) /\ 0 <= sample_offset /\ sample_offset + n <= 4096 /\
    0 <= sign_offset /\ sign_offset + 32 <= 512 /\
    W64.to_uint (BArray16.get64 initial_squares 0) < 281474976710656 /\
    W64.to_uint (BArray16.get64 initial_squares 1) < 281474976710656 /\
    gr_adequate (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j)) n attempts
    ==> true] = 1%r.
proof.
  conseq (_ : _ ==> _ : >= 1%r) => //.
  proc.
  seq 13 :
    (len = W64.of_int n /\ W64.to_uint sampleoff = sample_offset /\
     W64.to_uint signoff = sign_offset /\ rp = initial /\
     signsp = initial_signs /\ sqsump = initial_squares /\
     (n = 256 \/ n = 257) /\ 0 <= sample_offset /\ sample_offset + n <= 4096 /\
     0 <= sign_offset /\ sign_offset + 32 <= 512 /\
     W64.to_uint (BArray16.get64 initial_squares 0) < 281474976710656 /\
     W64.to_uint (BArray16.get64 initial_squares 1) < 281474976710656 /\
     gr_adequate (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j)) n attempts /\
     gs_buffer_segment (shake_stream_byte (shake_initial_words seed0 nonce0))
       bufp 0 0 6664 /\
     word_state_of_barray sp_0 = shake_iterate (shake_initial_words seed0 nonce0) 49) => //.
  + while (#pre /\ 0 <= W64.to_uint block <= 49 /\
      off = W64.of_int (136 * W64.to_uint block) /\
      word_state_of_barray sp_0 =
        shake_iterate (shake_initial_words seed0 nonce0) (W64.to_uint block) /\
      gs_buffer_segment (shake_stream_byte (shake_initial_words seed0 nonce0))
        bufp 0 0 (136 * W64.to_uint block)) (49 - W64.to_uint block).
    - move=> z; exists* block; elim* => block0.
      wp; call (gr_initial_squeeze_total
        (shake_initial_words seed0 nonce0) (W64.to_uint block0)).
      auto => />.
      move=> &hr hn hso0 hso hsign0 hsign hlo hhi had hb0 hb49 hstate hbuf hguard.
      move: hguard; rewrite W64.ultE (W64.of_uintK 49) /= => hguard.
      rewrite (gs_initial_offset_uint block0 hb49).
      split; first smt().
      move=> result hnewstate hnewbuf.
      rewrite /protect_64 /protect_ptr W64.to_uintD_small 1:/# W64.to_uint1
        gs_initial_offset_next.
      smt().
    conseq (_ : _ ==> _ : = 1%r) => //.
    wp; call (grt_seed_words_total seed0 nonce0).
    auto => />.
    move=> &hr hn hso0 hso hsign0 hsign hlo hhi had result hstate.
    split.
    - rewrite shake_iterate0.
      split; first exact hstate.
      apply gs_buffer_empty.
    move=> block0 bufp0 sampleoff0 signoff0 sp00.
    rewrite W64.ultE (W64.of_uintK 49) /=.
    split; first smt().
    move=> hdone hsample hsignoff hb0 hb49 hsp hbuf.
    have hb : W64.to_uint block0 = 49 by smt().
    smt().
  seq 10 :
    (len = W64.of_int n /\ W64.to_uint sampleoff = sample_offset /\
     W64.to_uint signoff = sign_offset /\ rp = initial /\ sqsump = initial_squares /\
     (n = 256 \/ n = 257) /\ 0 <= sample_offset /\ sample_offset + n <= 4096 /\
     0 <= sign_offset /\ sign_offset + 32 <= 512 /\
     W64.to_uint (BArray16.get64 initial_squares 0) < 281474976710656 /\
     W64.to_uint (BArray16.get64 initial_squares 1) < 281474976710656 /\
     gr_adequate (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j)) n attempts /\
     gs_buffer_segment (shake_stream_byte (shake_initial_words seed0 nonce0))
       bufp 0 0 6664 /\
     word_state_of_barray sp_0 = shake_iterate (shake_initial_words seed0 nonce0) 49 /\
     gs_signs_result (shake_stream_byte (shake_initial_words seed0 nonce0))
       initial_signs signsp sign_offset /\
     signbytes = W64.of_int 32 /\ bytecnt = W64.of_int 6632 /\
     gauss_requested counts = n /\ gauss_available counts = 6632 /\
     dont = W64.of_int (n - 256)) => //.
  + while ((n = 256 \/ n = 257) /\
      (dont = W64.of_int n \/ dont = W64.of_int (n - 256))) (W64.to_uint dont).
    - move=> z; auto => />; smt(gs_dummy_step grt_dont_decrease W64.to_uint_cmp).
    conseq (_ : _ ==> _ : = 1%r) => //.
    wp; call (grt_copy_signs_total
      (shake_stream_byte (shake_initial_words seed0 nonce0))
      initial_signs sign_offset).
    auto => />.
    move=> &hr hn hso0 hso hsign0 hsign hlo hhi had hbuf hstate.
    have hsignbytes := gs_signbytes_word n hn.
    have hprefix : gs_buffer_segment
      (shake_stream_byte (shake_initial_words seed0 nonce0)) bufp{hr} 0 0 32.
    - rewrite /gs_buffer_segment => j hj; apply hbuf; smt().
    have hn512 : 0 <= n <= 512 by smt().
    have hb6632 : 0 <= 6632 <= 8192 by done.
    have hdecode := gs_pack_counts_decode n 6632 hn512 hb6632.
    rewrite /(`>>`) /(`<<`) !W8.of_uintK /= hsignbytes /=.
    move: hdecode; rewrite /= => hdecode.
    split; first exact hprefix.
    move=> _ result hsignresult dont0; split.
    + move=> hd hd0; rewrite W64.uleE W64.of_uintK /=; smt(W64.to_uint_cmp).
    move=> hguard hd.
    have hdone := gs_dummy_done n dont0 hn hd hguard.
    smt().
  while (exists blocks,
    49 <= blocks /\ blocks <= gr_block_cap attempts /\
    blocks = grr_index
      (grt_compatible (shake_initial_words seed0 nonce0) initial initial_squares n sample_offset
        (rp, sqsump, bufp, sp_0, W64.to_uint bytecnt, firstflag <> W64.zero, W64.to_uint total))
      (gr_block_cap attempts) /\ len = W64.of_int n /\
    W64.to_uint sampleoff = sample_offset /\ W64.to_uint signoff = sign_offset /\
    signbytes = W64.of_int 32 /\ dont = W64.of_int (n - 256) /\
    (n = 256 \/ n = 257) /\ 0 <= sample_offset /\ sample_offset + n <= 4096 /\
    0 <= sign_offset /\ sign_offset + 32 <= 512 /\
    gs_signs_result (shake_stream_byte (shake_initial_words seed0 nonce0))
      initial_signs signsp sign_offset /\
    gr_adequate (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j)) n attempts /\
    word_state_of_barray sp_0 = shake_iterate (shake_initial_words seed0 nonce0) blocks /\
    gs_tail_matches (shake_stream_byte (shake_initial_words seed0 nonce0))
      bufp (W64.to_uint bytecnt) (firstflag <> W64.zero) blocks /\
    gs_progress (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j))
      initial rp initial_squares sqsump n sample_offset (gs_stream_attempts blocks)
      (W64.to_uint total))
    (grr_rank
      (grt_compatible (shake_initial_words seed0 nonce0) initial initial_squares n sample_offset
        (rp, sqsump, bufp, sp_0, W64.to_uint bytecnt, firstflag <> W64.zero, W64.to_uint total))
      (gr_block_cap attempts)).
  + move=> z; elim * => blocks.
    exists* total; elim* => total0.
    wp; call (gs_progress_consume_total_dynamic
      (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j))
      initial initial_squares n sample_offset (gs_stream_attempts blocks)
      (W64.to_uint total0) (136 + gs_stream_tail blocks) 0).
    wp; call (gr_refill_squeeze_total (shake_initial_words seed0 nonce0) blocks).
    call (gr_carry_total (shake_stream_byte (shake_initial_words seed0 nonce0)) blocks).
    while (0 <= W64.to_uint off <= W64.to_uint bytecnt /\
      W64.to_uint off %% 26 = W64.to_uint bytecnt %% 26) (W64.to_uint off).
    - move=> t; auto => />.
      move=> &hr ho0 hob hm hguard.
      move: hguard; rewrite W64.uleE (W64.of_uintK 26) /= => hguard.
      have [hsub hrem] := gs_mod26_word_step off{hr} hguard.
      smt(W64.to_uint_cmp).
    auto => /=.
    move=> &hr [ht0 [[hinv hguard] hrank]].
    have [hblocks [hbcap [hmax [hlen [hsample [hsignoff [hsignbytes [hdont [hn
      [hso0 [hsoend [hsg0 [hsgend [hsigns [had [hstate [htail hprogress]]]]]]]]]]]]]]]]] := hinv.
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
    move=> off0; split.
    + move=> [hoRange hoMod] hozero.
      rewrite W64.uleE W64.of_uintK /=; smt(W64.to_uint_cmp).
    move=> hdone [hoRange hoMod].
    have hoff := gs_mod26_word_done (W64.to_uint bytecnt{hr}) off0 hoMod hdone.
    move: hoff; rewrite hmod => hoff.
    have hoffu : W64.to_uint off0 = gs_stream_tail blocks by rewrite hoff htword.
    split; first smt().
    move=> _ carried hcarried.
    split; first smt().
    move=> _ squeezed [hnewstate [hcandidates htailnext]].
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
      move: hnextprogress; rewrite ht0 -hadvance.
    pose P := grt_compatible (shake_initial_words seed0 nonce0)
      initial initial_squares n sample_offset
      (rp{hr}, sqsump{hr}, bufp{hr}, sp_0{hr}, W64.to_uint bytecnt{hr},
       firstflag{hr} <> W64.zero, W64.to_uint total{hr}).
    pose Q := grt_compatible (shake_initial_words seed0 nonce0)
      initial initial_squares n sample_offset
      (consumed.`1, consumed.`2, squeezed.`1, squeezed.`2,
       136 + gs_stream_tail blocks, false,
       W64.to_uint total{hr} + W64.to_uint (BArray8.get64 consumed.`3 0)).
    have hp : P blocks by rewrite /P /grt_compatible /=; smt().
    have hpne : exists b, 49 <= b <= gr_block_cap attempts /\ P b by
      exists blocks; smt().
    have hbstrict : blocks < gr_block_cap attempts by
      exact (grt_compatible_below_cap _ _ _ _ _ _ _ _ had hp hlt).
    have hq : Q (blocks + 1) by rewrite /Q /grt_compatible /=; smt().
    have hPmax : blocks = grr_index P (gr_block_cap attempts) by exact hmax.
    have hindexstrict : grr_index P (gr_block_cap attempts) < gr_block_cap attempts by
      rewrite -hPmax.
    have hQindex : Q (grr_index P (gr_block_cap attempts) + 1) by rewrite -hPmax.
    have hstep := grr_rank_step P Q (gr_block_cap attempts) hpne hindexstrict hQindex.
    have [hqne [hqnonneg hqdec]] := hstep.
    have [hqbounds hqmax] := grr_index_witness Q (gr_block_cap attempts) hqne.
    rewrite hbytesnext htotal /=.
    split.
    + rewrite -/Q.
      exists (grr_index Q (gr_block_cap attempts)).
      have hqparts := grt_compatible_parts _ _ _ _ _ _ _ hqmax.
      have [hqlo hqhi] := hqbounds.
      split; first exact hqlo.
      split; first exact hqhi.
      split; first done.
      split; first exact hsignoff.
      split; first exact hn.
      split; first exact hso0.
      split; first exact hsoend.
      split; first exact hsg0.
      split; first exact hsgend.
      split; first exact hsigns.
      split; first exact had.
      exact hqparts.
    have holdrank : grr_rank P (gr_block_cap attempts) = z by exact hrank.
    by rewrite -holdrank.

  conseq (_ : _ ==> _ : = 1%r) => //.
  wp; call (gs_progress_consume_total_dynamic
    (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j))
    initial initial_squares n sample_offset 0 0 6632 32).
  auto => /=.
  move=> &hr hsetup.
  have [hlen [hsample [hsignoff [hrp [hsq [hn [hso0 [hsoend [hsg0 [hsgend
    [hlo [hhi [had [hbuf [hstate [hsigns [hsignbytes [hbytecnt [hrequested
    [havailable hdont]]]]]]]]]]]]]]]]]]]] := hsetup.
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
  have htail0 := gs_initial_tail
    (shake_stream_byte (shake_initial_words seed0 nonce0)) bufp{hr} hbuf.
  have hbyteu : W64.to_uint bytecnt{hr} = 6632 by rewrite hbytecnt W64.of_uintK /=.
  have hfirst : W64.one <> W64.zero by
    rewrite W64.to_uint_eq W64.to_uint1 W64.to_uint0.
  have hattempts : gs_stream_attempts 49 = 255 by rewrite /gs_stream_attempts.
  have [_ hattempts0] := gr_adequate_bounds _ _ _ had.
  have [hcap _] := gr_block_cap_bounds attempts hattempts0.
  pose P := grt_compatible (shake_initial_words seed0 nonce0)
    initial initial_squares n sample_offset
    (result.`1, result.`2, bufp{hr}, sp_0{hr}, 6632, true,
     W64.to_uint (BArray8.get64 result.`3 0)).
  have hp : P 49 by rewrite /P /grt_compatible /=; smt().
  have hpne : exists b, 49 <= b <= gr_block_cap attempts /\ P b by
    exists 49; smt().
  have [hpbounds hpmax] := grr_index_witness P (gr_block_cap attempts) hpne.
  have hnonneg := grr_rank_nonnegative P (gr_block_cap attempts) hpne.
  rewrite hbyteu hfirst /=.
  split.
  + rewrite -/P.
    exists (grr_index P (gr_block_cap attempts)).
    have hpparts := grt_compatible_parts _ _ _ _ _ _ _ hpmax.
    smt().
  move=> bufp0 bytecnt0 dont0 firstflag0 len0 rp0 sampleoff0 signbytes0 signoff0
    signsp0 sp00 sqsump0 total0 [blocks hinv] hrank0.
  have [hblocks [hbcap [hmax [hlen0 [hsample0 [hsignoff0 [hsignbytes0 [hdont0 [hn0
    [hsoL [hsoE [hsgL [hsgE [hsigns0 [had0 [hstate0 [htailEnd hprogress]]]]]]]]]]]]]]]]] := hinv.
  pose P0 := grt_compatible (shake_initial_words seed0 nonce0)
    initial initial_squares n sample_offset
    (rp0, sqsump0, bufp0, sp00, W64.to_uint bytecnt0, firstflag0 <> W64.zero,
     W64.to_uint total0).
  have hp0 : P0 blocks by rewrite /P0 /grt_compatible /=; smt().
  have hsome0 : exists b, 49 <= b <= gr_block_cap attempts /\ P0 b by
    exists blocks; smt().
  have hnword : W64.to_uint (W64.of_int n) = n by
    rewrite W64.of_uintK /=; apply modz_small; smt().
  rewrite hlen0 W64.ultE hnword.
  have hpos : W64.to_uint total0 < n =>
    0 < grr_rank P0 (gr_block_cap attempts).
  + move=> hlt; exact (grt_rank_positive _ _ _ _ _ _ _ had0 hsome0 hlt).
  have hzero : grr_rank P0 (gr_block_cap attempts) <= 0 by exact hrank0.
  smt().
qed.

lemma gr_sample_gauss_N_prefix_total
    (seed0 : BArray64.t) (nonce0 : W64.t) (n sample_offset sign_offset attempts : int)
    (initial : BArray32768.t) (initial_signs : BArray512.t) (initial_squares : BArray16.t) :
  phoare [StreamSigner._sf_sample_gauss_N_full_at :
    seedp = seed0 /\ nonce = nonce0 /\ len = W64.of_int n /\
    W64.to_uint sampleoff = sample_offset /\ W64.to_uint signoff = sign_offset /\
    rp = initial /\ signsp = initial_signs /\ sqsump = initial_squares /\
    (n = 256 \/ n = 257) /\ 0 <= sample_offset /\ sample_offset + n <= 4096 /\
    0 <= sign_offset /\ sign_offset + 32 <= 512 /\
    W64.to_uint (BArray16.get64 initial_squares 0) < 281474976710656 /\
    W64.to_uint (BArray16.get64 initial_squares 1) < 281474976710656 /\
    gr_adequate (fun j => shake_stream_byte (shake_initial_words seed0 nonce0) (32 + j)) n attempts
    ==>
    gr_prefix_result (shake_stream_byte (shake_initial_words seed0 nonce0))
      initial res.`1 initial_signs res.`2 initial_squares res.`3
      n sample_offset sign_offset attempts] = 1%r.
proof.
  by conseq (gr_sample_gauss_N_adequate_lossless seed0 nonce0 n sample_offset sign_offset attempts
      initial initial_signs initial_squares)
    (gr_sample_gauss_N_prefix_correct seed0 nonce0 n sample_offset sign_offset attempts
      initial initial_signs initial_squares).
qed.
