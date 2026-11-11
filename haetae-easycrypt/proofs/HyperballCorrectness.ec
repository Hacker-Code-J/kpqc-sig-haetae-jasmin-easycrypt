require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import ApiTarget GaussianOffsetBridge GaussianStreamCorrectness
  GaussianStreamSpec GaussianBufferLemmas HyperballFixedPointSpec
  HyperballFixedPointCorrectness.
import SLH64.

module HBSigner = GaussianOffsetBridge.Signer.

(* Counter equalities are word equalities and remain valid across wraparound. *)
lemma hb_nonce_successor (base : W64.t) (i : int) :
  (base + W64.of_int i) + W64.one = base + W64.of_int (i + 1).
proof. by rewrite W64.of_intD; ring. qed.

lemma hb_nonce_retry_step (base : W64.t) (total trials : int) :
  (base + W64.of_int (total * trials)) + W64.of_int total =
    base + W64.of_int (total * (trials + 1)).
proof.
  have -> : total * (trials + 1) = total * trials + total by ring.
  by rewrite W64.of_intD; ring.
qed.

lemma hb_count_add_word (l k : int) :
  W64.of_int l + W64.of_int k = W64.of_int (l + k).
proof. by rewrite -W64.of_intD. qed.

lemma hb_count_add_uint (l k : int) :
  0 <= l <= 8 => 0 <= k <= 8 =>
  W64.to_uint (W64.of_int l + W64.of_int k) = l + k.
proof.
  move=> hl hk; rewrite hb_count_add_word W64.of_uintK /=.
  apply modz_small; smt().
qed.

lemma hb_coeff_shift_word (c : int) :
  W64.of_int c `<<` W8.of_int 8 = W64.of_int (256 * c).
proof.
  rewrite /(`<<`) W8.of_uintK /= W64.shlMP 1:// /=.
  congr; ring.
qed.

lemma hb_coeff_shift_uint (c : int) :
  0 <= c <= 11 => W64.to_uint (W64.of_int c `<<` W8.of_int 8) = 256 * c.
proof.
  move=> hc; rewrite hb_coeff_shift_word W64.of_uintK /=.
  apply modz_small; smt().
qed.

lemma hb_sample_offset_word (i : int) :
  W64.of_int i * W64.of_int 256 = W64.of_int (256 * i).
proof.
  have -> : 256 * i = i * 256 by ring.
  by rewrite W64.of_intM.
qed.

lemma hb_sign_offset_word (i : int) :
  W64.of_int i * W64.of_int 32 = W64.of_int (32 * i).
proof.
  have -> : 32 * i = i * 32 by ring.
  by rewrite W64.of_intM.
qed.

lemma hb_sample_offset_uint (i : int) :
  0 <= i <= 11 => W64.to_uint (W64.of_int i * W64.of_int 256) = 256 * i.
proof.
  move=> hi; rewrite hb_sample_offset_word W64.of_uintK /=.
  apply modz_small; smt().
qed.

lemma hb_sign_offset_uint (i : int) :
  0 <= i <= 11 => W64.to_uint (W64.of_int i * W64.of_int 32) = 32 * i.
proof.
  move=> hi; rewrite hb_sign_offset_word W64.of_uintK /=.
  apply modz_small; smt().
qed.

lemma hb_gaussian_window_capacity (i : int) :
  0 <= i < 11 =>
  0 <= 256 * i /\ 256 * i + 257 <= 4096 /\
  0 <= 32 * i /\ 32 * i + 32 <= 512.
proof. smt(). qed.

lemma hb_index_successor (i : W64.t) :
  W64.to_uint i < 11 =>
  W64.to_uint (i + W64.one) = W64.to_uint i + 1.
proof. move=> hi; by rewrite W64.to_uintD_small 1:/# W64.to_uint1. qed.

lemma hb_request_draw_count (i : int) :
  0 <= i =>
  256 * (i + 1) + min (i + 1) 2 =
    256 * i + min i 2 + (if i < 2 then 257 else 256).
proof. rewrite /min; smt(). qed.

lemma hb_draw_count_bound (i : int) :
  0 <= i <= 11 => 0 <= 256 * i + min i 2 <= 2818.
proof. rewrite /min; smt(). qed.

lemma hb_cube_initial (p : BArray16.t) (cube : hb_fp) :
  BArray16.set64 (BArray16.set64 p 0 cube.`1) 1 cube.`2 = hb_pack cube.
proof. exact (hb_store_pack p cube). qed.

require import HyperballSpec HyperballBatchCorrectness HyperballHistoryCorrectness
  HyperballByteCorrectness HyperballScaleSpec HyperballScaleCorrectness
  HyperballReferenceConstants.
import HyperballScaleSpec.

lemma hb_nonce_nested base a b :
  hb_nonce (hb_nonce base a) b = hb_nonce base (a + b).
proof. by rewrite /hb_nonce W64.of_intD; ring. qed.

lemma hb_nonce_zero base : hb_nonce base 0 = base.
proof. by rewrite /hb_nonce /=. qed.

lemma hb_nonce_one base : hb_nonce base 1 = base + W64.one.
proof. by rewrite /hb_nonce /=. qed.

lemma hb_nonce_batch_done base m trials :
  hb_nonce (hb_nonce base (m * trials)) m = hb_nonce base (m * (trials + 1)).
proof.
  rewrite hb_nonce_nested; congr; ring.
qed.

lemma hb_shape_coefficients l k :
  hb_shape l k => hb_scale_bounds (256 * l) (256 * (l + k)).
proof. rewrite /hb_shape /hb_scale_bounds; smt(). qed.

(* Each terminating execution records every completed attempt. The norm
   acceptance remains the production unsigned comparison modulo 2^64. *)
lemma hyperball_full_correct
    (seed0 : BArray64.t) (base0 : W64.t) (l k : int)
    (cube three : hb_fp) (scale0 bound0 : W64.t)
    (initial1 initial2 : BArray8192.t) :
  hoare [HBSigner._sf_hyperball_full :
    seedp = seed0 /\ BArray8.get64 counterp 0 = base0 /\
    y1p = initial1 /\ y2p = initial2 /\
    lcount = W64.of_int l /\ kcount = W64.of_int k /\
    scale_const = scale0 /\ bound_const = bound0 /\
    cube0 = cube.`1 /\ cube1 = cube.`2 /\
    three0 = three.`1 /\ three1 = three.`2 /\ hb_shape l k
    ==>
    hb_result seed0 base0 l k cube three scale0 bound0 initial1 initial2
      res.`1 res.`2 res.`3 res.`4].
proof.
  proc; wp.
  ecall (HyperballByteCorrectness.hyperball_b_raw_correct seed0 ni).
  while (exists history,
    seedp = seed0 /\ lcount = W64.of_int l /\ kcount = W64.of_int k /\
    scale_const = scale0 /\ bound_const = bound0 /\
    cubep = hb_pack cube /\ threep = hb_pack three /\ hb_shape l k /\
    hb_history seed0 base0 l k cube three scale0 bound0 initial1 initial2
      history y1p y2p accepted /\
    ni = hb_nonce base0 ((l + k) * size history)).
  + elim * => history.
    seq 16 : (exists draw,
      seedp = seed0 /\ lcount = W64.of_int l /\ kcount = W64.of_int k /\
      scale_const = scale0 /\ bound_const = bound0 /\
      cubep = hb_pack cube /\ threep = hb_pack three /\ hb_shape l k /\
      hb_history seed0 base0 l k cube three scale0 bound0 initial1 initial2
        history y1p y2p W64.zero /\
      ni = hb_nonce base0 ((l + k) * (size history + 1)) /\
      total = W64.of_int (l + k) /\
      hb_batch_complete seed0 (hb_nonce base0 ((l + k) * size history))
        (l + k) draw /\
      samplesp = draw.`1 /\ signsp = draw.`2 /\ sqsump = draw.`3).
    - while (exists blocks,
        seedp = seed0 /\ lcount = W64.of_int l /\ kcount = W64.of_int k /\
        scale_const = scale0 /\ bound_const = bound0 /\
        cubep = hb_pack cube /\ threep = hb_pack three /\ hb_shape l k /\
        hb_history seed0 base0 l k cube three scale0 bound0 initial1 initial2
          history y1p y2p W64.zero /\
        total = W64.of_int (l + k) /\
        2 <= W64.to_uint idx <= l + k /\ size blocks = W64.to_uint idx /\
        ni = hb_nonce (hb_nonce base0 ((l + k) * size history)) (size blocks) /\
        hb_batch_progress seed0 (hb_nonce base0 ((l + k) * size history))
          blocks samplesp signsp sqsump).
      * elim * => blocks.
        wp; ecall (hb_batch_call_correct seed0
          (hb_nonce base0 ((l + k) * size history)) blocks samplesp signsp sqsump).
        wp; auto => /=.
        move=> &hr [hinv hguard].
        have [hseed [hl [hk [hscale [hbound [hcube [hthree [hshape
          [hhistory [htotal [hidx [hsize [hni hbatch]]]]]]]]]]]]] := hinv.
        have hshape' : 0 <= l <= 8 /\ 0 <= k <= 8 /\ 2 <= l + k <= 11
          by exact hshape.
        have htotalu : W64.to_uint total{hr} = l + k by
          rewrite htotal W64.of_uintK /= modz_small; smt().
        have hidxlt : W64.to_uint idx{hr} < l + k by
          move: hguard; rewrite W64.ultE htotalu.
        have hlimit : 0 <= size blocks < 11 by smt().
        have hidxw : idx{hr} = W64.of_int (size blocks) by
          rewrite hsize W64.to_uintK.
        have hsampleu := hb_sample_offset_uint (size blocks) _; first smt().
        have hsignu := hb_sign_offset_uint (size blocks) _; first smt().
        have hrequest : hb_request (size blocks) = 256 by rewrite /hb_request; smt().
        rewrite hidxw.
        split; first by rewrite hseed hni hrequest hsampleu hsignu hbatch hlimit.
        move=> _ result [block [hblock hnext]].
        exists (blocks ++ [block]).
        rewrite size_cat /=.
        have hnextidx : W64.to_uint (W64.of_int (size blocks + 1)) =
          size blocks + 1 by
          rewrite W64.of_uintK /= modz_small; clear -hlimit; smt().
        have hnextnonce := hb_nonce_step
          (hb_nonce base0 ((l + k) * size history)) (size blocks).
        rewrite hseed hl hk hscale hbound hcube hthree hshape hhistory htotal
          hnextidx hni -hnextnonce hnext /=.
        clear -hidx hidxlt hsize; smt().
      seq 7 : (exists firstblock,
        seedp = seed0 /\ lcount = W64.of_int l /\ kcount = W64.of_int k /\
        scale_const = scale0 /\ bound_const = bound0 /\
        cubep = hb_pack cube /\ threep = hb_pack three /\ hb_shape l k /\
        hb_history seed0 base0 l k cube three scale0 bound0 initial1 initial2
          history y1p y2p W64.zero /\
        ni = hb_nonce base0 ((l + k) * size history) /\ len = W64.of_int 257 /\
        hb_batch_progress seed0 (hb_nonce base0 ((l + k) * size history))
          [firstblock] samplesp signsp sqsump).
      * ecall (hb_batch_call_correct seed0
          (hb_nonce base0 ((l + k) * size history)) (iota_ 0 0) samplesp signsp sqsump).
        auto => /=.
        move=> &hr [hinv hguard].
        have [hseed [hl [hk [hscale [hbound [hcube [hthree [hshape
          [hhistory hni]]]]]]]]] := hinv.
        move: hhistory; rewrite hguard => hhistory.
        have hzero := hb_batch_progress_initial seed0
          (hb_nonce base0 ((l + k) * size history)) samplesp{hr} signsp{hr}
          (BArray16.set64 (BArray16.set64 sqsump{hr} 0 W64.zero) 1 W64.zero) _ _;
          first 2 by rewrite !BArray16.get_set64E /=.
        rewrite iota0 1:// /=.
        split; first by rewrite /hb_request /= hb_nonce_zero hseed hni hzero.
        move=> _ result [block [hblock hnext]].
        exists block.
        by rewrite hseed hl hk hscale hbound hcube hthree hshape hhistory hni hnext.
      elim * => firstblock.
      wp; ecall (hb_batch_call_correct seed0
        (hb_nonce base0 ((l + k) * size history)) [firstblock] samplesp signsp sqsump).
      auto => /=.
      move=> &hr hsetup.
      have [hseed [hl [hk [hscale [hbound [hcube [hthree [hshape
        [hhistory [hni [hlen hbatch]]]]]]]]]]] := hsetup.
      split; first by rewrite /hb_request /= hb_nonce_one hseed hni hlen hbatch.
      move=> _ result [block [hblock hnext]].
      split.
      * exists [firstblock; block].
        have hn2 :
          (hb_nonce base0 ((l + k) * size history) + W64.one) + W64.one =
          hb_nonce (hb_nonce base0 ((l + k) * size history)) 2 by
          rewrite -(hb_nonce_one (hb_nonce base0 ((l + k) * size history)))
            -(hb_nonce_step (hb_nonce base0 ((l + k) * size history)) 1).
        rewrite /= hseed hl hk hscale hbound hcube hthree hshape hhistory hni
          hb_count_add_word hn2 hnext /=.
        clear -hshape; rewrite /hb_shape in hshape; smt().
      move=> idx0 ni0 samplesp0 signsp0 sqsump0 hdone [blocks hinv].
      have [hseed0 [hl0 [hk0 [hscale0 [hbound0 [hcube0 [hthree0 [hshape0
        [hhistory0 [htotal0 [hidx0 [hsize0 [hni0 hbatch0]]]]]]]]]]]]] := hinv.
      have htotalu : W64.to_uint (W64.of_int (l + k)) = l + k by
        rewrite W64.of_uintK /= modz_small; move: hshape0; rewrite /hb_shape; smt().
      have hfinalsize : size blocks = l + k by
        move: hdone; rewrite htotal0 W64.ultE htotalu; smt().
      exists (samplesp0, signsp0, sqsump0).
      have hcomplete : hb_batch_complete seed0
        (hb_nonce base0 ((l + k) * size history)) (l + k)
        (samplesp0, signsp0, sqsump0) by
        rewrite /hb_batch_complete /=; exists blocks; split;
        [exact hfinalsize | exact hbatch0].
      have hfinalni : ni0 = hb_nonce base0 ((l + k) * (size history + 1)) by
        rewrite hni0 hfinalsize hb_nonce_batch_done.
      by rewrite /= hseed0 htotal0 hl0 hk0 hscale0 hbound0 hcube0 hthree0 hshape0
        hhistory0 hfinalni hcomplete.
    elim * => draw.
    ecall (HyperballScaleCorrectness.hb_scale_and_check_correct
      y1p y2p draw.`1 draw.`2 (hb_draw_scale draw cube three scale0)
      (256 * l) (256 * (l + k)) bound0).
    wp; ecall (hb_mul_high_correct invsqrtp scale0).
    wp; ecall (hb_newton_correct sqsump (hb_pack cube) (hb_pack three)).
    ecall (hb_half_round_correct draw.`3).
    auto => /=.
    move=> &hr hbatch.
    have [hseed [hl [hk [hscale [hbound [hcube [hthree [hshape
      [hhistory [hni [htotal [hcomplete [hsamples [hsigns hsquares]]]]]]]]]]]]]] := hbatch.
    split; first exact hsquares.
    move=> _ half hhalf.
    split; first smt().
    move=> _ inverse hinverse.
    split; first smt().
    move=> _ factor hfactor.
    have hfactor' : factor = hb_draw_scale draw cube three scale0 by
      rewrite hfactor hinverse hhalf !hb_load_pack /hb_draw_scale /hb_scale_factor.
    have hscalebounds := hb_shape_coefficients l k hshape.
    split; first by rewrite hfactor' hl htotal !hb_coeff_shift_word
      hsamples hsigns hbound hscalebounds.
    move=> _ scaled hscaled.
    have hnewhistory := hb_history_append seed0 base0 l k cube three scale0 bound0
      initial1 initial2 history y1p{hr} y2p{hr} draw scaled
      hshape hhistory hcomplete hscaled.
    exists (rcons history draw).
    by rewrite size_rcons hseed hl hk hscale hbound hcube hthree hshape hnewhistory hni.
  wp; auto => /=.
  move=> &hr [hseed [hcounter [hy1 [hy2 [hl [hk [hscale [hbound
    [hc0 [hc1 [ht0 [ht1 hshape]]]]]]]]]]]].
  split.
  + exists [].
    by rewrite /= hseed hl hk hscale hbound hc0 hc1 ht0 ht1 !hb_cube_initial
      hshape hy1 hy2 hb_history_initial hb_nonce_zero hcounter.
  move=> accepted0 ni0 y1p0 y2p0 hdone [history hinv].
  have [_ [_ [_ [_ [_ [_ [_ [_ [hhistory hni]]]]]]]]] := hinv.
  split; first exact hseed.
  move=> _ result hbyte.
  apply (hb_history_finish seed0 base0 l k cube three scale0 bound0
    initial1 initial2 history y1p0 y2p0 accepted0 result
    (BArray8.set64 (protect_ptr counterp{hr} W64.zero) 0 ni0)).
  + exact hhistory.
  + exact hdone.
  + by rewrite /hb_stream -hni; exact hbyte.
  by rewrite BArray8.get_set64E //=.
qed.

lemma hyperball_mode2_correct (seed0 : BArray64.t) (base0 : W64.t)
    (initial1 initial2 : BArray8192.t) :
  hoare [HBSigner._sf_hyperball_mode2 :
    seedp = seed0 /\ BArray8.get64 counterp 0 = base0 /\
    y1p = initial1 /\ y2p = initial2 ==>
    hb_result seed0 base0 (hb_ref_l 2) (hb_ref_k 2)
      (hb_ref_cube 2) (hb_ref_three 2) (hb_ref_scale 2) (hb_ref_bound 2)
      initial1 initial2 res.`1 res.`2 res.`3 res.`4].
proof.
  proc; call (hyperball_full_correct seed0 base0 (hb_ref_l 2) (hb_ref_k 2)
    (hb_ref_cube 2) (hb_ref_three 2) (hb_ref_scale 2) (hb_ref_bound 2)
    initial1 initial2).
  auto => />; rewrite /protect_ptr /protect_64 /hb_ref_l /hb_ref_k
    /hb_ref_cube /hb_ref_three /hb_ref_scale /hb_ref_bound /hb_shape /=.
qed.

lemma hyperball_mode3_correct (seed0 : BArray64.t) (base0 : W64.t)
    (initial1 initial2 : BArray8192.t) :
  hoare [HBSigner._sf_hyperball_mode3 :
    seedp = seed0 /\ BArray8.get64 counterp 0 = base0 /\
    y1p = initial1 /\ y2p = initial2 ==>
    hb_result seed0 base0 (hb_ref_l 3) (hb_ref_k 3)
      (hb_ref_cube 3) (hb_ref_three 3) (hb_ref_scale 3) (hb_ref_bound 3)
      initial1 initial2 res.`1 res.`2 res.`3 res.`4].
proof.
  proc; call (hyperball_full_correct seed0 base0 (hb_ref_l 3) (hb_ref_k 3)
    (hb_ref_cube 3) (hb_ref_three 3) (hb_ref_scale 3) (hb_ref_bound 3)
    initial1 initial2).
  auto => />; rewrite /protect_ptr /protect_64 /hb_ref_l /hb_ref_k
    /hb_ref_cube /hb_ref_three /hb_ref_scale /hb_ref_bound /hb_shape /=.
qed.

lemma hyperball_mode5_correct (seed0 : BArray64.t) (base0 : W64.t)
    (initial1 initial2 : BArray8192.t) :
  hoare [HBSigner._sf_hyperball_mode5 :
    seedp = seed0 /\ BArray8.get64 counterp 0 = base0 /\
    y1p = initial1 /\ y2p = initial2 ==>
    hb_result seed0 base0 (hb_ref_l 5) (hb_ref_k 5)
      (hb_ref_cube 5) (hb_ref_three 5) (hb_ref_scale 5) (hb_ref_bound 5)
      initial1 initial2 res.`1 res.`2 res.`3 res.`4].
proof.
  proc; call (hyperball_full_correct seed0 base0 (hb_ref_l 5) (hb_ref_k 5)
    (hb_ref_cube 5) (hb_ref_three 5) (hb_ref_scale 5) (hb_ref_bound 5)
    initial1 initial2).
  auto => />; rewrite /protect_ptr /protect_64 /hb_ref_l /hb_ref_k
    /hb_ref_cube /hb_ref_three /hb_ref_scale /hb_ref_bound /hb_shape /=.
qed.
