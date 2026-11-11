require import AllCore IntDiv List StdRing StdOrder.
from Jasmin require import JModel_x86.
require import HyperballFixedPointSpec HyperballFixedPointCorrectness
  HyperballReferenceConstants HyperballSafeSpec HyperballSafeConstants GaussianAccumulatorCorrectness
  HyperballMulBounds HyperballPositiveArithmetic HyperballNewtonBarrier.

(* The first subtraction may leave a low limb as large as2R-1. The
   inductive representation records that slack, rather than assuming a
   canonical first iterate. All value bounds concern the actual words. *)
op hsn_state (upper : int) (x : hb_fp) : bool =
  W64.to_uint x.`1 < 2*hbs_radix /\ 0 <= hb_value x <= upper.

lemma hsn_value_nonnegative (x : hb_fp) : 0 <= hb_value x.
proof.
  have hx := W64.to_uint_cmp x.`1.
  have hy := W64.to_uint_cmp x.`2.
  rewrite /hb_value; smt().
qed.

lemma hsn_norm_canonical (x : hb_fp) : hbs_canonical (hb_norm x).
proof.
  have h := hb_norm_low_bound x.
  rewrite /hbs_canonical /hbs_radix; smt().
qed.

lemma hsn_half_canonical (x : hb_fp) : hbs_canonical (hb_half_round x).
proof. rewrite /hb_half_round; apply hsn_norm_canonical. qed.

lemma hsn_mul_canonical (x y : hb_fp) : hbs_canonical (hb_mul x y).
proof. rewrite /hb_mul /=; apply hsn_norm_canonical. qed.

lemma hsn_square_canonical (x : hb_fp) : hbs_canonical (hb_square x).
proof.
  have h := gauss_square_low_bound x.`1 x.`2.
  rewrite /hbs_canonical /hbs_radix /hb_square; smt().
qed.

lemma hsn_cneg_canonical (x : hb_fp) (sign : W64.t) : hbs_canonical (hb_cneg x sign).
proof. rewrite /hb_cneg /=; apply hsn_norm_canonical. qed.

lemma hsn_signed_mul_canonical (x y : hb_fp) : hbs_canonical (hb_signed_mul x y).
proof. rewrite /hb_signed_mul /=; apply hsn_cneg_canonical. qed.

lemma hsn_step_canonical (half current : hb_fp) :
  hbs_canonical (hb_newton_step half current).
proof. rewrite /hb_newton_step; apply hsn_signed_mul_canonical. qed.

lemma hsn_newton_canonical (half cube three : hb_fp) :
  hbs_canonical (hb_newton half cube three).
proof.
  rewrite /hb_newton (hb_newton_iterS half (hb_newton_initial half cube three) 5) 1://.
  apply hsn_step_canonical.
qed.

lemma hsn_canonical_operand (x : hb_fp) :
  hbs_canonical x => hb_value x <= hbs_operand_cap => hbs_operand x.
proof. rewrite /hbs_canonical /hbs_operand /hbs_radix; smt(). qed.

lemma hsn_state_operand (upper : int) (x : hb_fp) :
  hsn_state upper x => upper <= hbs_operand_cap => hbs_operand x.
proof. rewrite /hsn_state /hbs_operand; smt(). qed.

lemma hsn_half_window (mode : int) (sum : hb_fp) : hbs_good mode sum =>
  hbs_canonical (hb_half_round sum) /\
  hbs_half_min mode <= hb_value (hb_half_round sum) <= hbs_half_max mode.
proof.
  rewrite /hbs_good; move=> [hm [hc hs]].
  have hc' : W64.to_uint sum.`1 < 281474976710656 by
    move: hc; rewrite /hbs_canonical /hbs_radix.
  have he := hb_half_round_integer sum hc'.
  have hl := leq_div2r 2 (hbs_sum_min mode) (hb_value sum+1) _ _;
    first 2 smt().
  have hu := leq_div2r 2 (hb_value sum+1) (hbs_sum_max mode+1) _ _;
    first 2 smt().
  split; first exact (hsn_half_canonical sum).
  rewrite he /hbs_half_min /hbs_half_max; smt().
qed.

lemma hsn_iter_preserves (half start : hb_fp) (upper iterations : int) :
  0 <= iterations => hsn_state upper start =>
  (forall x, hsn_state upper x => hsn_state upper (hb_newton_step half x)) =>
  hsn_state upper (hb_newton_iter half start iterations).
proof.
  move=> hk hstart hstep.
  elim: iterations hk => [|k hk ih].
  + by rewrite hb_newton_iter0.
  rewrite (hb_newton_iterS half start k hk).
  exact (hstep _ ih).
qed.

lemma hsn_half_operand (mode : int) (sum : hb_fp) : hbs_good mode sum =>
  hbs_operand (hb_half_round sum).
proof.
  move=> hg; have [hc hw] := hsn_half_window mode sum hg.
  have hm : hbs_mode mode by move: hg; rewrite /hbs_good; smt().
  have [hb _] := hbs_half_certificate mode (hb_value (hb_half_round sum)) hm hw.
  apply hsn_canonical_operand; smt().
qed.

lemma hsn_square_numeric_bound (upper y s : int) :
  0 <= y <= upper => upper <= 2^71 =>
  `|hbs_q*s-y*y| <= hbs_q => s <= 2^66+1.
proof.
  move=> hy hupper hs.
  have hy0 : 0 <= y by smt().
  have hy71 : y <= 2361183241434822606848 by move: hupper; rewrite /=; smt().
  have hp0 : 0 <= 2361183241434822606848 by trivial.
  have hm1 := IntOrder.ler_wpmul2r y hy0 y 2361183241434822606848 hy71.
  have hm2 := IntOrder.ler_wpmul2l 2361183241434822606848 hp0 y 2361183241434822606848 hy71.
  have hyy : y*y <= 2361183241434822606848*2361183241434822606848 by smt().
  move: hs hyy; rewrite IntOrder.ler_norml /hbs_q /=; smt().
qed.

lemma hsn_barrier_scale : hnb_Q = hbs_q.
proof. by rewrite /hnb_Q /hbs_q. qed.

lemma hsn_initial_safe (mode : int) (half : hb_fp) :
  hbs_mode mode => hbs_canonical half =>
  hbs_half_min mode <= hb_value half <= hbs_half_max mode =>
  hsn_state (hbs_inverse_cap mode)
    (hb_newton_initial half (hb_ref_cube mode) (hb_ref_three mode)).
proof.
  move=> hm hc hw.
  have hmode := hbs_mode_certificate mode hm.
  have [hh _] := hbs_half_certificate mode (hb_value half) hm hw.
  have halfop : hbs_operand half by apply hsn_canonical_operand; smt().
  have cubec : hbs_canonical (hb_ref_cube mode) by smt().
  have cubecap : hb_value (hb_ref_cube mode) <= hbs_operand_cap by smt().
  have cubeop := hsn_canonical_operand (hb_ref_cube mode) cubec cubecap.
  pose product := hb_mul half (hb_ref_cube mode).
  have he := hmb_mul_error half (hb_ref_cube mode) halfop cubeop.
  have [hd hp] := hbs_initial_numeric_bound mode (hb_value half) (hb_value product) hm hw he.
  have threec : hbs_canonical (hb_ref_three mode) by smt().
  have threecap : hb_value (hb_ref_three mode) <= hbs_operand_cap by smt().
  have productc : hbs_canonical product by exact (hsn_mul_canonical half (hb_ref_cube mode)).
  have productcap : hb_value product <= hbs_operand_cap by smt().
  have difference : hbs_radix <= hb_value (hb_ref_three mode)-hb_value product by smt().
  have [hl hv] := hpa_sub_exact (hb_ref_three mode) product
    threec productc threecap productcap difference.
  rewrite /hb_newton_initial -/product /hsn_state hv.
  move: hd; rewrite /hbs_radix; smt().
qed.

lemma hsn_step_safe (mode : int) (half current : hb_fp) :
  hbs_mode mode => hbs_canonical half =>
  hbs_half_min mode <= hb_value half <= hbs_half_max mode =>
  hsn_state (hbs_inverse_cap mode) current =>
  hsn_state (hbs_inverse_cap mode) (hb_newton_step half current).
proof.
  move=> hm hc hw hx.
  pose upper := hbs_inverse_cap mode.
  have hmode := hbs_mode_certificate mode hm.
  have [hh [hlo hhi]] := hbs_half_certificate mode (hb_value half) hm hw.
  have hH : 2^70 <= upper <= 2^71 by smt().
  have hHcap : upper <= hbs_operand_cap by move: hH; rewrite /hbs_operand_cap /=; smt().
  have hh88 : 0 <= hb_value half <= 2^88 by move: hh; rewrite /hbs_operand_cap /=.
  have hy : 0 <= hb_value current <= upper by move: hx; rewrite /hsn_state; smt().
  have halfop : hbs_operand half by apply hsn_canonical_operand; smt().
  have currentop := hsn_state_operand upper current hx hHcap.
  pose squared := hb_square current.
  have es := hmb_square_error current currentop.
  have hMax : upper <= 2^71 by smt().
  have hsq := hsn_square_numeric_bound upper (hb_value current) (hb_value squared) hy hMax es.
  have sqcap : hb_value squared <= hbs_operand_cap by move: hsq; rewrite /hbs_operand_cap /=; smt().
  have sqc : hbs_canonical squared by exact (hsn_square_canonical current).
  have sqop := hsn_canonical_operand squared sqc sqcap.
  pose product := hb_mul half squared.
  have eu := hmb_mul_error half squared halfop sqop.
  have lower : 17*hnb_Q^3 <= 32*hb_value half*upper*upper.
  + rewrite hsn_barrier_scale.
    have -> : 32*hb_value half*upper*upper = 16*2*hb_value half*(hbs_inverse_cap mode)^2
      by rewrite /upper; ring.
    exact hlo.
  have upperbar : 8*hb_value half*upper*upper <= 9*hnb_Q^3.
  + rewrite hsn_barrier_scale.
    have -> : 8*hb_value half*upper*upper = 8*hb_value half*(hbs_inverse_cap mode)^2
      by rewrite /upper; ring.
    exact hhi.
  have es' : `|hnb_Q*hb_value squared-hb_value current*hb_value current| <= hnb_Q
    by rewrite hsn_barrier_scale; exact es.
  have eu' : `|hnb_Q*hb_value product-hb_value half*hb_value squared| <= hnb_Q
    by rewrite hsn_barrier_scale; exact eu.
  have hub := hnb_u_bound (hb_value half) upper (hb_value current)
    (hb_value squared) (hb_value product) hH hy hh88 upperbar es' eu'.
  have uroom : hb_value product <= 3*hbs_q %/ 2.
  + move: hub; rewrite hsn_barrier_scale /hbs_q /=; smt().
  have productc : hbs_canonical product by exact (hsn_mul_canonical half squared).
  pose correction := hb_threehalves_minus product.
  have [tc te] := hpa_threehalves_exact product productc uroom.
  have u0 := hsn_value_nonnegative product.
  have tupper : hb_value correction <= 3*hbs_q %/ 2 by smt().
  have tcap : hb_value correction <= hbs_operand_cap by
    move: tupper; rewrite /hbs_q /hbs_operand_cap /=; smt().
  have top := hsn_canonical_operand correction tc tcap.
  pose next := hb_mul correction current.
  have ez := hmb_mul_error correction current top currentop.
  have ez' : `|hnb_Q*hb_value next-hb_value correction*hb_value current| <= hnb_Q
    by rewrite hsn_barrier_scale; exact ez.
  have te' : hb_value correction = (3*hnb_Q) %/ 2-hb_value product
    by rewrite hsn_barrier_scale; exact te.
  have s0 := hsn_value_nonnegative squared.
  have z0 := hsn_value_nonnegative next.
  have hz := hnb_z_bound (hb_value half) upper (hb_value current) (hb_value squared)
    (hb_value product) (hb_value correction) (hb_value next)
    hH hy hh88 lower upperbar es' s0 eu' u0 te' ez' z0.
  have he : hb_newton_step half current = next.
  + rewrite /hb_newton_step -/squared -/product -/correction /next.
    exact (hpa_signed_mul_positive current correction tc tupper).
  have hnext := hsn_mul_canonical correction current.
  rewrite he /hsn_state -/upper.
  move: hnext; rewrite /hbs_canonical /hbs_radix; smt().
qed.

lemma hbs_safe_newton (mode : int) (sum : hb_fp) : hbs_good mode sum =>
  hbs_canonical (hb_newton (hb_half_round sum) (hb_ref_cube mode) (hb_ref_three mode)) /\
  0 <= hb_value (hb_newton (hb_half_round sum) (hb_ref_cube mode) (hb_ref_three mode)) <=
    hbs_inverse_cap mode.
proof.
  move=> hg.
  have hm : hbs_mode mode by move: hg; rewrite /hbs_good; smt().
  have [hc hw] := hsn_half_window mode sum hg.
  have hi := hsn_initial_safe mode (hb_half_round sum) hm hc hw.
  have hs : forall x, hsn_state (hbs_inverse_cap mode) x =>
      hsn_state (hbs_inverse_cap mode) (hb_newton_step (hb_half_round sum) x).
  + move=> x hx; exact (hsn_step_safe mode (hb_half_round sum) x hm hc hw hx).
  have hf := hsn_iter_preserves (hb_half_round sum)
    (hb_newton_initial (hb_half_round sum) (hb_ref_cube mode) (hb_ref_three mode))
    (hbs_inverse_cap mode) 6 _ hi hs; first trivial.
  split; first exact (hsn_newton_canonical (hb_half_round sum) (hb_ref_cube mode) (hb_ref_three mode)).
  move: hf; rewrite /hsn_state /hb_newton; smt().
qed.

lemma hbs_safe_newton_total (mode : int) (sum : hb_fp) :
  phoare [HB._fixpoint_newton_invsqrt :
    xhalfp = hb_pack (hb_half_round sum) /\
    start_cubep = hb_pack (hb_ref_cube mode) /\
    start_threep = hb_pack (hb_ref_three mode) /\ hbs_good mode sum ==>
    hbs_canonical (hb_load res) /\ 0 <= hb_value (hb_load res) <= hbs_inverse_cap mode] = 1%r.
proof.
  conseq hb_newton_ll (hb_newton_correct (hb_pack (hb_half_round sum))
    (hb_pack (hb_ref_cube mode)) (hb_pack (hb_ref_three mode))) => //.
  move=> &m hpre result.
  have hg : hbs_good mode sum by smt().
  have h := hbs_safe_newton mode sum hg.
  rewrite !hb_load_pack; smt(hb_load_pack).
qed.
