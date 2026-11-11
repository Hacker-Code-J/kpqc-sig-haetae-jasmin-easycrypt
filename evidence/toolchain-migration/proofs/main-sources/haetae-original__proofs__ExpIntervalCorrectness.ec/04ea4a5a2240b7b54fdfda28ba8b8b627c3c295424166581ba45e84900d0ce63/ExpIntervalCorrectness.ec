require import AllCore IntDiv List Real RealExp StdOrder.
require import ExpIntervalSpec.
import RField RealOrder.

lemma ei_pow2_double n v : 0 <= n => Ring.IntID.exp 2 n = v =>
  Ring.IntID.exp 2 (n+n) = v*v.
proof. by move=> hn hv; rewrite Ring.IntID.exprD_nneg // !hv. qed.

lemma ei_pow2_1 : Ring.IntID.exp 2 1 = 2.
proof. by rewrite Ring.IntID.expr1. qed.

lemma ei_pow2_2 : Ring.IntID.exp 2 2 = 4.
proof.
  have h := ei_pow2_double 1 2 _ ei_pow2_1; first trivial.
  by move: h; rewrite /=.
qed.

lemma ei_pow2_4 : Ring.IntID.exp 2 4 = 16.
proof.
  have h := ei_pow2_double 2 4 _ ei_pow2_2; first trivial.
  by move: h; rewrite /=.
qed.

lemma ei_pow2_8 : Ring.IntID.exp 2 8 = 256.
proof.
  have h := ei_pow2_double 4 16 _ ei_pow2_4; first trivial.
  by move: h; rewrite /=.
qed.

lemma ei_pow2_16 : Ring.IntID.exp 2 16 = 65536.
proof.
  have h := ei_pow2_double 8 256 _ ei_pow2_8; first trivial.
  by move: h; rewrite /=.
qed.

lemma ei_pow2_32 : Ring.IntID.exp 2 32 = 4294967296.
proof.
  have h := ei_pow2_double 16 65536 _ ei_pow2_16; first trivial.
  by move: h; rewrite /=.
qed.

lemma ei_pow2_64 : Ring.IntID.exp 2 64 = 18446744073709551616.
proof.
  have h := ei_pow2_double 32 4294967296 _ ei_pow2_32; first trivial.
  by move: h; rewrite /=.
qed.

lemma ei_pow2_128 : Ring.IntID.exp 2 128 = 340282366920938463463374607431768211456.
proof.
  have h := ei_pow2_double 64 18446744073709551616 _ ei_pow2_64; first trivial.
  by move: h; rewrite /=.
qed.

lemma ei_pow2_256 : Ring.IntID.exp 2 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936.
proof.
  have h := ei_pow2_double 128 340282366920938463463374607431768211456 _ ei_pow2_128; first trivial.
  by move: h; rewrite /=.
qed.

lemma ei_pow2_137 : Ring.IntID.exp 2 137 = 174224571863520493293247799005065324265472.
proof.
  by rewrite (Ring.IntID.exprD_nneg 2 128 9) 1,2://
    (Ring.IntID.exprD_nneg 2 8 1) 1,2:// ei_pow2_128 ei_pow2_8 ei_pow2_1 /=.
qed.

lemma ei_pow2_320 : Ring.IntID.exp 2 320 = 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576.
proof.
  by rewrite (Ring.IntID.exprD_nneg 2 256 64) 1,2:// ei_pow2_256 ei_pow2_64 /=.
qed.


(* Analytic inputs are the installed RealExp theory: exp0, expD,
   exp_mono, exp_gt0, expK, le_ln_up and le1Dx_exp. No analytic assumption
   or externally generated certificate is added as an axiom here. *)
lemma ei_exp_reciprocal_sandwich (d : real) : 1%r < d =>
  0%r < RealExp.exp (- (1%r / d)) /\
  d - 1%r <= d * RealExp.exp (- (1%r / d)) /\
  (d + 1%r) * RealExp.exp (- (1%r / d)) <= d.
proof.
  move=> hd.
  have hd0 : d <> 0%r by smt().
  have hinv : d * (1%r / d) = 1%r by field; smt().
  have ht : 0%r <= 1%r / d by smt().
  have ha : 0%r < 1%r - 1%r / d by smt().
  have hl := le_ln_up (1%r - 1%r / d) ha.
  have hel : RealExp.exp (RealExp.ln (1%r - 1%r / d)) <= RealExp.exp (- (1%r / d)).
  + apply exp_mono; smt().
  rewrite expK 1:ha in hel.
  have hu := le1Dx_exp (1%r / d) ht.
  have hp := exp_gt0 (- (1%r / d)).
  have he : RealExp.exp (- (1%r / d)) * RealExp.exp (1%r / d) = 1%r.
  + by rewrite -expD addNr exp0.
  have hupper : RealExp.exp (- (1%r / d)) * (1%r + 1%r / d) <= 1%r by smt().
  smt().
qed.

lemma ei_exp_reciprocal_bounds (d : real) : 1%r < d =>
  1%r - 1%r / d <= RealExp.exp (- (1%r / d)) /\
  RealExp.exp (- (1%r / d)) <= d / (d + 1%r).
proof.
  move=> hd.
  have h := ei_exp_reciprocal_sandwich d hd.
  have h1 : d * (1%r / d) = 1%r by field; smt().
  have h2 : (d + 1%r) * (d / (d + 1%r)) = d by field; smt().
  smt().
qed.

lemma ei_mod_bounds D n : 0 < D => 0 <= n %% D < D.
proof.
  move=> hD.
  have h0 : 0 <= n %% D by apply modz_ge0; smt().
  have h1 := ltz_pmod n D hD; smt().
qed.

lemma ei_floor_bounds D n : 0 < D => 0 <= n =>
  0 <= n %/ D /\ D * (n %/ D) <= n.
proof.
  move=> hD hn.
  have hdiv := divz_eq n D.
  have hmod := ei_mod_bounds D n hD.
  have hq : 0 <= n %/ D by rewrite divz_ge0.
  smt().
qed.

lemma ei_ceil_bounds D n : 0 < D => 0 <= n =>
  0 <= (n + D - 1) %/ D /\ n <= D * ((n + D - 1) %/ D).
proof.
  move=> hD hn.
  have hdiv := divz_eq (n+D-1) D.
  have hmod := ei_mod_bounds D (n+D-1) hD.
  have hq : 0 <= (n+D-1) %/ D by rewrite divz_ge0; smt().
  smt().
qed.

lemma ei_contains_nonnegative D b x : ei_contains D b x =>
  0 < D /\ 0 <= b.`1 /\ 0 <= b.`2 /\ 0%r <= x.
proof.
  rewrite /ei_contains; move=> [hD [hl [hx [hlo hhi]]]].
  have hDr : 0%r < D%r by rewrite lt_fromint.
  have hbr : 0%r <= b.`2%r by smt().
  have hb : 0 <= b.`2 by move: hbr; rewrite le_fromint.
  smt().
qed.

lemma ei_contains_division D b x : ei_contains D b x =>
  b.`1%r / D%r <= x /\ x <= b.`2%r / D%r.
proof.
  rewrite /ei_contains; move=> [hD [hl [hx [hlo hhi]]]].
  have hDr : 0%r < D%r by rewrite lt_fromint.
  have h1 : D%r * (b.`1%r / D%r) = b.`1%r by field; smt().
  have h2 : D%r * (b.`2%r / D%r) = b.`2%r by field; smt().
  smt().
qed.

lemma ei_mul_real_core (s l1 u1 l2 u2 l u x y : real) :
  0%r < s => 0%r <= l1 => 0%r <= l2 => 0%r <= x => 0%r <= y =>
  l1 <= s*x => s*x <= u1 => l2 <= s*y => s*y <= u2 =>
  s*l <= l1*l2 => u1*u2 <= s*u =>
  l <= s*(x*y) /\ s*(x*y) <= u.
proof.
  move=> hs hl1 hl2 hx hy hxl hxu hyl hyu hl hu.
  have hsx : 0%r <= s*x by smt().
  have hsy : 0%r <= s*y by smt().
  have hu1 : 0%r <= u1 by smt().
  have lo1 := RealOrder.ler_wpmul2r l2 hl2 l1 (s*x) hxl.
  have lo2 := RealOrder.ler_wpmul2l (s*x) hsx l2 (s*y) hyl.
  have hi1 := RealOrder.ler_wpmul2r (s*y) hsy (s*x) u1 hxu.
  have hi2 := RealOrder.ler_wpmul2l u1 hu1 (s*y) u2 hyu.
  have he : (s*x)*(s*y) = s*(s*(x*y)) by ring.
  have hlo : s*l <= s*(s*(x*y)) by rewrite -he; smt().
  have hhi : s*(s*(x*y)) <= s*u by rewrite -he; smt().
  move: hlo hhi; rewrite !RealOrder.ler_pmul2l 1:hs 1:hs; smt().
qed.

lemma ei_mul_sound D a b x y :
  ei_contains D a x => ei_contains D b y => ei_contains D (ei_mul D a b) (x*y).
proof.
  move=> ha hb.
  have [hD [ha0 [ha1 hx]]] := ei_contains_nonnegative D a x ha.
  have [_ [hb0 [hb1 hy]]] := ei_contains_nonnegative D b y hb.
  have hlow0 : 0 <= a.`1*b.`1 by smt().
  have hhigh0 : 0 <= a.`2*b.`2 by smt().
  have [hl0 hl] := ei_floor_bounds D (a.`1*b.`1) hD hlow0.
  have [hh0 hh] := ei_ceil_bounds D (a.`2*b.`2) hD hhigh0.
  have hDr : 0%r < D%r by rewrite lt_fromint.
  have hlr : D%r * (a.`1*b.`1 %/ D)%r <= a.`1%r*b.`1%r.
  + rewrite -!fromintM le_fromint; exact hl.
  have hhr : a.`2%r*b.`2%r <= D%r * ((a.`2*b.`2+D-1) %/ D)%r.
  + rewrite -!fromintM le_fromint; exact hh.
  have har : 0%r <= a.`1%r by rewrite le_fromint.
  have hbr : 0%r <= b.`1%r by rewrite le_fromint.
  have [_ [_ [_ [hal hau]]]] := ha.
  have [_ [_ [_ [hbl hbu]]]] := hb.
  have hbnds := ei_mul_real_core D%r a.`1%r a.`2%r b.`1%r b.`2%r
    (a.`1*b.`1 %/ D)%r ((a.`2*b.`2+D-1) %/ D)%r x y
    hDr har hbr hx hy hal hau hbl hbu hlr hhr.
  have hxy : 0%r <= x*y by smt().
  rewrite /ei_contains /ei_mul /=.
  smt().
qed.

lemma ei_seed_sound D d b : ei_seed_ok D d b =>
  ei_contains D b (RealExp.exp (- (1%r / d%r))).
proof.
  rewrite /ei_seed_ok; move=> [hD [hd [hb [hlo hhi]]]].
  have hDr : 0%r < D%r by rewrite lt_fromint.
  have hdr : 1%r < d%r by rewrite lt_fromint.
  have [hx [hl hu]] := ei_exp_reciprocal_sandwich d%r hdr.
  have hlr : b.`1%r*d%r <= D%r*(d%r-1%r).
  + rewrite -fromintB -!fromintM le_fromint; exact hlo.
  have hur : D%r*d%r <= b.`2%r*(d%r+1%r).
  + rewrite -fromintD -!fromintM le_fromint; exact hhi.
  rewrite /ei_contains; smt().
qed.

lemma ei_square_steps_sound D (steps : ei_interval list) :
  forall current r,
  ei_contains D current (RealExp.exp r) => ei_square_steps_check D current steps =>
  ei_contains D (last current steps)
    (RealExp.exp ((Ring.IntID.exp 2 (size steps))%r * r)).
proof.
  elim: steps => [|next tail ih] current r hc hcheck.
  + by rewrite /= Ring.IntID.expr0 /=.
  have [he ht] : next = ei_mul D current current /\ ei_square_steps_check D next tail
    by move: hcheck; rewrite /=.
  have hnext : ei_contains D next (RealExp.exp (r+r)).
  + rewrite he expD; exact (ei_mul_sound D current current (RealExp.exp r) (RealExp.exp r) hc hc).
  have hrec := ih next (r+r) hnext ht.
  have hlen : 1 + size tail = size tail + 1 by ring.
  have hexp : (Ring.IntID.exp 2 (1 + size tail))%r * r =
      (Ring.IntID.exp 2 (size tail))%r * (r+r).
  + rewrite hlen Ring.IntID.exprS 1:size_ge0 fromintM; ring.
  by rewrite /= hexp.
qed.

lemma ei_q_exponent :
  (Ring.IntID.exp 2 128)%r * (-(1%r / (Ring.IntID.exp 2 137)%r)) = -(1%r / 512%r).
proof. rewrite ei_pow2_128 ei_pow2_137; field; smt(). qed.

lemma ei_square_q_sound D (chain : ei_interval list) :
  ei_seed_ok D (Ring.IntID.exp 2 137) (head witness chain) =>
  ei_square_check D chain => size chain = 129 =>
  ei_contains D (last witness chain) (RealExp.exp (-(1%r / 512%r))).
proof.
  case: chain => [|b0 rest].
  + by rewrite /ei_square_check.
  move=> hseed hcheck hsize.
  have hfirst := ei_seed_sound D (Ring.IntID.exp 2 137) b0 hseed.
  have hlen : size rest = 128 by move: hsize; rewrite /=; smt().
  have h := ei_square_steps_sound D rest b0
    (-(1%r / (Ring.IntID.exp 2 137)%r)) hfirst hcheck.
  move: h; rewrite hlen ei_q_exponent /=.
  trivial.
qed.

lemma ei_weight_powers_step (x : real) (k : int) : 0 <= k =>
  RField.exp x (k*k) * RField.exp x (2*k+1) = RField.exp x ((k+1)*(k+1)) /\
  RField.exp x (2*k+1) * (x*x) = RField.exp x (2*(k+1)+1).
proof.
  move=> hk; split.
  + rewrite -RField.exprD_nneg 1:/# 1:/#; congr; ring.
  rewrite -RField.expr2 -RField.exprD_nneg 1:/# 1://; congr; ring.
qed.

lemma ei_exp_power (r : real) (n : int) : 0 <= n =>
  RField.exp (RealExp.exp r) n = RealExp.exp (n%r * r).
proof.
  move=> hn; elim: n hn => [|n hn ih].
  + by rewrite RField.expr0 /= exp0.
  rewrite RField.exprS 1:hn ih -expD fromintD /=; congr; ring.
qed.

lemma ei_q_power (n : int) : 0 <= n =>
  RField.exp (RealExp.exp (-(1%r/512%r))) n = RealExp.exp (-(n%r/512%r)).
proof. move=> hn; rewrite ei_exp_power 1:hn; congr; field; smt(). qed.

lemma ei_weight_step_sound D q2 (state : ei_weight_state) x k :
  0 <= k => ei_contains D q2 (x*x) =>
  ei_contains D state.`1 (RField.exp x (k*k)) =>
  ei_contains D state.`2 (RField.exp x (2*k+1)) =>
  ei_contains D (ei_weight_step D q2 state).`1 (RField.exp x ((k+1)*(k+1))) /\
  ei_contains D (ei_weight_step D q2 state).`2 (RField.exp x (2*(k+1)+1)).
proof.
  move=> hk hq2 hw hr.
  have hwp := ei_mul_sound D state.`1 state.`2
    (RField.exp x (k*k)) (RField.exp x (2*k+1)) hw hr.
  have hrp := ei_mul_sound D state.`2 q2 (RField.exp x (2*k+1)) (x*x) hr hq2.
  have [hew her] := ei_weight_powers_step x k hk.
  move: hwp hrp; rewrite hew her /ei_weight_step /=; smt().
qed.

lemma ei_weight_steps_sound D q2 (steps : ei_weight_state list) :
  forall (current : ei_weight_state) (x : real) (k : int),
  0 <= k => ei_contains D q2 (x*x) =>
  ei_contains D current.`1 (RField.exp x (k*k)) =>
  ei_contains D current.`2 (RField.exp x (2*k+1)) =>
  ei_weight_steps_check D q2 current steps =>
  forall j, 0 <= j < 1 + size steps =>
    ei_contains D (nth witness (current::steps) j).`1 (RField.exp x ((k+j)*(k+j))) /\
    ei_contains D (nth witness (current::steps) j).`2 (RField.exp x (2*(k+j)+1)).
proof.
  elim: steps => [|next tail ih] current x k hk hq2 hw hr hc j hj.
  + have -> : j = 0 by move: hj; rewrite /=; smt().
    by rewrite /=.
  have [he ht] : next = ei_weight_step D q2 current /\ ei_weight_steps_check D q2 next tail
    by move: hc; rewrite /=.
  case (j=0) => hj0.
  + by rewrite hj0 /=.
  have [hnw hnr] := ei_weight_step_sound D q2 current x k hk hq2 hw hr.
  rewrite -he in hnw.
  rewrite -he in hnr.
  have hk1 : 0 <= k+1 by smt().
  have hj1 : 0 <= j-1 < 1+size tail by move: hj; rewrite /=; smt().
  have h := ih next x (k+1) hk1 hq2 hnw hnr ht (j-1) hj1.
  have hindex : k+1+(j-1) = k+j by ring.
  move: h; rewrite hindex /= hj0.
  trivial.
qed.

lemma ei_contains_one D : 0 < D => ei_contains D (D,D) 1%r.
proof. rewrite /ei_contains /=; smt(). qed.

lemma ei_weights_sound D q (chain : ei_weight_state list) (x : real) :
  ei_contains D q x => ei_weights_check D q chain =>
  forall k, 0 <= k < size chain =>
    ei_contains D (nth witness chain k).`1 (RField.exp x (k*k)) /\
    ei_contains D (nth witness chain k).`2 (RField.exp x (2*k+1)).
proof.
  move=> hq; case: chain => [|b0 rest].
  + by rewrite /ei_weights_check.
  rewrite /ei_weights_check; move=> [hfirst hcheck] k hk.
  have hD : 0 < D by move: hq; rewrite /ei_contains; smt().
  have hone := ei_contains_one D hD.
  have hq2 := ei_mul_sound D q q x x hq hq.
  have hw : ei_contains D b0.`1 (RField.exp x (0*0)).
  + by rewrite hfirst /= RField.expr0.
  have hr : ei_contains D b0.`2 (RField.exp x (2*0+1)).
  + by rewrite hfirst /= RField.expr1.
  have h := ei_weight_steps_sound D (ei_mul D q q) rest b0 x 0 _ hq2 hw hr hcheck k hk;
    first trivial.
  by move: h; rewrite /=.
qed.
