require import AllCore IntDiv StdRing StdOrder RealExp.
require import ExpIntervalCorrectness.
import RField RealOrder.

theory ExponentialGridComparison.

(* A single comparison step. In particular, the lower approximation need
   not be nonnegative; only the reference value x is multiplied as a
   nonnegative quantity in the exponential-ratio inequalities. *)
lemma eg_comparison_step (m x r lo hi lonext hinext : real) :
  1%r < m => 0%r <= x =>
  m-1%r <= m*r => (m+1%r)*r <= m =>
  lo <= x <= hi =>
  m*lonext <= (m-1%r)*lo => m*hi <= (m+1%r)*hinext =>
  lonext <= x*r <= hinext.
proof.
  move=> hm hx hrl hrh [hlo hhi] hln hhn.
  have hm0 : 0%r <= m by smt().
  have hm1 : 0%r <= m-1%r by smt().
  have hl1 := ler_wpmul2l (m-1%r) hm1 lo x hlo.
  have hl2 := ler_wpmul2r x hx (m-1%r) (m*r) hrl.
  have hh1 := ler_wpmul2r x hx ((m+1%r)*r) m hrh.
  have hh2 := ler_wpmul2l m hm0 x hi hhi.
  have hl : m*lonext <= m*(x*r) by smt().
  have hh : (m+1%r)*(x*r) <= (m+1%r)*hinext by smt().
  have hml : 0%r < m by smt().
  have hmh : 0%r < m+1%r by smt().
  move: hl hh; rewrite !ler_pmul2l //; smt().
qed.

lemma eg_exp_grid_successor (M i : int) :
  RealExp.exp (-((i+1)%r/M%r)) =
    RealExp.exp (-(i%r/M%r)) * RealExp.exp (-(1%r/M%r)).
proof.
  rewrite -RealExp.expD; congr; rewrite fromintD; ring.
qed.

(* The recurrence conditions are separate certificate obligations. This
   theorem quantifies over the finite integer interval and proves its
   conclusion by induction; it never enumerates the grid. *)
lemma eg_exp_grid_bounds (M L : int) (P : real -> real) (E : real) :
  1 < M => 0 <= L => 0%r <= E =>
  P 0%r - E <= 1%r <= P 0%r + E =>
  (forall i, 0 <= i < L =>
    M%r * (P (i%r/M%r) + E) <=
      (M+1)%r * (P ((i+1)%r/M%r) + E)) =>
  (forall i, 0 <= i < L =>
    M%r * (P ((i+1)%r/M%r) - E) <=
      (M-1)%r * (P (i%r/M%r) - E)) =>
  forall i, 0 <= i <= L =>
    P (i%r/M%r) - E <= RealExp.exp (-(i%r/M%r)) <= P (i%r/M%r) + E.
proof.
  move=> hM hL hE h0 hupper hlower i [hi0 hiL].
  have hm : 1%r < M%r by rewrite lt_fromint.
  have [hrpos [hrlo hrhi]] := ei_exp_reciprocal_sandwich M%r hm.
  move: hiL; elim: i hi0 => [|i hi0 ih] hiL.
  + by rewrite /= RealExp.exp0.
  have hilt : 0 <= i < L by smt().
  have hb := ih _; first smt().
  have hup := hupper i hilt.
  have hlo := hlower i hilt.
  rewrite fromintD in hup.
  rewrite fromintB in hlo.
  have hx : 0%r <= RealExp.exp (-(i%r/M%r)) by
    exact (ltrW _ _ (RealExp.exp_gt0 _)).
  have h := eg_comparison_step M%r (RealExp.exp (-(i%r/M%r)))
    (RealExp.exp (-(1%r/M%r))) (P (i%r/M%r)-E) (P (i%r/M%r)+E)
    (P ((i+1)%r/M%r)-E) (P ((i+1)%r/M%r)+E)
    hm hx hrlo hrhi hb hlo hup.
  by rewrite eg_exp_grid_successor.
qed.

lemma eg_exp_grid_abs (M L : int) (P : real -> real) (E : real) :
  1 < M => 0 <= L => 0%r <= E =>
  P 0%r - E <= 1%r <= P 0%r + E =>
  (forall i, 0 <= i < L =>
    M%r * (P (i%r/M%r) + E) <=
      (M+1)%r * (P ((i+1)%r/M%r) + E)) =>
  (forall i, 0 <= i < L =>
    M%r * (P ((i+1)%r/M%r) - E) <=
      (M-1)%r * (P (i%r/M%r) - E)) =>
  forall i, 0 <= i <= L =>
    `|P (i%r/M%r) - RealExp.exp (-(i%r/M%r))| <= E.
proof.
  move=> hM hL hE h0 hupper hlower i hi.
  have h := eg_exp_grid_bounds M L P E hM hL hE h0 hupper hlower i hi.
  rewrite ler_norml; smt().
qed.

end ExponentialGridComparison.
