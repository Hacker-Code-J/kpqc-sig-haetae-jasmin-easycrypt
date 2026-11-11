require import AllCore IntDiv RealExp RealSeries Distr StdOrder.

(* Independent discrete Gaussian on every integer. The denominator is
   2*(2^76)^2=2^153. No CDT table, acceptance program or machine word
   defines this target or its normalizing constant. *)
op g76_denominator : int = 11417981541647679048466287755595961091061972992.

op [opaque] g76_rho (k : int) : real =
  RealExp.exp (-(k*k)%r / g76_denominator%r).

op [opaque] g76_half_rho (k : int) : real =
  if 0 <= k then g76_rho k else 0%r.

op [opaque] g76_normalizer : real = RealSeries.sum g76_rho.
op [opaque] g76_pmf (k : int) : real = g76_rho k / g76_normalizer.
op [opaque] g76_distr : int distr = Distr.mk g76_pmf.

(* Integer rounding is unbounded, including every tail value. *)
op [opaque] g76_round_magnitude (z : int) : int = (z + 32768) %/ 65536.
op [opaque] g76_round_absolute (k : int) : int = g76_round_magnitude (`|k|).
op [opaque] g76_rounded : int distr = dmap g76_distr g76_round_absolute.

(* The folded signed Gaussian counts zero once and every positive
   magnitude twice. The acceptance weight is one half of that weight. *)
op [opaque] g76_fold_weight (z : int) : real =
  if 0 <= z then (if z = 0 then 1%r else 2%r) * g76_rho z else 0%r.

op [opaque] g76_accept_weight (z : int) : real =
  if 0 <= z then (if z = 0 then 1%r/2%r else 1%r) * g76_rho z else 0%r.
