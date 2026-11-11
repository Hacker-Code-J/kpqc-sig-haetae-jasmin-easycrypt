require import AllCore IntDiv List StdRing StdOrder StdBigop.
require import RealExp RealSeries Distr.

theory HalfGaussianSpec.

(* The nonnegative discrete Gaussian of sigma 16 has 2*sigma^2 = 512.
   These definitions do not refer to the CDT table or to executable code. *)
op hg16_q : real = RealExp.exp (-1%r / 512%r).

op hg16_rho (k : int) : real =
  if 0 <= k then RealExp.exp (-(k*k)%r / 512%r) else 0%r.

op hg16_normalizer : real = RealSeries.sum hg16_rho.

(* N is an exclusive upper bound: this contains the terms 0,...,N-1. *)
op hg16_partial (N : int) : real =
  Bigreal.BRA.bigi predT hg16_rho 0 N.

op hg16_tail (N : int) : real =
  RealSeries.sum (fun k => if N <= k then hg16_rho k else 0%r).

op hg16_tail_bound (N : int) : real =
  hg16_rho N / (1%r - hg16_q ^ (2*N+1)).

op hg16_pmf (k : int) : real = hg16_rho k / hg16_normalizer.
op hg16_distr : int distr = Distr.mk hg16_pmf.
op hg16_cdf (k : int) : real = mu hg16_distr (fun x => x <= k).

end HalfGaussianSpec.
