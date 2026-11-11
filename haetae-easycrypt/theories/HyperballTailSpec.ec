require import AllCore Real RealExp.
require import GaussianPayloadSpec HyperballIidPayloadSpec.

(* Explicit iid-byte model. The raw-square accumulator includes both dummies. *)
op ht_q : int = 75557863725914323419136.
op ht_mode mode : bool = hip_mode mode.
op ht_count mode : int = hip_total mode.
op ht_tplus : real = 19%r / 200%r.
op ht_tminus : real = 15%r / 98%r.
op ht_mplus : real = 10%r / 9%r + 1%r / 262144%r.
op ht_mminus : real = 7%r / 8%r + 1%r / 262144%r.
op ht_rplus : real = 3947%r / 4000%r.
op ht_rminus : real = 1963%r / 2000%r.
op ht_eta : real = 1%r / 8796093022208%r.
op ht_cap : real = 4194304%r.
op ht_epsilon mode : real =
  if mode=2 then 1%r / 536870912%r
  else if mode=3 then 1%r / 17592186044416%r
  else if mode=5 then 1%r / 18014398509481984%r
  else 0%r.

op ht_raw_square code : real = (gpd_square code)%r / ht_q%r.
op ht_weight_plus code : real = RealExp.exp (ht_tplus * ht_raw_square code).
op ht_weight_minus code : real = RealExp.exp (-ht_tminus * ht_raw_square code).
op ht_centered_plus code : real = RealExp.exp (ht_tplus * (ht_raw_square code-5%r/4%r)).
op ht_centered_minus code : real = RealExp.exp (ht_tminus * (3%r/4%r-ht_raw_square code)).
