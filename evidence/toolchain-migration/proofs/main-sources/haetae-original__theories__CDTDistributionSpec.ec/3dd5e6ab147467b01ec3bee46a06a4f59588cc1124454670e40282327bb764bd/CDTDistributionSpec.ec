require import AllCore List Distr DInterval.

(* A mathematical inverse CDF on a finite uniform integer sample space.
   The comparison is strict: a threshold equal to u is not counted. *)
op cdt_rank (thresholds : int list) (u : int) : int =
  count (fun t => t < u) thresholds.

op cdt_valid (modulus : int) (thresholds : int list) : bool =
  0 < modulus /\ sorted (<=) thresholds /\
  all (fun t => 0 <= t < modulus) thresholds.

(* Half-open bins. The +1 terms retain the threshold-equality case. *)
op cdt_bin_lower (thresholds : int list) (k : int) : int =
  if k = 0 then 0 else nth 0 thresholds (k - 1) + 1.

op cdt_bin_upper (modulus : int) (thresholds : int list) (k : int) : int =
  if k = size thresholds then modulus else nth 0 thresholds k + 1.

op cdt_bin_mass (modulus : int) (thresholds : int list) (k : int) : real =
  if 0 <= k <= size thresholds then
    (cdt_bin_upper modulus thresholds k - cdt_bin_lower thresholds k)%r / modulus%r
  else 0%r.

op cdt_distribution (modulus : int) (thresholds : int list) : int distr =
  dmap (dinter 0 (modulus - 1)) (cdt_rank thresholds).

(* This is an explicit uniform-input experiment. It makes no assertion
   that a concrete deterministic byte stream has a uniform distribution. *)
module UniformCDT = {
  proc sample(modulus : int, thresholds : int list) : int = {
    var u;
    u <$ dinter 0 (modulus - 1);
    return cdt_rank thresholds u;
  }
}.
