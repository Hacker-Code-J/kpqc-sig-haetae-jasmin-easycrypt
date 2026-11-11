require import AllCore Real RealExp Distr.

op grn_delta : real = 1%r/549755813888%r.
op grn_epsilon : real = 1%r/295147905179352825856%r.

op grn_likelihood ['a] (p q : 'a distr) (x : 'a) : real = mu1 p x / mu1 q x.

op grn_mass_bounds ['a] (p q : 'a distr) : bool =
  forall x, (1%r-grn_delta)*mu1 q x <= mu1 p x <= (1%r+grn_delta)*mu1 q x.

(* Real-valued finite-support definition. The public theorems establish
   support inclusion and integrability before using this non-logarithmic
   Renyi quantity; no extended-infinity convention is encoded here. *)
op grn_moment ['a] (order : int) (p q : 'a distr) : real =
  E q (fun x => (grn_likelihood p q x)^order).

op grn_renyi ['a] (order : int) (p q : 'a distr) : real =
  (grn_moment order p q) ^ (1%r/(order-1)%r).
