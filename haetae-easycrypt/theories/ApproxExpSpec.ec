require import AllCore IntDiv List Real.
from Jasmin require import JModel_x86.
require import ReferenceConstants.

op ae_scale : int = 281474976710656.
op ae_bound : int = 844424930131974.
op ae_domain (x : int) : bool = 0 <= x /\ 3*x <= 2*ae_scale.
op [opaque] ae_coefficients : int list = reference_exp_coefficients.
op [opaque] ae_leading : int = head 0 ae_coefficients.
op [opaque] ae_tail : int list = behead ae_coefficients.
op ae_coefficient_ok (c : int) : bool = -(ae_scale+1) <= c <= ae_scale+1.

(* Ceiling division is valid for negative products as well: the denominator
   is positive and the integer quotient uses Euclidean division. *)
op [opaque] ae_ceil (a x : int) : int = (a*x+ae_scale-1) %/ ae_scale.
op [opaque] ae_integer_fold (x a : int) (cs : int list) : int =
  foldl (fun r c => ae_ceil r x + c) a cs.
op [opaque] ae_real_fold (z r : real) (cs : int list) : real =
  foldl (fun v c => v*z+c%r) r cs.
op [opaque] ae_integer (x : int) : int = ae_integer_fold x ae_leading ae_tail.
op [opaque] ae_polynomial (z : real) : real =
  ae_real_fold z ae_leading%r ae_tail / ae_scale%r.

(* The multiplication argument keeps the coefficient-provenance proof
   independent of any machine-word multiplication implementation. *)
op [opaque] ae_word_fold (mul : W64.t -> W64.t -> W64.t)
    (x r : W64.t) (cs : int list) : W64.t =
  foldl (fun v c => mul v x + W64.of_int c) r cs.
