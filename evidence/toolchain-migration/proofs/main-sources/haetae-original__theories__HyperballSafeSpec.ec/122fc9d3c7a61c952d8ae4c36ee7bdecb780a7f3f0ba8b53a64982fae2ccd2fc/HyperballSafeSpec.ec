require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import HyperballFixedPointSpec HyperballReferenceConstants.

(* Fixed-point values use Q=2^76 and radix R=2^48. The safe input interval
   concerns the accumulated raw square limbs, including both dummy events. *)
op hbs_q : int = 75557863725914323419136.
op hbs_radix : int = 281474976710656.
op hbs_operand_cap : int = 309485009821345068724781056.
op hbs_scale_cap : int = 38685626227668133590597632.
op hbs_coefficient_cap : int = 67108864.

op hbs_mode (mode : int) : bool = mode=2 \/ mode=3 \/ mode=5.
op hbs_events mode : int = 256*(hb_ref_l mode+hb_ref_k mode)+2.
op hbs_sum_min mode : int = 3*hbs_events mode*18889465931478580854784.
op hbs_sum_max mode : int = 5*hbs_events mode*18889465931478580854784.
op hbs_half_min mode : int = hbs_sum_min mode %/ 2.
op hbs_half_max mode : int = (hbs_sum_max mode+1) %/ 2.
op hbs_inverse_cap (mode : int) : int =
  if mode=2 then 2361183241434822606848
  else if mode=3 then 2066035336255469780992
  else if mode=5 then 1697100454781278748672
  else 0.

op hbs_canonical (x : hb_fp) : bool = W64.to_uint x.`1 < hbs_radix.
op hbs_operand (x : hb_fp) : bool =
  W64.to_uint x.`1 < 2*hbs_radix /\ hb_value x <= hbs_operand_cap.

(* This predicate contains only input mode, representation and square-sum
   bounds. It contains no assumed inverse, scaled coefficient or output norm. *)
op hbs_good (mode : int) (sum : hb_fp) : bool =
  hbs_mode mode /\ hbs_canonical sum /\
  hbs_sum_min mode <= hb_value sum <= hbs_sum_max mode.
