require import AllCore IntDiv Real RealExp.
from Jasmin require import JModel_x86.
require import SigmaSpec CDTCorrectness.

(* The unrounded candidate uses the 72 noise bits and the independent CDT
   integer. These mathematical quantities do not depend on the word square or
   the approximate exponential evaluator. *)
op sr_scale : int = 281474976710656.
op sr_noise_modulus : int = 4722366482869645213696.

op [opaque] sr_noise (p : BArray26.t) : int =
  W64.to_uint (le6_word p 17) + sr_scale * W64.to_uint (le3_word p 23).

op [opaque] sr_cdt (p : BArray26.t) : int =
  cdt_count (cdt_lo_input p) (cdt_hi_input p) 166.

op [opaque] sr_candidate (p : BArray26.t) : int =
  sr_noise p + sr_noise_modulus * sr_cdt p.

op [opaque] sr_numerator (p : BArray26.t) : int =
  sr_noise p * (sr_noise p + 2 * sr_noise_modulus * sr_cdt p).

op [opaque] sr_exponent (p : BArray26.t) : real =
  (sr_numerator p)%r / 11417981541647679048466287755595961091061972992%r.

op [opaque] sr_raw_factor (p : BArray26.t) : real =
  if sr_candidate p = 0 then 1%r / 2%r else 1%r.

op [opaque] sr_acceptance_target (p : BArray26.t) : real =
  sr_raw_factor p * RealExp.exp (-sr_exponent p).

op [opaque] sr_zero_mismatch (p : BArray26.t) : bool =
  sr_cdt p = 0 /\ 1 <= sr_noise p < 32768.
