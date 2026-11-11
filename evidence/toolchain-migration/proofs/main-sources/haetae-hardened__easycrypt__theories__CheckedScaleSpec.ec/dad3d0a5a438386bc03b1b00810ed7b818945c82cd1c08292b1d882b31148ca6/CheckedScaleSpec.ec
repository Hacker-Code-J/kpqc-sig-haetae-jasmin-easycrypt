require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import HyperballFixedPointSpec.

(* The earlier multiplication keeps the baseline word semantics. Only the
   final rounding is interpreted without its old 64-bit addition wrap. *)
op hcs_product (sample : W64.t) (scale : hb_fp) : hb_fp =
  hb_mul ((sample `&` W64.of_int 4294967295) `<<<` 16, sample `>>>` 32) scale.

op hcs_round_word (high : W64.t) : W64.t =
  (high `>>>` 15) + ((high `>>>` 14) `&` W64.one).

op hcs_wide_magnitude (sample : W64.t) (scale : hb_fp) : int =
  (W64.to_uint (hcs_product sample scale).`2 + 16384) %/ 32768.

op hcs_magnitude_word (sample : W64.t) (scale : hb_fp) : W64.t =
  hcs_round_word (hcs_product sample scale).`2.

op hcs_badmask (sample : W64.t) (scale : hb_fp) : W64.t =
  if hcs_wide_magnitude sample scale <= 2147483647 then W64.zero else W64.onew.

op hcs_coefficient (sample : W64.t) (scale : hb_fp) (sign : W64.t) : W32.t =
  truncateu32 ((hcs_magnitude_word sample scale `^` (W64.zero-sign)) + sign).

op hcs_scalar (sample : W64.t) (scale : hb_fp) (sign : W64.t) : W32.t * W64.t =
  (hcs_coefficient sample scale sign, hcs_badmask sample scale).

op hcs_scale_sample (sample : W64.t) (scale : BArray16.t) (sign : W8.t) : W32.t * W64.t =
  hcs_scalar sample (hb_load scale) (zeroextu64 sign).
