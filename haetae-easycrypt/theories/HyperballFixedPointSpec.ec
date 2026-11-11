require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import BArray16 SigmaSpec.

type hb_fp = W64.t * W64.t.
op hb_load (p : BArray16.t) : hb_fp = (BArray16.get64 p 0, BArray16.get64 p 1).
op hb_store (p : BArray16.t) (x : hb_fp) : BArray16.t =
  BArray16.set64 (BArray16.set64 p 0 x.`1) 1 x.`2.
op hb_pack (x : hb_fp) : BArray16.t = hb_store witness x.
op hb_value (x : hb_fp) : int = W64.to_uint x.`1 + 281474976710656 * W64.to_uint x.`2.

op hb_norm (x : hb_fp) : hb_fp =
  (x.`1 `&` W64.of_int 281474976710655, x.`2 + (x.`1 `>>>` 48)).
op hb_cneg (x : hb_fp) (sign : W64.t) : hb_fp =
  let mask = W64.zero - sign in
  hb_norm (((mask `&` W64.of_int 281474976710655) `^` x.`1) + sign, x.`2 `^` mask).
op hb_sub (x y : hb_fp) : hb_fp =
  let neg = hb_cneg y W64.one in (x.`1 + neg.`1, x.`2 + neg.`2).
op hb_threehalves_minus (x : hb_fp) : hb_fp =
  let neg = hb_cneg x W64.one in
  hb_norm (neg.`1, neg.`2 + (W64.of_int 3 `<<<` 27)).

(* Exact fixed-point word arithmetic, retaining both rounding stages and all
   truncations. These operations do not assert absence of intermediate wrap. *)
op hb_mul (x y : hb_fp) : hb_fp =
  let a = mul48_word x.`1 y.`1 in
  let b = mul48_word x.`1 y.`2 in
  let c = mul48_word x.`2 y.`1 in
  let d = mulu_64 x.`2 y.`2 in
  let r0 = a.`2 + (((a.`1 `>>>` 47) + W64.one) `>>>` 1) + b.`1 + c.`1 +
    (W64.one `<<<` 27) in
  let r1 = b.`2 + c.`2 in
  let s0 = (r0 `>>>` 28) + ((r1 `<<<` 20) `&` W64.of_int 281474976710655) +
    ((d.`2 `<<<` 20) `&` W64.of_int 281474976710655) in
  let s1 = (r1 `>>>` 28) + ((d.`2 `>>>` 28) + (d.`1 `<<<` 36)) in
  hb_norm (s0, s1).
op hb_square (x : hb_fp) : hb_fp = square_word x.`1 x.`2.
op hb_signed_mul (xy y : hb_fp) : hb_fp =
  let sign = (y.`2 `>>>` 63) `&` W64.one in
  hb_cneg (hb_mul (hb_cneg y sign) xy) sign.
op hb_mul_high (x : hb_fp) (y : W64.t) : hb_fp =
  let a = mul48_word x.`1 y in
  let b = mul48_word x.`2 y in
  let hi = a.`2 + b.`1 in
  hb_norm (((a.`1 + (W64.one `<<<` 27)) `>>>` 28) +
    ((hi `<<<` 20) `&` W64.of_int 281474976710655),
    (hi `>>>` 28) + (b.`2 `<<<` 20)).
op hb_half_round (x : hb_fp) : hb_fp =
  hb_norm (((x.`1 + W64.one) `>>>` 1) +
    ((x.`2 `&` W64.one) `<<<` 47), x.`2 `>>>` 1).
op hb_mul_rnd13 (sample : W64.t) (scale : hb_fp) (sign : W64.t) : W32.t =
  let x = ((sample `&` W64.of_int 4294967295) `<<<` 16, sample `>>>` 32) in
  let r = hb_mul x scale in
  let rounded = (r.`2 + W64.of_int 16384) `>>>` 15 in
  truncateu32 ((rounded `^` (W64.zero - sign)) + sign).
op hb_scale_sample (sample : W64.t) (scale : BArray16.t) (sign : W8.t) : W32.t =
  hb_mul_rnd13 sample (hb_load scale) (zeroextu64 sign).

(* The integer magnitude after the implemented word rounding. It does not
   replace hb_mul by an ideal real multiplication. *)
op hb_rnd13_magnitude (sample : W64.t) (scale : hb_fp) : int =
  let x = ((sample `&` W64.of_int 4294967295) `<<<` 16, sample `>>>` 32) in
  W64.to_uint (((hb_mul x scale).`2 + W64.of_int 16384) `>>>` 15).

op hb_newton_initial (half cube three : hb_fp) : hb_fp = hb_sub three (hb_mul half cube).
op hb_newton_step (half inv : hb_fp) : hb_fp =
  hb_signed_mul inv (hb_threehalves_minus (hb_mul half (hb_square inv))).
op hb_newton_iter (half start : hb_fp) (k : int) : hb_fp =
  foldl (fun (inv : hb_fp) (_ : int) => hb_newton_step half inv) start (iota_ 0 k).
op hb_newton (half cube three : hb_fp) : hb_fp =
  hb_newton_iter half (hb_newton_initial half cube three) 6.
op hb_scale_factor (sum cube three : hb_fp) (scale_const : W64.t) : hb_fp =
  hb_mul_high (hb_newton (hb_half_round sum) cube three) scale_const.
