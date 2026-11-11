require import AllCore IntDiv.
from Jasmin require import JModel_x86.

(* The exact 64-bit evaluator, with arithmetic shifts, an unsigned double
   product, and the carry implementing rounding toward positive infinity. *)
op smulh48_word (a b : W64.t) : W64.t =
  let p = mulu_64 a b in
  let hi = p.`1 - ((a `|>>>` 63) `&` b) in
  let lo = p.`2 in
  let rem = lo `&` W64.of_int 281474976710655 in
  ((hi `<<<` 16) `|` (lo `>>>` 48)) +
    ((rem `|` (W64.zero - rem)) `>>>` 63).

(* Integer reference: ceil(signed(a) * unsigned(b) / 2^48). *)
op smulh48_ceil (a b : W64.t) : int =
  let p = W64.to_sint a * W64.to_uint b in
  p %/ 281474976710656 + b2i (p %% 281474976710656 <> 0).

(* HAETAE-1.2.0's degree-10 polynomial, evaluated using its specified
   fixed-point multiply and word arithmetic. This does not assert a real
   exponential approximation bound or absence of intermediate overflow. *)
op approx_exp_word (x : W64.t) : W64.t =
  let r0 = W64.of_int 55868746 in
  let r1 = smulh48_word r0 x - W64.of_int 743564434 in
  let r2 = smulh48_word r1 x + W64.of_int 6953427278 in
  let r3 = smulh48_word r2 x - W64.of_int 55833338892 in
  let r4 = smulh48_word r3 x + W64.of_int 390932311155 in
  let r5 = smulh48_word r4 x - W64.of_int 2345623661771 in
  let r6 = smulh48_word r5 x + W64.of_int 11728123872951 in
  let r7 = smulh48_word r6 x - W64.of_int 46912496106200 in
  let r8 = smulh48_word r7 x + W64.of_int 140737488354861 in
  let r9 = smulh48_word r8 x - W64.of_int 281474976710650 in
  smulh48_word r9 x + W64.of_int 281474976710657.
