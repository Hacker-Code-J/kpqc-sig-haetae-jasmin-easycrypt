require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import BArray26 FixedPointSpec.

(* Exact unsigned limbs of a double product, split at 48 bits. *)
op mul48_word (a b : W64.t) : W64.t * W64.t =
  let p = mulu_64 a b in
  (p.`2 `&` W64.of_int 281474976710655,
   (p.`1 `<<<` 16) `^` (p.`2 `>>>` 48)).

(* Fixed-point square from reference src/fixpoint.c, including every truncation.
   It is intentionally separate from an ideal real-valued square. *)
op square_word (x0 x1 : W64.t) : W64.t * W64.t =
  let mask = W64.of_int 281474976710655 in
  let a = mul48_word x0 x0 in
  let b = mul48_word x0 x1 in
  let c = mulu_64 x1 x1 in
  let r0 = (a.`1 `>>>` 48) + a.`2 + (b.`1 `<<<` 1) in
  let r1 = b.`2 `<<<` 1 in
  let s0 = (r0 `>>>` 28) + ((r1 `<<<` 20) `&` mask) +
           ((c.`2 `<<<` 20) `&` mask) in
  let s1 = (r1 `>>>` 28) + ((c.`2 `>>>` 28) + (c.`1 `<<<` 36)) in
  (s0 `&` mask, s1 + (s0 `>>>` 48)).

op byte_word (p : BArray26.t) (i : int) : W64.t =
  zeroextu64 (BArray26.get8 p i).

op le3_word (p : BArray26.t) (i : int) : W64.t =
  (byte_word p i `|` (byte_word p (i + 1) `<<<` 8)) `|`
  (byte_word p (i + 2) `<<<` 16).

op le6_word (p : BArray26.t) (i : int) : W64.t =
  ((le3_word p i `|` (byte_word p (i + 3) `<<<` 24)) `|`
  (byte_word p (i + 4) `<<<` 32)) `|` (byte_word p (i + 5) `<<<` 40).

op le8_word (p : BArray26.t) (i : int) : W64.t =
  (le6_word p i `|` (byte_word p (i + 6) `<<<` 48)) `|`
  (byte_word p (i + 7) `<<<` 56).

op cdt_lo_input (p : BArray26.t) : W64.t = le8_word p 0.
op cdt_hi_input (p : BArray26.t) : W32.t =
  truncateu32 (le3_word p 8 `&` W64.of_int 524287).

(* The single-attempt specification consumes all 26 input bytes:
   0..10 CDT; 11..16 rejection; 17..25 fixed-point noise. *)
op sigma_from_cdt (p : BArray26.t) (x : W64.t) :
    W64.t * W64.t * W64.t * W64.t =
  let rej = le6_word p 11 in
  let y0 = le6_word p 17 in
  let y1 = le3_word p 23 `|` (x `<<<` 24) in
  let r = (((y0 `>>>` 15) + W64.one) `>>>` 1) + (y1 `<<<` 32) in
  let sq = square_word y0 y1 in
  let ei = ((((sq.`2 - ((x * x) `<<<` 20)) `<<<` 20) `|`
             (sq.`1 `>>>` 28)) + W64.one) `>>>` 1 in
  let e = approx_exp_word ei in
  let accepted = (((rej `^` (rej `&` W64.one)) - e) `|>>>` 63) `&`
                   (((r `|` (W64.zero - r)) `>>>` 63) `|` rej) `&` W64.one in
  (r, sq.`1, sq.`2, accepted).

(* The intended integer rounding formula, for separately decoded low noise,
   high noise and the CDT sample. The upper endpoint includes sample 166. *)
op sigma_round_int (lo hi x : int) : int =
  ((lo %/ 32768 + 1) %/ 2) + (hi + x * 16777216) * 4294967296.

lemma sigma_round_int_bounds (lo hi x : int) :
  0 <= lo < 281474976710656 =>
  0 <= hi < 16777216 =>
  0 <= x <= 166 =>
  0 <= sigma_round_int lo hi x <= 12033618204333965312 /\
  sigma_round_int lo hi x < 18446744073709551616.
proof.
  move=> hlo hhi hx.
  have h0 := divz_eq lo 32768.
  have h1 := modz_cmp lo 32768.
  have h2 := divz_eq (lo %/ 32768 + 1) 2.
  have h3 := modz_cmp (lo %/ 32768 + 1) 2.
  rewrite /sigma_round_int.
  smt().
qed.
