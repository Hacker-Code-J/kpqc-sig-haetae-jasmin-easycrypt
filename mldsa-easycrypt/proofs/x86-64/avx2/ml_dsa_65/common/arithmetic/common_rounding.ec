require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.

from Spec require import GFq Rq Parameters MLDSA_W32_Rep.

import Round ZModQ Zq.

require import Array256.

(* ================================================================== *)
(* polynomial____make_hint                                              *)
(* For each coefficient i:                                             *)
(*   hints[i] = MakeHint(low_coefficients[i], high_coefficients[i])   *)
(*            = 1 if HighBits(low+high) != HighBits(high), else 0     *)
(* Also returns the total weight (count of 1s).                        *)
(* Spec connection (via poly_MakeHintImpl from Rq.ec):                 *)
(*   liftu_wpoly res.`1 = poly_MakeHintImpl (lifts_wpoly _high)        *)
(*                                           (lifts_wpoly _low)         *)
(*   res.`2 = count (fun i => (liftu_wpoly res.`1).[i] <> Zq.zero)    *)
(*                  (iota_ 0 256)                                      *)
(* ================================================================== *)

lemma polynomial____make_hint_ll : islossless M.polynomial____make_hint.
proof.
proc.
wp; while (offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset);
  last by auto => /> /#. 
by move => *; auto => /> /#. 
qed.

lemma polynomial____make_hint_correct
      (_h : W32.t Array256.t) (_low : W32.t Array256.t) (_high : W32.t Array256.t) :
    hoare [ M.polynomial____make_hint :
        hints = _h /\ low_coefficients = _low /\ high_coefficients = _high /\
        (* low: w0_minus_cs2_plus_ct0 range — tightest achievable from norm checks *)
        wpoly_srng (2*gamma2 - Beta - 2) (2*gamma2 - Beta - 2) _low /\
        (* high: HighBits (w1) output range [0, (q-1) / (2*gamma2)] *)
        wpoly_urng ((q - 1) %/ (2 * gamma2)) _high
        ==>
        wpoly_urng 2 res.`1 /\
        liftu_wpoly res.`1 = poly_MakeHintImpl (lifts_wpoly _high) (lifts_wpoly _low) /\
        res.`2 = count (fun i => (liftu_wpoly res.`1).[i] <> Zq.zero) (iota_ 0 256)
    ].
proof.
admitted. (*poly  make hint *)

lemma polynomial____make_hint_ph
      (_h : W32.t Array256.t) (_low : W32.t Array256.t) (_high : W32.t Array256.t) :
    phoare [ M.polynomial____make_hint :
        hints = _h /\ low_coefficients = _low /\ high_coefficients = _high /\
        wpoly_srng (2*gamma2 - Beta - 2) (2*gamma2 - Beta - 2) _low /\
        wpoly_urng ((q - 1) %/ (2 * gamma2)) _high
        ==>
        wpoly_urng 2 res.`1 /\
        liftu_wpoly res.`1 = poly_MakeHintImpl (lifts_wpoly _high) (lifts_wpoly _low) /\
        res.`2 = count (fun i => (liftu_wpoly res.`1).[i] <> Zq.zero) (iota_ 0 256)
    ] = 1%r
  by conseq polynomial____make_hint_ll (polynomial____make_hint_correct _h _low _high).

(* ================================================================== *)
(* polynomial____power2round                                             *)
(* Splits each coefficient into high and low parts using 2^d:          *)
(*   highbits = (a + 2^(d-1)) >> d                                    *)
(*   lowbits  = a - highbits * 2^d                                    *)
(* Spec connection: poly_Power2Round from Rq.ec                        *)
(*   (liftu_wpoly res.`1, lifts_wpoly res.`2) ~ poly_Power2Round      *)
(* ================================================================== *)

lemma polynomial____power2round_ll : islossless M.polynomial____power2round.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
by move => *; auto => /#.
qed.

lemma polynomial____power2round_correct
      (_high : W32.t Array256.t) (_low : W32.t Array256.t) (_a : W32.t Array256.t) :
    hoare [ M.polynomial____power2round :
        highbits = _high /\ lowbits = _low /\ polynomial = _a /\
        wpoly_urng q _a  (* input in [0, q-1], after conditionally_add_modulus *)
        ==>
        (* t1 (high): unsigned, [0, 2^(23-d) - 1] *)
        (forall i, 0 <= i < 256 =>
            W32.to_uint res.`1.[i] = asint (Power2Round (liftu_wpoly _a).[i]).`1 ) /\
        wpoly_urng (2^(23-d)) res.`1 /\
        (* t0 (low): signed, (-(2^(d-1)), 2^(d-1)] *)
        (forall i, 0 <= i < 256 =>
            W32.to_sint res.`2.[i] = asint (Power2Round (liftu_wpoly _a).[i]).`2 ) /\
        wpoly_srng (2^(d-1) - 1) (2^(d-1)) res.`2
    ].
proof.
admitted. (* poly power2round *)

lemma polynomial____power2round_ph
      (_high : W32.t Array256.t) (_low : W32.t Array256.t) (_a : W32.t Array256.t) :
    phoare [ M.polynomial____power2round :
        highbits = _high /\ lowbits = _low /\ polynomial = _a /\
        wpoly_urng q _a
        ==>
        (forall i, 0 <= i < 256 =>
            W32.to_uint res.`1.[i] = asint (Power2Round (liftu_wpoly _a).[i]).`1 ) /\
        wpoly_urng (2^(23-d)) res.`1 /\
        (forall i, 0 <= i < 256 =>
            W32.to_sint res.`2.[i] = asint (Power2Round (liftu_wpoly _a).[i]).`2 ) /\
        wpoly_srng (2^(d-1) - 1) (2^(d-1)) res.`2
    ] = 1%r
  by conseq polynomial____power2round_ll
            (polynomial____power2round_correct _high _low _a).
