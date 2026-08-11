require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.

from Spec require import GFq Rq Parameters MLDSA_W32_Rep.

import Round ZModQ Zq.

require import Array256.

(* STRATEGY: TRY WITH SMT @ GUSTAVO *)

(* ================================================================== *)
(* polynomial__decompose                                                *)
(* Decomposes each coefficient into (LowBits, HighBits) per FIPS 204. *)
(* Uses gamma2 = (q-1)/32 for ML-DSA-65.                              *)
(* Input: polynomial in [0, q-1] (after conditionally_add_modulus).    *)
(* Output: lows in [-(gamma2-1), gamma2],                              *)
(*         highs in [0, (q-1)/(2*gamma2)]                             *)
(* Spec connection (via Decompose from GFq.ec):                        *)
(*   lows.[i]  = LowBits((liftu_wpoly _a).[i])                       *)
(*   highs.[i] = HighBits((liftu_wpoly _a).[i])                      *)
(* ================================================================== *)

lemma polynomial__decompose_ll : islossless M.polynomial__decompose.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
by move => *; auto => /#.
qed.

lemma polynomial__decompose_correct
      (_low : W32.t Array256.t) (_high : W32.t Array256.t) (_a : W32.t Array256.t) :
    hoare [ M.polynomial__decompose :
        lows = _low /\ highs = _high /\ polynomial = _a /\
        wpoly_urng q _a  (* input in [0, q-1] *)
        ==>
        (* LowBits: signed, [-(gamma2-1), gamma2] *)
        (forall i, 0 <= i < 256 =>
            W32.to_sint res.`1.[i] = LowBits ((liftu_wpoly _a).[i])) /\
        wpoly_srng (gamma2 - 1) gamma2 res.`1 /\
        (* HighBits: unsigned, [0, (q-1)/(2*gamma2)] *)
        (forall i, 0 <= i < 256 =>
            W32.to_uint res.`2.[i] = HighBits ((liftu_wpoly _a).[i])) /\
        wpoly_urng ((q - 1) %/ (2 * gamma2)) res.`2
    ].
proof.
admitted. (* poly decompose *)

lemma polynomial__decompose_ph
      (_low : W32.t Array256.t) (_high : W32.t Array256.t) (_a : W32.t Array256.t) :
    phoare [ M.polynomial__decompose :
        lows = _low /\ highs = _high /\ polynomial = _a /\
        wpoly_urng q _a
        ==>
        (forall i, 0 <= i < 256 =>
            W32.to_sint res.`1.[i] = LowBits ((liftu_wpoly _a).[i])) /\
        wpoly_srng (gamma2 - 1) gamma2 res.`1 /\
        (forall i, 0 <= i < 256 =>
            W32.to_uint res.`2.[i] = HighBits ((liftu_wpoly _a).[i])) /\
        wpoly_urng ((q - 1) %/ (2 * gamma2)) res.`2
    ] = 1%r
  by conseq polynomial__decompose_ll (polynomial__decompose_correct _low _high _a).

(* ================================================================== *)
(* polynomial__use_hints                                                *)
(* Applies hints to adjust HighBits of commitment coefficients.        *)
(* Internally calls polynomial__decompose, then uses VPSIGN-based     *)
(* conditional adjustment of high bits based on sign of low bits.      *)
(* Spec connection (via poly_UseHint from Rq.ec):                      *)
(*   liftu_wpoly res = poly_UseHint (liftu_wpoly _hints)               *)
(*                                   (liftu_wpoly _commitment)         *)
(* ================================================================== *)

lemma polynomial__use_hints_ll : islossless M.polynomial__use_hints.
proof.
proc.
while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
       ((256 * 32) %/ 8 - offset); last first.
+ wp; call polynomial__decompose_ll.
  by auto => /#.
by move => *; auto => /#.
qed.

(* Tight output bound: the AVX2 impl ends use_hints with `& 15` (4-bit mask),     *)
(* so output is always in [0..15] = wpoly_urng ((q-1)/(2*gamma2)) = wpoly_urng 16.*)
(* See submodules/dilithium/dilithium/ref/rounding.c:91-95 for the reference.     *)
lemma polynomial__use_hints_correct
      (_commitment : W32.t Array256.t) (_hints : W32.t Array256.t) :
    hoare [ M.polynomial__use_hints :
        commitment = _commitment /\ hint_polynomial = _hints /\
        wpoly_urng q _commitment /\   (* standard range [0, q-1] *)
        wpoly_urng 2 _hints           (* hints are 0 or 1 *)
        ==>
        liftu_wpoly res = poly_UseHint (liftu_wpoly _hints) (liftu_wpoly _commitment) /\
        wpoly_urng ((q - 1) %/ (2 * gamma2)) res
    ].
proof.
admitted. (* poly use hints *)

lemma polynomial__use_hints_ph
      (_commitment : W32.t Array256.t) (_hints : W32.t Array256.t) :
    phoare [ M.polynomial__use_hints :
        commitment = _commitment /\ hint_polynomial = _hints /\
        wpoly_urng q _commitment /\
        wpoly_urng 2 _hints
        ==>
        liftu_wpoly res = poly_UseHint (liftu_wpoly _hints) (liftu_wpoly _commitment) /\
        wpoly_urng ((q - 1) %/ (2 * gamma2)) res
    ] = 1%r
  by conseq polynomial__use_hints_ll (polynomial__use_hints_correct _commitment _hints).
