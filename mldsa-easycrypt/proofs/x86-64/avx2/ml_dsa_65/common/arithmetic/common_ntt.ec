require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.

from Spec require import GFq Rq Parameters MLDSA_W32_Rep.

import Round ZModQ Zq.

require import Array256.

(* ================================================================== *)
(* polynomial__ntt                                                      *)
(* Computes the forward NTT of a polynomial.                           *)
(* Input:  wpoly_ntt_irng _a                                           *)
(* Output: lifts_wpoly res = ntt (lifts_wpoly _a)                     *)
(*         wpoly_ntt_orng res                                          *)
(* ================================================================== *)

lemma polynomial__ntt_ll : islossless M.polynomial__ntt.
proof.
proc.
do 7!(wp; call (: true ==> true); [by proc; admit |]). (* to : ntt ll *)
by auto.
qed.

lemma polynomial__ntt_correct (_a : W32.t Array256.t) :
    hoare [ M.polynomial__ntt :
        polynomial = _a /\ wpoly_ntt_irng _a
        ==>
        lifts_wpoly res = ntt (lifts_wpoly _a) /\
        wpoly_ntt_orng res
    ].
proof.
admitted.

lemma polynomial__ntt_ph (_a : W32.t Array256.t) :
    phoare [ M.polynomial__ntt :
        polynomial = _a /\ wpoly_ntt_irng _a
        ==>
        lifts_wpoly res = ntt (lifts_wpoly _a) /\
        wpoly_ntt_orng res
    ] = 1%r
  by conseq polynomial__ntt_ll (polynomial__ntt_correct _a).
