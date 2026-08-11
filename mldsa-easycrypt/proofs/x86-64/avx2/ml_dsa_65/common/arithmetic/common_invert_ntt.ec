require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Common_modular.

from Spec require import GFq Rq Parameters MLDSA_W32_Rep.

import Round ZModQ Zq.

require import Array256.

(* ================================================================== *)
(* polynomial__invert_ntt_montgomery                                    *)
(* Computes the inverse NTT of a polynomial.                           *)
(* Input:  wpoly_intt_irng _a  (satisfied when basemul output in range [-q+1,q-1])  *)
(* Output: lifts_wpoly res = invntt (lifts_wpoly _a)  (TODO: Montgomery factor analysis) *)
(*         wpoly_srng (q-1) (q-1) res  (from final Montgomery scaling step)              *)
(* ================================================================== *)

lemma polynomial__invert_ntt_montgomery_ll : islossless M.polynomial__invert_ntt_montgomery.
proof.
proc.
wp; while (0 <= i <= (256 * 32) %/ 8 /\ i %% 32 = 0) ((256 * 32) %/ 8 - i);
  last first.
+ do 8!(wp; call (: true ==> true); 1: by admit). (* to do, ntt lossless *)
  by auto => /#.
move => *.
wp; call montgomery_multiply_and_reduce_ll.
by auto => /#.
qed.

lemma polynomial__invert_ntt_montgomery_correct (_a : W32.t Array256.t) :
    hoare [ M.polynomial__invert_ntt_montgomery :
        polynomial = _a /\ wpoly_intt_irng _a
        ==>
        lifts_wpoly res = invntt (lifts_wpoly _a) /\ (* TODO: algebraic claim requires Montgomery factor analysis *)
        wpoly_srng invntt_obound invntt_obound res
    ].
proof.
admitted. (* invert ntt correct *)

lemma polynomial__invert_ntt_montgomery_ph (_a : W32.t Array256.t) :
    phoare [ M.polynomial__invert_ntt_montgomery :
        polynomial = _a /\ wpoly_intt_irng _a
        ==>
        lifts_wpoly res = invntt (lifts_wpoly _a) /\ (* TODO: algebraic claim requires Montgomery factor analysis *)
        wpoly_srng invntt_obound invntt_obound res
    ] = 1%r
  by conseq polynomial__invert_ntt_montgomery_ll
            (polynomial__invert_ntt_montgomery_correct _a).
