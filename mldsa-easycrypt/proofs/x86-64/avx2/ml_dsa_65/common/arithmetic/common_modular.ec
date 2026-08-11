require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.

from Spec require import GFq Rq Parameters MLDSA_W32_Rep.

import Round ZModQ Zq.

require import Array256.

(* ================================================================== *)
(* montgomery_multiply_and_reduce                                       *)
(* AVX2 vectorised Montgomery multiplication (8 lanes in parallel).    *)
(* Computes a * b * R^-1 mod q for each of 8 coefficient pairs.        *)
(* Used as the inner loop body of pointwise_montgomery_multiply and     *)
(* invert_ntt_montgomery.                                               *)
(* ================================================================== *)

lemma montgomery_multiply_and_reduce_ll : islossless M.montgomery_multiply_and_reduce.
proof. by proc; islossless. qed.

lemma montgomery_multiply_and_reduce_correct (u v : W256.t) :
    hoare [ M.montgomery_multiply_and_reduce :
        arg = (u, v)
        ==>
        true (* TODO: state word-level correctness in terms of Zq multiplication *)
    ].
proof. admitted. (* montgomery multiply and reduce *)

lemma montgomery_multiply_and_reduce_ph (u v : W256.t) :
    phoare [ M.montgomery_multiply_and_reduce :
        arg = (u, v)
        ==>
        true
    ] = 1%r
  by conseq montgomery_multiply_and_reduce_ll
            (montgomery_multiply_and_reduce_correct u v).

(* ================================================================== *)
(* polynomial__reduce32                                                 *)
(* reduce32(a)[i] = a[i] mod q, centered representative                *)
(* Concretely: a[i] - round(a[i] / 2^23) * q                         *)
(* Spec: lifts_wpoly res = lifts_wpoly _a (same GFq value)             *)
(*       wpoly_srng ((q-1)%/2) ((q-1)%/2) res  (centered rep)         *)
(* ================================================================== *)

lemma polynomial__reduce32_ll : islossless M.polynomial__reduce32.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
by move => *; auto => /#.
qed.

lemma polynomial__reduce32_correct (_a : W32.t Array256.t) :
    hoare [ M.polynomial__reduce32 :
        polynomial = _a
        ==>
        (* GFq value preserved *)
        lifts_wpoly res = lifts_wpoly _a /\
        (* output is centered representative: |to_sint coeff| <= (q-1)/2 *)
        wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2) res
    ].
proof.
admitted. (* reduce *)

lemma polynomial__reduce32_ph (_a : W32.t Array256.t) :
    phoare [ M.polynomial__reduce32 :
        polynomial = _a
        ==>
        lifts_wpoly res = lifts_wpoly _a /\
        wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2) res
    ] = 1%r
  by conseq polynomial__reduce32_ll (polynomial__reduce32_correct _a).

(* ================================================================== *)
(* polynomial__pointwise_montgomery_multiply_and_reduce                 *)
(* Computes lhs[i] * rhs[i] in Zq via Montgomery reduction.           *)
(* Input:  wpoly_bmul_irng on both operands                            *)
(*         (NTT outputs satisfy this: wpoly_ntt_orng => wpoly_bmul_irng)*)
(* Output: lifts_wpoly res = basemul (lifts_wpoly lhs) (lifts_wpoly rhs)*)
(*         wpoly_srng (q-1) (q-1) res  (from final Montgomery reduction) *)
(* ================================================================== *)

lemma polynomial__pointwise_montgomery_multiply_and_reduce_ll :
    islossless M.polynomial__pointwise_montgomery_multiply_and_reduce.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 64 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
move => *.
(* each loop body processes two 32-byte chunks via montgomery_multiply_and_reduce *)
wp; call (: true ==> true); 1: by islossless. (* second call *)
wp; call (: true ==> true); 1: by islossless. (* first call *)
by auto => /#.
qed.

lemma polynomial__pointwise_montgomery_multiply_and_reduce_correct
      (_prod : W32.t Array256.t) (_lhs : W32.t Array256.t) (_rhs : W32.t Array256.t) :
    hoare [ M.polynomial__pointwise_montgomery_multiply_and_reduce :
        product = _prod /\ lhs = _lhs /\ rhs = _rhs /\
        wpoly_bmul_irng _lhs /\ wpoly_bmul_irng _rhs
        ==>
        lifts_wpoly res = basemul (lifts_wpoly _lhs) (lifts_wpoly _rhs) /\ (* TODO: may need Montgomery factor correction *)
        wpoly_srng (q-1) (q-1) res
    ].
proof.
admitted. (* pointwise mont mul and reduce *)

lemma polynomial__pointwise_montgomery_multiply_and_reduce_ph
      (_prod : W32.t Array256.t) (_lhs : W32.t Array256.t) (_rhs : W32.t Array256.t) :
    phoare [ M.polynomial__pointwise_montgomery_multiply_and_reduce :
        product = _prod /\ lhs = _lhs /\ rhs = _rhs /\
        wpoly_bmul_irng _lhs /\ wpoly_bmul_irng _rhs
        ==>
        lifts_wpoly res = basemul (lifts_wpoly _lhs) (lifts_wpoly _rhs) /\ (* TODO: may need Montgomery factor correction *)
        wpoly_srng (q-1) (q-1) res
    ] = 1%r
  by conseq polynomial__pointwise_montgomery_multiply_and_reduce_ll
            (polynomial__pointwise_montgomery_multiply_and_reduce_correct _prod _lhs _rhs).

(* ================================================================== *)
(* polynomial__conditionally_add_modulus                                 *)
(* Converts centered representative to standard [0, q-1]:              *)
(*   if coeff < 0 then coeff + q else coeff                           *)
(* Spec: lifts_wpoly res = lifts_wpoly _a  (Zq value preserved)       *)
(*       wpoly_urng q res                  (all in [0, q-1])          *)
(* ================================================================== *)

lemma polynomial__conditionally_add_modulus_ll :
    islossless M.polynomial__conditionally_add_modulus.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
by move => *; auto => /#.
qed.

lemma polynomial__conditionally_add_modulus_correct (_a : W32.t Array256.t) :
    hoare [ M.polynomial__conditionally_add_modulus :
        polynomial = _a /\
        wpoly_srng (q-1) (q-1) _a
        ==>
        lifts_wpoly res = lifts_wpoly _a /\
        wpoly_urng q res
    ].
proof.
admitted. (* cond add modulus *)

lemma polynomial__conditionally_add_modulus_ph (_a : W32.t Array256.t) :
    phoare [ M.polynomial__conditionally_add_modulus :
        polynomial = _a /\
        wpoly_srng (q-1) (q-1) _a
        ==>
        lifts_wpoly res = lifts_wpoly _a /\
        wpoly_urng q res
    ] = 1%r
  by conseq polynomial__conditionally_add_modulus_ll
            (polynomial__conditionally_add_modulus_correct _a).
