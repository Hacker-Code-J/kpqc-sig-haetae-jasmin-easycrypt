require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.

require import CircuitBindings Bindings.

from Spec require import GFq Rq Parameters MLDSA_W32_Rep Symmetric Serialization.

import Round ZModQ Zq.

require import XArray256 Array256.

require import WArray1024.

(* FIXME: PY TRY WITH COMPUTATION *)

op check_inf_norm_circuit (_a : W32.t Array256.t) (_threshold : int) : bool =
   all (fun i => (W32.of_int (-_threshold) \slt _a.[i] /\ _a.[i] \slt W32.of_int (_threshold)))  (iotared 0 256).

lemma polynomial____check_infinity_norm_correct (_a : W32.t Array256.t) (_threshold : int) :
   hoare [ M.polynomial____check_infinity_norm :
       (* gamma1-Beta = 524092  or  gamma2-Beta = 261692  or  gamma2 = 261888 *)
       (_threshold = (1 `<<` gamma1m1_bits) - 49 * w1_bits \/
        _threshold = (q - 1) %/ 32 - 49 * w1_bits \/
        _threshold = (q - 1) %/ 32) /\
       polynomial = _a /\ threshold = _threshold /\
       (* coefficients must be centered representatives so to_sint = crepr *)
       wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2) _a
     ==>
       (wpoly_infnorm_lt _threshold _a => res = W64.zero) /\
       (!wpoly_infnorm_lt _threshold _a => res = W64.one)
   ].
proof.
rewrite /(`<<`) /=.
proc => /=.
seq 2 : (#pre /\ threshold_vector = W256.of_int (_threshold - 1)).
+ auto => />  Hdisj; elim Hdisj => [-> | [-> | ->]] /= Hrng.
  + rewrite /VMOV_64 /= to_uint_eq to_uint_zeroextu256 of_uintK /=.
    rewrite -(W128.of_uintK 524091); congr; rewrite wordP => i ib.
    rewrite /pack2_t initiE 1:/# /= get_of_list 1:/# /= of_intE /= bits2wE initiE 1:/# /=.
    case (i %/ 64 = 0) => ? /=.
    + rewrite of_intE /= bits2wE initiE 1:/# /=.
      by rewrite /BitEncoding.BS2Int.int2bs nth_mkseq 1:/# /= nth_mkseq 1:/# /= /#.
    rewrite /BitEncoding.BS2Int.int2bs nth_mkseq 1:/# /=.
    rewrite pdiv_small; last by smt().
    smt(StdOrder.IntOrder.ler_lt_trans StdOrder.IntOrder.ler_weexpn2l pow2_64).
  + rewrite /VMOV_64 /= to_uint_eq to_uint_zeroextu256 of_uintK /=.
    rewrite -(W128.of_uintK 261691); congr; rewrite wordP => i ib.
    rewrite /pack2_t initiE 1:/# /= get_of_list 1:/# /= of_intE /= bits2wE initiE 1:/# /=.
    case (i %/ 64 = 0) => ? /=.
    + rewrite of_intE /= bits2wE initiE 1:/# /=.
      by rewrite /BitEncoding.BS2Int.int2bs nth_mkseq 1:/# /= nth_mkseq 1:/# /= /#.
    rewrite /BitEncoding.BS2Int.int2bs nth_mkseq 1:/# /=.
    rewrite pdiv_small; last by smt().
    smt(StdOrder.IntOrder.ler_lt_trans StdOrder.IntOrder.ler_weexpn2l pow2_64).
  + (* gamma2 = 261888, threshold_vector = W256.of_int 261887 *)
    rewrite /VMOV_64 /= to_uint_eq to_uint_zeroextu256 of_uintK /=.
    rewrite -(W128.of_uintK 261887); congr; rewrite wordP => i ib.
    rewrite /pack2_t initiE 1:/# /= get_of_list 1:/# /= of_intE /= bits2wE initiE 1:/# /=.
    case (i %/ 64 = 0) => ? /=.
    + rewrite of_intE /= bits2wE initiE 1:/# /=.
      by rewrite /BitEncoding.BS2Int.int2bs nth_mkseq 1:/# /= nth_mkseq 1:/# /= /#.
    rewrite /BitEncoding.BS2Int.int2bs nth_mkseq 1:/# /=.
    rewrite pdiv_small; last by smt().
    smt(StdOrder.IntOrder.ler_lt_trans StdOrder.IntOrder.ler_weexpn2l pow2_64).

proc change ^while.1 : { coefficients <- if (0 <= offset*8 <= 32*256-256)
                                         then BSWAS_256u32_256.sliceget polynomial (offset*8)
                                         else get256_direct (WArray1024.init32 (fun i => polynomial.[i])) offset; }.
                + auto => /> &2.
                  case (0 <= offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.

wp 7.
proc change 7 : { zf <- msb_mask = W32.zero; }.
+ by auto => /= &1 &2 ->; rewrite /TEST_32 /rflags_of_bwop /= /ZF_of  /=.

unroll for ^while.
cfold 131.
wp -1.
conseq (: polynomial = _a /\ threshold_vector = W256.of_int (_threshold - 1) /\
        List.all (fun i => W32.of_int (-4190208) \sle _a.[i]
               /\ _a.[i] \sle  W32.of_int 4190208) (iotared 0 256) /\
          (_threshold = 524092 \/ _threshold = 261692 \/ _threshold = 261888)  ==>
    zf = (check_inf_norm_circuit _a _threshold)).

(*  Connect circuit form to poly_infnorm spec *)
+ move => &1 [#] ? <- ? + ?; rewrite /wpoly_srng iotaredE /(\sle) !of_sintK /smod !allP /=;smt(mem_iota).

move => &hr [#] Hdij <- Ht Hr ? zf  -> /=.
rewrite /check_inf_norm_circuit !allP /SETcc;
split; rewrite iotaredE /= => H4.
+ rewrite ifF /=.
  + rewrite /(\slt) /= !of_sintK /= /smod /=.
    move => x; rewrite mem_iota => ?.
    move : H4; rewrite /wpoly_infnorm_lt /wpoly_srng allP /= /#.
  by rewrite to_uint_eq /=.
rewrite ifT /=.
  + rewrite /(\slt) /= !of_sintK /= /smod /=.
    move : H4; rewrite /wpoly_infnorm_lt /wpoly_srng allP /=; smt(mem_iota).
  by rewrite to_uint_eq /=.

  (* Handle the circuit *)
case (_threshold = 524092).
+ conseq (: polynomial = _a /\ threshold_vector = W256.of_int 524091 /\
       List.all (fun i => W32.of_int (-4190208) \sle _a.[i]
               /\ _a.[i] \sle  W32.of_int 4190208) (iotared 0 256)
          ==>
    zf = (check_inf_norm_circuit _a 524092));
    [ by smt() | by smt() | by simplify;circuit].
case (_threshold = 261692).
+ conseq (: polynomial = _a /\ threshold_vector = W256.of_int 261691 /\
       List.all (fun i => W32.of_int (-4190208) \sle _a.[i]
               /\ _a.[i] \sle  W32.of_int 4190208) (iotared 0 256)
          ==>
    zf = (check_inf_norm_circuit _a 261692));
    [ by smt() | by smt() | by simplify;circuit].
(* gamma2 = 261888: threshold_vector = W256.of_int 261887 *)
+ conseq (: polynomial = _a /\ threshold_vector = W256.of_int 261887 /\
       List.all (fun i => W32.of_int (-4190208) \sle _a.[i]
               /\ _a.[i] \sle  W32.of_int 4190208) (iotared 0 256)
          ==>
    zf = (check_inf_norm_circuit _a 261888));
    [ by smt() | by smt() | by simplify;circuit].
qed.

lemma polynomial____check_infinity_norm_ll : islossless M.polynomial____check_infinity_norm.
proof.
proc.
wp;while (0 <= offset <= 1024 /\ offset %% 32 = 0) (1024 - offset); auto => /> /#.
qed.

lemma polynomial____check_infinity_norm_ph (_a : W32.t Array256.t) (_threshold : int) :
   phoare [ M.polynomial____check_infinity_norm :
       (* gamma1-Beta = 524092  or  gamma2-Beta = 261692  or  gamma2 = 261888 *)
       (_threshold = (1 `<<` gamma1m1_bits) - 49 * w1_bits \/
        _threshold = (q - 1) %/ 32 - 49 * w1_bits \/
        _threshold = (q - 1) %/ 32) /\
       polynomial = _a /\ threshold = _threshold /\
       (* coefficients must be centered representatives so to_sint = crepr *)
       wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2) _a
     ==>
       (wpoly_infnorm_lt _threshold _a => res = W64.zero) /\
       (!wpoly_infnorm_lt _threshold _a => res = W64.one)
   ] = 1%r
 by conseq polynomial____check_infinity_norm_ll (polynomial____check_infinity_norm_correct _a _threshold).

(* ================================================================== *)
(* polynomial__add                                                      *)
(* Pointwise addition without reduction.                               *)
(* Spec: lifts_wpoly res = lifts_wpoly _lhs + lifts_wpoly _rhs        *)
(* No range restriction: result may need reduce32 afterwards.          *)
(* ================================================================== *)

lemma polynomial__add_ll : islossless M.polynomial__add.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
by move => *; auto => /#.
qed.

lemma polynomial__add_correct
      (_sum : W32.t Array256.t) (_lhs : W32.t Array256.t) (_rhs : W32.t Array256.t)
      (A B : int) :
    hoare [ M.polynomial__add :
        sum_pointer = _sum /\ lhs_pointer = _lhs /\ rhs_pointer = _rhs /\
        wpoly_srng A A _lhs /\ wpoly_srng B B _rhs /\ A + B < 2^31
        ==>
        lifts_wpoly res = lifts_wpoly _lhs &+ lifts_wpoly _rhs /\
        wpoly_srng (A + B) (A + B) res
    ].
proof.
admitted. (* poly add correct *)

lemma polynomial__add_ph
      (_sum : W32.t Array256.t) (_lhs : W32.t Array256.t) (_rhs : W32.t Array256.t)
      (A B : int) :
    phoare [ M.polynomial__add :
        sum_pointer = _sum /\ lhs_pointer = _lhs /\ rhs_pointer = _rhs /\
        wpoly_srng A A _lhs /\ wpoly_srng B B _rhs /\ A + B < 2^31
        ==>
        lifts_wpoly res = lifts_wpoly _lhs &+ lifts_wpoly _rhs /\
        wpoly_srng (A + B) (A + B) res
    ] = 1%r
  by conseq polynomial__add_ll (polynomial__add_correct _sum _lhs _rhs A B).

(* ================================================================== *)
(* polynomial__subtract                                                 *)
(* Pointwise subtraction without reduction.                            *)
(* Spec: lifts_wpoly res = lifts_wpoly _lhs - lifts_wpoly _rhs        *)
(* No range restriction: result may need reduce32 afterwards.          *)
(* ================================================================== *)

lemma polynomial__subtract_ll : islossless M.polynomial__subtract.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
by move => *; auto => /#.
qed.

lemma polynomial__subtract_correct
      (_diff : W32.t Array256.t) (_lhs : W32.t Array256.t) (_rhs : W32.t Array256.t)
      (A B : int) :
    hoare [ M.polynomial__subtract :
        difference_pointer = _diff /\ lhs_pointer = _lhs /\ rhs_pointer = _rhs /\
        wpoly_srng A A _lhs /\ wpoly_srng B B _rhs /\ A + B < 2^31
        ==>
        lifts_wpoly res = lifts_wpoly _lhs &+ ((&-) (lifts_wpoly _rhs)) /\
        wpoly_srng (A + B) (A + B) res
    ].
proof.
admitted. (* poly sub correct *)

lemma polynomial__subtract_ph
      (_diff : W32.t Array256.t) (_lhs : W32.t Array256.t) (_rhs : W32.t Array256.t)
      (A B : int) :
    phoare [ M.polynomial__subtract :
        difference_pointer = _diff /\ lhs_pointer = _lhs /\ rhs_pointer = _rhs /\
        wpoly_srng A A _lhs /\ wpoly_srng B B _rhs /\ A + B < 2^31
        ==>
        lifts_wpoly res = lifts_wpoly _lhs &+ ((&-) (lifts_wpoly _rhs)) /\
        wpoly_srng (A + B) (A + B) res
    ] = 1%r
  by conseq polynomial__subtract_ll (polynomial__subtract_correct _diff _lhs _rhs A B).

(* ================================================================== *)
(* polynomial____zero                                                    *)
(* Sets all 256 coefficients to zero.                                  *)
(* ================================================================== *)

lemma polynomial____zero_ll : islossless M.polynomial____zero.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
by move => *; auto => /#.
qed.

lemma polynomial____zero_correct (_a : W32.t Array256.t) :
    hoare [ M.polynomial____zero :
        polynomial = _a
        ==>
        (forall i, 0 <= i < 256 => res.[i] = W32.zero) /\
        wpoly_srng 0 0 res
    ].
proof.
admitted. (* poly zero correct *)

lemma polynomial____zero_ph (_a : W32.t Array256.t) :
    phoare [ M.polynomial____zero :
        polynomial = _a
        ==>
        (forall i, 0 <= i < 256 => res.[i] = W32.zero) /\
        wpoly_srng 0 0 res
    ] = 1%r
  by conseq polynomial____zero_ll (polynomial____zero_correct _a).

(* ================================================================== *)
(* polynomial____pointwise_add_to_total                                  *)
(* Pointwise addition into accumulator: total += polynomial.           *)
(* Identical semantics to polynomial__add.                             *)
(* ================================================================== *)

lemma polynomial____pointwise_add_to_total_ll :
    islossless M.polynomial____pointwise_add_to_total.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
by move => *; auto => /#.
qed.

lemma polynomial____pointwise_add_to_total_correct
      (_total : W32.t Array256.t) (_poly : W32.t Array256.t) (A B : int) :
    hoare [ M.polynomial____pointwise_add_to_total :
        total = _total /\ polynomial = _poly /\
        wpoly_srng A A _total /\ wpoly_srng B B _poly /\ A + B < 2^31
        ==>
        lifts_wpoly res = lifts_wpoly _total &+ lifts_wpoly _poly /\
        wpoly_srng (A + B) (A + B) res
    ].
proof.
admitted. (*  self add correct *)

lemma polynomial____pointwise_add_to_total_ph
      (_total : W32.t Array256.t) (_poly : W32.t Array256.t) (A B : int) :
    phoare [ M.polynomial____pointwise_add_to_total :
        total = _total /\ polynomial = _poly /\
        wpoly_srng A A _total /\ wpoly_srng B B _poly /\ A + B < 2^31
        ==>
        lifts_wpoly res = lifts_wpoly _total &+ lifts_wpoly _poly /\
        wpoly_srng (A + B) (A + B) res
    ] = 1%r
  by conseq polynomial____pointwise_add_to_total_ll
            (polynomial____pointwise_add_to_total_correct _total _poly A B).

(* ================================================================== *)
(* polynomial____shift_coefficients_left                                 *)
(* Left-shifts all coefficients by d = 13 bits.                        *)
(* Used in verify to reconstruct t1 * 2^d.                            *)
(* ================================================================== *)

lemma polynomial____shift_coefficients_left_ll :
    islossless M.polynomial____shift_coefficients_left.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
by move => *; auto => /#.
qed.

(* Pre/post tightened 2026-04-17: pre from wpoly_urng (2^10+1) = values ≤ 2^10    *)
(* to wpoly_urng (2^10) = values ≤ 2^10 - 1 (matches t1_decode's output bound     *)
(* b_t1 + 1 = 2^10). Post from wpoly_srng (2^10 * 2^d) ≥ q bound to                *)
(* wpoly_srng (q-1) (q-1): tight since (2^10 - 1) * 2^d = q - 1 exactly.          *)
lemma polynomial____shift_coefficients_left_correct (_a : W32.t Array256.t) :
    hoare [ M.polynomial____shift_coefficients_left :
        polynomial = _a /\
        wpoly_urng (2^10) _a       (* t1 range: [0, 2^10 - 1] = [0, b_t1] *)
        ==>
        (forall i, 0 <= i < 256 =>
            W32.to_sint res.[i] = W32.to_uint _a.[i] * 2^d) /\
        wpoly_srng (q-1) (q-1) res
    ].
proof.
admitted. (* shif coeffs correct *)

lemma polynomial____shift_coefficients_left_ph (_a : W32.t Array256.t) :
    phoare [ M.polynomial____shift_coefficients_left :
        polynomial = _a /\
        wpoly_urng (2^10) _a
        ==>
        (forall i, 0 <= i < 256 =>
            W32.to_sint res.[i] = W32.to_uint _a.[i] * 2^d) /\
        wpoly_srng (q-1) (q-1) res
    ] = 1%r
  by conseq polynomial____shift_coefficients_left_ll
            (polynomial____shift_coefficients_left_correct _a).
