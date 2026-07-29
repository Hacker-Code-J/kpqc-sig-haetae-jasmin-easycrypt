require import AllCore IntDiv List Ring StdOrder Real RealExp.

require import KeygenM23ComplexReal.

import RField RealOrder.
import KeygenM23ComplexReal.

theory KeygenM23IdealRootDFT.

(* Instantiate the library's proved commutative-ring power laws for the
   transparent real-pair complex representation.  ComRingDflInv supplies its
   inverse by a proved choice construction; this file introduces no axiom. *)
clone import Ring.ComRingDflInv as C with
  type t <- complex,
  op zeror <- czero,
  op oner  <- cone,
  op (+)   <- cadd,
  op [-]   <- cneg,
  op ( * ) <- cmul
  proof *
  remove abbrev (-)
  remove abbrev (/).

realize addrA.
proof.
move=> x y z.
apply complex_ext.
+ rewrite !creal_add.
  ring.
+ rewrite !cimag_add.
  ring.
qed.
realize addrC.     proof. by apply caddC. qed.
realize add0r.     proof. by apply cadd0. qed.
realize addNr.     proof. by apply caddN. qed.
realize oner_neq0.
proof. by rewrite /cone /czero. qed.
realize mulrA.
proof.
move=> x y z.
apply complex_ext.
+ rewrite !creal_mul !cimag_mul.
  ring.
+ rewrite !cimag_mul !creal_mul.
  ring.
qed.
realize mulrC.     proof. by apply cmulC. qed.
realize mul1r.     proof. by apply cmul1. qed.
realize mulrDl.
proof.
move=> x y z.
apply complex_ext.
+ rewrite creal_mul !creal_add !cimag_add !creal_mul.
  ring.
+ rewrite cimag_mul !creal_add !cimag_add !cimag_mul.
  ring.
qed.

abbrev cpow = C.exp.

(* The table in the reference implementation uses exp(-i*pi*k/256), so the
   primitive witness must consistently choose the lower-half-plane square
   root. *)
op chalf_re (z : complex) : real =
  sqrt ((1%r + creal z) / 2%r).

op chalf_im (z : complex) : real =
  - sqrt ((1%r - creal z) / 2%r).

op chalf_neg (z : complex) : complex =
  (chalf_re z, chalf_im z).

op lower_unit (z : complex) : bool =
  cnorm2 z = 1%r /\
  -1%r <= creal z /\ creal z <= 1%r /\
  cimag z <= 0%r.

lemma creal_chalf_neg (z : complex) :
  creal (chalf_neg z) = chalf_re z by done.

lemma cimag_chalf_neg (z : complex) :
  cimag (chalf_neg z) = chalf_im z by done.

lemma chalf_arguments_ge0 (z : complex) :
  -1%r <= creal z => creal z <= 1%r =>
  0%r <= (1%r + creal z) / 2%r /\
  0%r <= (1%r - creal z) / 2%r.
proof. by move=> hlo hhi; split; smt(). qed.

lemma sqrt_one :
  sqrt 1%r = 1%r.
proof.
have h := sqrtsq_ge0 1%r.
by rewrite expr2 in h.
qed.

lemma chalf_re_bounds (z : complex) :
  -1%r <= creal z => creal z <= 1%r =>
  0%r <= chalf_re z /\ chalf_re z <= 1%r.
proof.
move=> hlo hhi.
have [ha0 hb0] := chalf_arguments_ge0 z hlo hhi.
have ha1 : (1%r + creal z) / 2%r <= 1%r by smt().
split.
+ exact (ge0_sqrt ((1%r + creal z) / 2%r)).
+ have hmono := sqrt_mono ((1%r + creal z) / 2%r) 1%r ha0.
  rewrite sqrt_one in hmono.
  by apply hmono.
qed.

lemma chalf_im_nonpos (z : complex) :
  chalf_im z <= 0%r.
proof.
rewrite /chalf_im.
have := ge0_sqrt ((1%r - creal z) / 2%r).
by smt().
qed.

lemma chalf_norm1 (z : complex) :
  -1%r <= creal z => creal z <= 1%r =>
  cnorm2 (chalf_neg z) = 1%r.
proof.
move=> hlo hhi.
have [ha0 hb0] := chalf_arguments_ge0 z hlo hhi.
have ha :
  sqrt ((1%r + creal z) / 2%r) *
  sqrt ((1%r + creal z) / 2%r) =
  (1%r + creal z) / 2%r.
+ rewrite -expr2.
  exact (sqsqrt ((1%r + creal z) / 2%r) ha0).
have hb :
  sqrt ((1%r - creal z) / 2%r) *
  sqrt ((1%r - creal z) / 2%r) =
  (1%r - creal z) / 2%r.
+ rewrite -expr2.
  exact (sqsqrt ((1%r - creal z) / 2%r) hb0).
have hbn :
  - sqrt ((1%r - creal z) / 2%r) *
  - sqrt ((1%r - creal z) / 2%r) =
  (1%r - creal z) / 2%r.
+ rewrite (_ :
    - sqrt ((1%r - creal z) / 2%r) *
    - sqrt ((1%r - creal z) / 2%r) =
    sqrt ((1%r - creal z) / 2%r) *
    sqrt ((1%r - creal z) / 2%r)).
  + ring.
  + exact hb.
rewrite /cnorm2 /chalf_neg /chalf_re /chalf_im /creal /cimag /=.
smt().
qed.

lemma chalf_neg_square (z : complex) :
  lower_unit z =>
  cmul (chalf_neg z) (chalf_neg z) = z.
proof.
move=> [hnorm [hlo [hhi him]]].
have [ha0 hb0] := chalf_arguments_ge0 z hlo hhi.
have ha :
  sqrt ((1%r + creal z) / 2%r) *
  sqrt ((1%r + creal z) / 2%r) =
  (1%r + creal z) / 2%r.
+ rewrite -expr2.
  exact (sqsqrt ((1%r + creal z) / 2%r) ha0).
have hb :
  sqrt ((1%r - creal z) / 2%r) *
  sqrt ((1%r - creal z) / 2%r) =
  (1%r - creal z) / 2%r.
+ rewrite -expr2.
  exact (sqsqrt ((1%r - creal z) / 2%r) hb0).
have hbn :
  - sqrt ((1%r - creal z) / 2%r) *
  - sqrt ((1%r - creal z) / 2%r) =
  (1%r - creal z) / 2%r.
+ rewrite (_ :
    - sqrt ((1%r - creal z) / 2%r) *
    - sqrt ((1%r - creal z) / 2%r) =
    sqrt ((1%r - creal z) / 2%r) *
    sqrt ((1%r - creal z) / 2%r)).
  + ring.
  + exact hb.
pose ti :=
  - (2%r *
     sqrt ((1%r + creal z) / 2%r) *
     sqrt ((1%r - creal z) / 2%r)).
have hti : ti <= 0%r.
+ rewrite /ti.
  have hsa := ge0_sqrt ((1%r + creal z) / 2%r).
  have hsb := ge0_sqrt ((1%r - creal z) / 2%r).
  have hab :
    0%r <=
      sqrt ((1%r + creal z) / 2%r) *
      sqrt ((1%r - creal z) / 2%r) by
    apply mulr_ge0.
  by smt().
have hti2 :
  ti * ti = 1%r - creal z * creal z.
+ rewrite /ti.
  smt().
have him2 :
  cimag z * cimag z = 1%r - creal z * creal z.
+ rewrite /cnorm2 in hnorm.
  by smt().
have htieq : ti = cimag z.
+ have hfac :
    (ti - cimag z) * (ti + cimag z) = 0%r.
  + have hid :
      (ti - cimag z) * (ti + cimag z) =
      ti * ti - cimag z * cimag z by ring.
    by rewrite hid hti2 him2 subrr.
  rewrite mulf_eq0 in hfac.
  case: hfac => hfac.
  + by move: hfac; rewrite subr_eq0.
  + have hopp : ti = - cimag z.
    - by move: hfac; rewrite addr_eq0.
    have hti0 : ti = 0%r by smt().
    have him0 : cimag z = 0%r by smt().
    by rewrite hti0 him0.
apply complex_ext.
+ rewrite creal_mul !creal_chalf_neg !cimag_chalf_neg
           /chalf_re /chalf_im.
  smt().
+ rewrite cimag_mul !creal_chalf_neg !cimag_chalf_neg
           /chalf_re /chalf_im.
  rewrite -htieq /ti.
  ring.
qed.

lemma chalf_neg_lower_unit (z : complex) :
  -1%r <= creal z => creal z <= 1%r =>
  lower_unit (chalf_neg z).
proof.
move=> hlo hhi.
have [hre0 hre1] := chalf_re_bounds z hlo hhi.
rewrite /lower_unit.
split.
+ exact (chalf_norm1 z hlo hhi).
+ rewrite creal_chalf_neg cimag_chalf_neg.
  split.
  + by smt().
  + split.
    - exact hre1.
    - exact (chalf_im_nonpos z).
qed.

(* Repeated lower-half-plane square roots, beginning at -i.  Each link is
   constructive: the next root is a pair of standard EasyCrypt reals. *)
op omega4   : complex = cneg ci.
op omega8   : complex = chalf_neg omega4.
op omega16  : complex = chalf_neg omega8.
op omega32  : complex = chalf_neg omega16.
op omega64  : complex = chalf_neg omega32.
op omega128 : complex = chalf_neg omega64.
op omega256 : complex = chalf_neg omega128.
op omega512 : complex = chalf_neg omega256.

lemma omega4_lower_unit :
  lower_unit omega4.
proof.
rewrite /lower_unit /omega4 /cnorm2 /cneg /ci /creal /cimag /=.
by split; [ring | smt()].
qed.

lemma omega8_lower_unit :
  lower_unit omega8.
proof.
have [_ [hlo [hhi _]]] := omega4_lower_unit.
apply chalf_neg_lower_unit.
+ exact hlo.
+ exact hhi.
qed.

lemma omega16_lower_unit :
  lower_unit omega16.
proof.
have [_ [hlo [hhi _]]] := omega8_lower_unit.
apply chalf_neg_lower_unit.
+ exact hlo.
+ exact hhi.
qed.

lemma omega32_lower_unit :
  lower_unit omega32.
proof.
have [_ [hlo [hhi _]]] := omega16_lower_unit.
apply chalf_neg_lower_unit.
+ exact hlo.
+ exact hhi.
qed.

lemma omega64_lower_unit :
  lower_unit omega64.
proof.
have [_ [hlo [hhi _]]] := omega32_lower_unit.
apply chalf_neg_lower_unit.
+ exact hlo.
+ exact hhi.
qed.

lemma omega128_lower_unit :
  lower_unit omega128.
proof.
have [_ [hlo [hhi _]]] := omega64_lower_unit.
apply chalf_neg_lower_unit.
+ exact hlo.
+ exact hhi.
qed.

lemma omega256_lower_unit :
  lower_unit omega256.
proof.
have [_ [hlo [hhi _]]] := omega128_lower_unit.
apply chalf_neg_lower_unit.
+ exact hlo.
+ exact hhi.
qed.

lemma omega512_lower_unit :
  lower_unit omega512.
proof.
have [_ [hlo [hhi _]]] := omega256_lower_unit.
apply chalf_neg_lower_unit.
+ exact hlo.
+ exact hhi.
qed.

lemma omega8_square :
  cmul omega8 omega8 = omega4.
proof.
apply chalf_neg_square.
exact omega4_lower_unit.
qed.

lemma omega16_square :
  cmul omega16 omega16 = omega8.
proof.
apply chalf_neg_square.
exact omega8_lower_unit.
qed.

lemma omega32_square :
  cmul omega32 omega32 = omega16.
proof.
apply chalf_neg_square.
exact omega16_lower_unit.
qed.

lemma omega64_square :
  cmul omega64 omega64 = omega32.
proof.
apply chalf_neg_square.
exact omega32_lower_unit.
qed.

lemma omega128_square :
  cmul omega128 omega128 = omega64.
proof.
apply chalf_neg_square.
exact omega64_lower_unit.
qed.

lemma omega256_square :
  cmul omega256 omega256 = omega128.
proof.
apply chalf_neg_square.
exact omega128_lower_unit.
qed.

lemma omega512_square :
  cmul omega512 omega512 = omega256.
proof.
apply chalf_neg_square.
exact omega256_lower_unit.
qed.

lemma omega4_square :
  cmul omega4 omega4 = cneg cone.
proof.
apply complex_ext.
+ rewrite creal_mul /omega4 !creal_neg !cimag_neg
          !creal_i !cimag_i !creal_one.
  ring.
+ rewrite cimag_mul /omega4 !creal_neg !cimag_neg
          !creal_i !cimag_i !cimag_one.
  ring.
qed.

lemma omega512_norm :
  cnorm2 omega512 = 1%r.
proof.
have [hnorm _] := omega512_lower_unit.
exact hnorm.
qed.

lemma cpow_square_transfer (z w : complex) (n : int) :
  cmul z z = w =>
  cpow z (2 * n) = cpow w n.
proof.
move=> hzw.
rewrite C.exprM C.expr2 hzw.
done.
qed.

lemma omega512_pow128 :
  cpow omega512 128 = omega4.
proof.
rewrite (_ : 128 = 2 * 64) 1://
        (cpow_square_transfer omega512 omega256 64 omega512_square).
rewrite (_ : 64 = 2 * 32) 1://
        (cpow_square_transfer omega256 omega128 32 omega256_square).
rewrite (_ : 32 = 2 * 16) 1://
        (cpow_square_transfer omega128 omega64 16 omega128_square).
rewrite (_ : 16 = 2 * 8) 1://
        (cpow_square_transfer omega64 omega32 8 omega64_square).
rewrite (_ : 8 = 2 * 4) 1://
        (cpow_square_transfer omega32 omega16 4 omega32_square).
rewrite (_ : 4 = 2 * 2) 1://
        (cpow_square_transfer omega16 omega8 2 omega16_square).
rewrite (_ : 2 = 2 * 1) 1://
        (cpow_square_transfer omega8 omega4 1 omega8_square).
by rewrite C.expr1.
qed.

lemma omega512_pow128_minus_i :
  cpow omega512 128 = cneg ci.
proof. by rewrite omega512_pow128 /omega4. qed.

lemma omega512_pow256 :
  cpow omega512 256 = cneg cone.
proof.
rewrite (_ : 256 = 128 * 2) 1:// C.exprM omega512_pow128 C.expr2.
exact omega4_square.
qed.

lemma omega512_pow512 :
  cpow omega512 512 = cone.
proof.
rewrite (_ : 512 = 256 * 2) 1:// C.exprM omega512_pow256 C.expr2.
apply complex_ext.
+ rewrite /cmul /cneg /cone /creal /cimag /=.
  ring.
+ by rewrite /cmul /cneg /cone /creal /cimag /=.
qed.

lemma cneg_one_neq_one :
  cneg cone <> cone.
proof.
rewrite /cneg /cone /creal /cimag /=.
smt().
qed.

(* For an element already known to have 512th power one, checking the
   half-order power is the standard power-of-two primitivity criterion.
   The name records exactly what is checked; no finite-group library is
   silently assumed here. *)
op power_of_two_primitive_512_criterion (z : complex) : bool =
  cpow z 512 = cone /\ cpow z 256 <> cone.

lemma omega512_power_of_two_primitive_criterion :
  power_of_two_primitive_512_criterion omega512.
proof.
rewrite /power_of_two_primitive_512_criterion
        omega512_pow512 omega512_pow256.
exact cneg_one_neq_one.
qed.

(* Abstract ideal roots and a finite, unnormalised 256-point transform.
   These operations intentionally contain no extracted Q16 table. *)
op ideal_root (j : int) : complex =
  cpow omega512 j.

op dft_root : complex =
  ideal_root 2.

op odd_root (k : int) : complex =
  ideal_root (2 * k + 1).

op csum (xs : complex list) : complex =
  foldr cadd czero xs.

op csum256 (f : int -> complex) : complex =
  csum (map f (iota_ 0 256)).

op dft256 (input : int -> complex) (k : int) : complex =
  csum256
    (fun j => cmul (input j) (cpow dft_root (k * j))).

op twist256 (input : int -> complex) (j : int) : complex =
  cmul (input j) (ideal_root j).

op odd_dft256 (input : int -> complex) (k : int) : complex =
  csum256
    (fun j => cmul (input j) (cpow (odd_root k) j)).

lemma dft_rootE :
  dft_root = cpow omega512 2.
proof. by rewrite /dft_root /ideal_root. qed.

lemma odd_rootE k :
  odd_root k = cpow omega512 (2 * k + 1).
proof. by rewrite /odd_root /ideal_root. qed.

lemma ideal_root_power (a b : int) :
  cpow (ideal_root a) b = ideal_root (a * b).
proof. by rewrite /ideal_root -C.exprM. qed.

lemma dft_root_power (n : int) :
  cpow dft_root n = ideal_root (2 * n).
proof. by rewrite /dft_root ideal_root_power. qed.

lemma odd_kernel_twist (k j : int) :
  0 <= k =>
  0 <= j =>
  cpow (odd_root k) j =
  cmul (ideal_root j) (cpow dft_root (k * j)).
proof.
move=> hk hj.
rewrite /odd_root ideal_root_power dft_root_power.
rewrite /ideal_root -C.exprD_nneg 1:hj 1:/#.
congr.
ring.
qed.

lemma odd_dft_term_twist (input : int -> complex) (k j : int) :
  0 <= k =>
  0 <= j =>
  cmul (input j) (cpow (odd_root k) j) =
  cmul (twist256 input j) (cpow dft_root (k * j)).
proof.
move=> hk hj.
rewrite /twist256 (odd_kernel_twist k j hk hj).
by rewrite -cmulA.
qed.

lemma odd_dft256_twist (input : int -> complex) (k : int) :
  0 <= k =>
  odd_dft256 input k = dft256 (twist256 input) k.
proof.
move=> hk.
rewrite /odd_dft256 /dft256 /csum256.
congr.
apply/eq_in_map => j.
rewrite mem_iota => hj.
have hj0 : 0 <= j by smt().
exact (odd_dft_term_twist input k j hk hj0).
qed.

end KeygenM23IdealRootDFT.
