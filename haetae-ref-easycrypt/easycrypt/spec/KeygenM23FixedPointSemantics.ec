require import AllCore IntDiv Ring.

from Jasmin require import JUtils JModel_x86.

import SLH64.

require import KeygenM23SingularSpec Fq.

theory KeygenM23FixedPointSemantics.

op q16_scale : int = 65536.
op q16_half : int = 32768.

op q16_round (z : int) : int =
  (z + q16_half) %/ q16_scale.

op mulrnd16_int (x y : int) : int =
  q16_round (x * y).

op mulrnd16_result_fits (x y : int) : bool =
  W32.min_sint <= mulrnd16_int x y <= W32.max_sint.

lemma q16_round_error (z : int) :
  -q16_half <
    q16_round z * q16_scale - z <=
      q16_half.
proof.
have hdiv := divz_eq (z + q16_half) q16_scale.
have hmod := modz_cmp (z + q16_half) q16_scale.
rewrite /q16_round.
rewrite /q16_scale /q16_half in hdiv.
rewrite /q16_scale /q16_half in hmod.
rewrite /q16_scale /q16_half.
smt().
qed.

lemma sigextu64_semantics (a : W32.t) :
  sigextu64 a = W64.of_int (W32.to_sint a).
proof. by rewrite /sigextu64. qed.

lemma pow2_minus_one_odd (n : int) :
  1 <= n =>
  (2 ^ n - 1) %% 2 = 1.
proof.
move=> hn.
have hnE : n = (n - 1) + 1 by ring.
rewrite {1}hnE exprSr 1:/#.
have -> : 2 ^ (n - 1) * 2 - 1 =
    (2 ^ (n - 1) - 1) * 2 + 1 by ring.
by rewrite modzMDl.
qed.

lemma of_int_high_bits48 (z i : int) :
  -140737488355328 <= z < 140737488355328 =>
  47 <= i < 64 =>
  (W64.of_int z).[i] = (W64.of_int z).[47].
proof.
move=> hz hi.
rewrite !W64.of_intwE /W64.int_bit /=.
case (0 <= z) => hzsign.
+ have hmod64 :
      z %% 18446744073709551616 = z by
      rewrite modz_small 1:/#.
  rewrite hmod64.
  have hpowi : 140737488355328 <= 2 ^ i by
    rewrite (_ : 140737488355328 = 2 ^ 47) //;
    apply StdOrder.IntOrder.ler_weexpn2l => //; smt().
  have hdivi : z %/ 2 ^ i = 0 by
    rewrite divz_small 1:/#.
  have hdiv47 : z %/ 140737488355328 = 0 by
    rewrite divz_small 1:/#.
  by rewrite hdivi hdiv47.
have hmod64 :
    z %% 18446744073709551616 =
      18446744073709551616 + z by
  rewrite -(modzDl z 18446744073709551616)
          modz_small 1:/#.
rewrite hmod64.
have hquot : forall j,
  47 <= j < 64 =>
    (18446744073709551616 + z) %/ 2 ^ j =
      2 ^ (64 - j) - 1.
+ move=> j hj.
  have hpowj : 140737488355328 <= 2 ^ j.
  + rewrite (_ : 140737488355328 = 2 ^ 47) //.
    apply StdOrder.IntOrder.ler_weexpn2l => //.
    smt().
  have hpow64 :
      18446744073709551616 = 2 ^ (64 - j) * 2 ^ j.
  + rewrite -exprD_nneg.
    + smt().
    + smt().
    rewrite (_ : 18446744073709551616 = 2 ^ 64) //.
    congr.
    ring.
  have hdecomp :
      18446744073709551616 + z =
        (2 ^ (64 - j) - 1) * 2 ^ j + (2 ^ j + z).
  + rewrite hpow64.
    ring.
  rewrite hdecomp divzMDl.
  + have hpos : 0 < 2 ^ j by apply gt0_pow2.
    smt().
  rewrite divz_small.
  + apply bound_abs.
    smt().
  by ring.
rewrite (hquot i hi) (hquot 47) 1:/#.
rewrite !pow2_minus_one_odd 1,2:/#.
smt().
qed.

lemma sar16_sar32_scale_small (z : int) :
  -140737488355328 <= z < 140737488355328 =>
  W64.sar (W64.of_int z) 16 =
    W64.sar (W64.of_int (z * q16_scale)) 32.
proof.
move=> hz.
have hshift :
    W64.of_int (z * q16_scale) = W64.of_int z `<<<` 16.
+ rewrite W64.shlMP 1:/#.
  rewrite /q16_scale.
  congr.
  ring.
rewrite hshift.
apply W64.ext_eq => i hi.
rewrite /W64.sar /W64.(`|>>>`) !W64.initiE 1:hi 1:hi.
case (i < 32).
+ move=> hlo.
  have hmin16 : min 63 (i + 16) = i + 16 by smt().
  have hmin32 : min 63 (i + 32) = i + 32 by smt().
  by rewrite hmin16 hmin32 /=; smt().
+ move=> hhi.
have hmin32 : min 63 (i + 32) = 63 by smt().
rewrite hmin32 W64.shlwE /=.
rewrite of_int_high_bits48 1:hz.
+ smt().
done.
qed.

lemma sar16_of_int_result_fit (z : int) :
  W32.min_sint <= z %/ q16_scale <= W32.max_sint =>
  W64.sar (W64.of_int z) 16 =
    W64.of_int (z %/ q16_scale).
proof.
move=> hfit.
have hdiv := divz_eq z q16_scale.
have hmod := modz_cmp z q16_scale.
have hz : -140737488355328 <= z < 140737488355328.
+ rewrite /q16_scale in hfit.
  rewrite /q16_scale in hdiv.
  rewrite /q16_scale in hmod.
  smt().
rewrite sar16_sar32_scale_small 1:hz.
have hzscaled :
    W64.min_sint <= z * q16_scale <= W64.max_sint.
+ rewrite /q16_scale in hz.
  rewrite /q16_scale.
  smt().
have hsint :
    W64.to_sint (W64.of_int (z * q16_scale)) =
      z * q16_scale.
+ apply W64.to_sintK_small.
  exact hzscaled.
have hsem := Fq.SAR_sem32
  (W64.of_int (z * q16_scale)).
rewrite /(`|>>`) W8.of_uintK /= hsint in hsem.
rewrite hsem.
congr.
rewrite /q16_scale
        (_ : 4294967296 = 65536 * 65536) //.
by rewrite divzMpr 1:/#.
qed.

lemma mulrnd16_word_of_int (x y : W32.t) :
  mulrnd16_result_fits (W32.to_sint x) (W32.to_sint y) =>
  KeygenM23SingularSpec.mulrnd16_word x y =
    W32.of_int (mulrnd16_int (W32.to_sint x) (W32.to_sint y)).
proof.
move=> hfit.
pose z := W32.to_sint x * W32.to_sint y + q16_half.
have hqfit :
    W32.min_sint <= z %/ q16_scale <= W32.max_sint.
+ move: hfit.
  rewrite /mulrnd16_result_fits /mulrnd16_int /q16_round /z.
  done.
rewrite /KeygenM23SingularSpec.mulrnd16_word
        !sigextu64_semantics
        W64.of_intM' W64.of_intD'.
rewrite (_ :
    W32.to_sint x * W32.to_sint y + 32768 = z).
+ by rewrite /z /q16_half.
rewrite /(`|>>`) W8.of_uintK /=.
rewrite sar16_of_int_result_fit 1:hqfit.
apply W32.to_uint_eq.
rewrite /truncateu32 !W32.of_uintK W64.of_uintK.
rewrite /mulrnd16_int /q16_round /z /q16_half.
have hptr : ptr_modulus = 2 ^ 64 by done.
have hw32 : W32.modulus = 2 ^ 32 by done.
by rewrite hptr hw32 modz_mod_pow2 /=.
qed.

lemma mulrnd16_word_to_sint (x y : W32.t) :
  mulrnd16_result_fits (W32.to_sint x) (W32.to_sint y) =>
  W32.to_sint (KeygenM23SingularSpec.mulrnd16_word x y) =
    mulrnd16_int (W32.to_sint x) (W32.to_sint y).
proof.
move=> hfit.
rewrite mulrnd16_word_of_int 1:hfit.
apply W32.to_sintK_small.
exact hfit.
qed.

end KeygenM23FixedPointSemantics.
