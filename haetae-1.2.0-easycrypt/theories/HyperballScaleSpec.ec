require import AllCore IntDiv List StdOrder.
from Jasmin require import JModel_x86.
require import BArray16 BArray512 BArray8192 BArray32768
               HyperballFixedPointSpec HyperballNormSpec.

theory HyperballScaleSpec.

op hb_scale_bounds (l total : int) : bool =
  0 <= l <= 2048 /\ 0 <= total - l <= 2048 /\ total <= 4096.

op hb_sign_bit (signs : BArray512.t) (i : int) : W8.t =
  W8.of_int (b2i (BArray512.get8 signs (i %/ 8)).[i %% 8]).

op hb_scaled_coeff (samples : BArray32768.t) (signs : BArray512.t)
    (scale : BArray16.t) (i : int) : W32.t =
  hb_scale_sample (BArray32768.get64 samples i) scale (hb_sign_bit signs i).

(* Bytewise construction makes the untouched tail explicit. The callback
   produces exact signed/rounded W32 words, retaining the scalar word wraps. *)
op hb_scaled_output (before : BArray8192.t) (coeff : int -> W32.t)
    (base count : int) : BArray8192.t =
  BArray8192.init (fun j => if j < 4 * count
    then coeff (base + j %/ 4) \bits8 (j %% 4) else BArray8192.get8 before j).

op hb_scale_result (before1 before2 : BArray8192.t)
    (samples : BArray32768.t) (signs : BArray512.t) (scale : BArray16.t)
    (l total : int) : BArray8192.t * BArray8192.t =
  (hb_scaled_output before1 (hb_scaled_coeff samples signs scale) 0 l,
   hb_scaled_output before2 (hb_scaled_coeff samples signs scale) l (total - l)).

op hb_output_frame (before after : BArray8192.t) (count : int) : bool =
  forall j, 4 * count <= j < 8192 =>
    BArray8192.get8 after j = BArray8192.get8 before j.

op hb_scale_norm (before1 before2 : BArray8192.t)
    (samples : BArray32768.t) (signs : BArray512.t) (scale : BArray16.t)
    (l total : int) : int =
  let result = hb_scale_result before1 before2 samples signs scale l total in
  hyperball_sqnorm result.`1 l result.`2 (total - l).

(* The actual acceptance test is unsigned comparison after reduction modulo
   2^64. An integer geometric-norm interpretation needs a separate bound. *)
op hb_scale_check_result (before1 before2 : BArray8192.t)
    (samples : BArray32768.t) (signs : BArray512.t) (scale : BArray16.t)
    (l total : int) (bound : W64.t) : BArray8192.t * BArray8192.t * W64.t =
  let result = hb_scale_result before1 before2 samples signs scale l total in
  (result.`1, result.`2,
   W64.of_int (b2i (hb_scale_norm before1 before2 samples signs scale l total
     %% W64.modulus <= W64.to_uint bound))).

lemma hb_scaled_output_get8 before coeff base count j : 0 <= j < 8192 =>
  BArray8192.get8 (hb_scaled_output before coeff base count) j =
    if j < 4 * count then coeff (base + j %/ 4) \bits8 (j %% 4)
    else BArray8192.get8 before j.
proof. by move=> hj; rewrite /hb_scaled_output BArray8192.initiE. qed.

lemma hb_scaled_output0 before coeff base :
  hb_scaled_output before coeff base 0 = before.
proof.
  apply BArray8192.ext_eq => j hj.
  rewrite hb_scaled_output_get8 1:hj /=; smt().
qed.

lemma hb_scaled_output_get32 before coeff base count i :
  0 <= count <= 2048 => 0 <= i < 2048 =>
  BArray8192.get32 (hb_scaled_output before coeff base count) i =
    if i < count then coeff (base + i) else BArray8192.get32 before i.
proof.
  move=> hc hi; apply W4u8.wordP => byte hb.
  rewrite BArray8192.get32d_byte 1:hb.
  have hidx : 0 <= 4 * i + byte < 8192 by smt().
  rewrite hb_scaled_output_get8 1:hidx.
  have hd : (4 * i + byte) %/ 4 = i by rewrite divz_eqP //; smt().
  have hm : (4 * i + byte) %% 4 = byte by
    rewrite (mulzC 4 i) modzMDl modz_small; smt().
  have he : (4 * i + byte < 4 * count) = (i < count) by smt().
  rewrite hd hm he.
  case (i < count) => hit /=; first trivial.
  by rewrite BArray8192.get32d_byte.
qed.

lemma hb_scaled_output_step before coeff base count : 0 <= count < 2048 =>
  BArray8192.set32 (hb_scaled_output before coeff base count) count
      (coeff (base + count)) = hb_scaled_output before coeff base (count + 1).
proof.
  move=> hc; apply BArray8192.ext_eq32 => i hi.
  have hic : 0 <= i < 2048 by smt().
  have hn : 0 <= count <= 2048 by smt().
  have hn1 : 0 <= count + 1 <= 2048 by smt().
  rewrite BArray8192.get_set32E 1:/# 1:/#.
  rewrite (hb_scaled_output_get32 before coeff base count i hn hic).
  rewrite (hb_scaled_output_get32 before coeff base (count + 1) i hn1 hic).
  smt().
qed.

lemma hb_scaled_output_frame before coeff base count : 0 <= count <= 2048 =>
  hb_output_frame before (hb_scaled_output before coeff base count) count.
proof.
  move=> hc; rewrite /hb_output_frame => j hj.
  rewrite hb_scaled_output_get8 1:/#; smt().
qed.

lemma hb_scaled_output_extensional before after coeff coeff' base count :
  0 <= count <= 2048 =>
  (forall i, 0 <= i < count => coeff (base + i) = coeff' (base + i)) =>
  (forall j, 4 * count <= j < 8192 => BArray8192.get8 before j = BArray8192.get8 after j) =>
  hb_scaled_output before coeff base count = hb_scaled_output after coeff' base count.
proof.
  move=> hc hv ht; apply BArray8192.ext_eq => j hj.
  rewrite !hb_scaled_output_get8 1..2:hj.
  case (j < 4 * count) => hinside /=; last by apply ht; smt().
  have hq : 0 <= j %/ 4 < count by smt(divz_cmp).
  by rewrite (hv (j %/ 4) hq).
qed.

lemma hb_scale_result_layout before1 before2 samples signs scale l total :
  hb_scale_bounds l total =>
  (forall i, 0 <= i < 2048 =>
    BArray8192.get32 (hb_scale_result before1 before2 samples signs scale l total).`1 i =
    if i < l then hb_scaled_coeff samples signs scale i else BArray8192.get32 before1 i) /\
  (forall i, 0 <= i < 2048 =>
    BArray8192.get32 (hb_scale_result before1 before2 samples signs scale l total).`2 i =
    if i < total - l then hb_scaled_coeff samples signs scale (l + i)
    else BArray8192.get32 before2 i) /\
  hb_output_frame before1 (hb_scale_result before1 before2 samples signs scale l total).`1 l /\
  hb_output_frame before2 (hb_scale_result before1 before2 samples signs scale l total).`2 (total - l).
proof.
  rewrite /hb_scale_bounds /hb_scale_result /=; move=> [hl [hk ht]].
  do split.
  + move=> i hi; by rewrite hb_scaled_output_get32 1:hl 1:hi /=.
  + move=> i hi; by rewrite hb_scaled_output_get32 1:hk 1:hi /=.
  + exact (hb_scaled_output_frame before1 _ 0 l hl).
  exact (hb_scaled_output_frame before2 _ l (total-l) hk).
qed.

lemma hb_scale_result_extensional
    before1 before2 after1 after2 samples samples' signs signs' scale l total :
  hb_scale_bounds l total =>
  (forall i, 0 <= i < total => BArray32768.get64 samples i = BArray32768.get64 samples' i) =>
  (forall j, 0 <= 8 * j < total => BArray512.get8 signs j = BArray512.get8 signs' j) =>
  (forall j, 4 * l <= j < 8192 => BArray8192.get8 before1 j = BArray8192.get8 after1 j) =>
  (forall j, 4 * (total-l) <= j < 8192 => BArray8192.get8 before2 j = BArray8192.get8 after2 j) =>
  hb_scale_result before1 before2 samples signs scale l total =
    hb_scale_result after1 after2 samples' signs' scale l total.
proof.
  rewrite /hb_scale_bounds; move=> [hl [hk ht]] hs hsign ht1 ht2.
  have hc : forall i, 0 <= i < total =>
    hb_scaled_coeff samples signs scale i = hb_scaled_coeff samples' signs' scale i.
  + move=> i hi; rewrite /hb_scaled_coeff /hb_sign_bit (hs i hi).
    have hq : 0 <= 8 * (i %/ 8) < total by smt(divz_eq divz_cmp modz_cmp).
    by rewrite (hsign (i %/ 8) hq).
  have h1 : hb_scaled_output before1 (hb_scaled_coeff samples signs scale) 0 l =
    hb_scaled_output after1 (hb_scaled_coeff samples' signs' scale) 0 l.
  + apply hb_scaled_output_extensional => //.
    move=> i hi; apply hc; smt().
  have h2 : hb_scaled_output before2 (hb_scaled_coeff samples signs scale) l (total-l) =
    hb_scaled_output after2 (hb_scaled_coeff samples' signs' scale) l (total-l).
  + apply hb_scaled_output_extensional => //.
    move=> i hi; apply hc; smt().
  by rewrite /hb_scale_result h1 h2.
qed.

lemma hb_scale_norm_nonnegative before1 before2 samples signs scale l total :
  hb_scale_bounds l total => 0 <= hb_scale_norm before1 before2 samples signs scale l total.
proof.
  rewrite /hb_scale_bounds /hb_scale_norm /=; move=> [hl [hk ht]].
  apply hyperball_sqnorm_nonnegative; smt().
qed.

lemma hb_scale_accept_integer before1 before2 samples signs scale l total bound :
  hb_scale_bounds l total =>
  hb_scale_norm before1 before2 samples signs scale l total < W64.modulus =>
  (hb_scale_check_result before1 before2 samples signs scale l total bound).`3 =
    W64.of_int (b2i (hb_scale_norm before1 before2 samples signs scale l total <= W64.to_uint bound)).
proof.
  move=> hd hf; have hz := hb_scale_norm_nonnegative before1 before2 samples signs scale l total hd.
  by rewrite /hb_scale_check_result /= modz_small 1:/#.
qed.

lemma hb_scale_check_result_extensional
    before1 before2 after1 after2 samples samples' signs signs' scale l total bound :
  hb_scale_bounds l total =>
  (forall i, 0 <= i < total => BArray32768.get64 samples i = BArray32768.get64 samples' i) =>
  (forall j, 0 <= 8 * j < total => BArray512.get8 signs j = BArray512.get8 signs' j) =>
  (forall j, 4 * l <= j < 8192 => BArray8192.get8 before1 j = BArray8192.get8 after1 j) =>
  (forall j, 4 * (total-l) <= j < 8192 => BArray8192.get8 before2 j = BArray8192.get8 after2 j) =>
  hb_scale_check_result before1 before2 samples signs scale l total bound =
    hb_scale_check_result after1 after2 samples' signs' scale l total bound.
proof.
  move=> hd hs hb ht1 ht2.
  have hr := hb_scale_result_extensional before1 before2 after1 after2
    samples samples' signs signs' scale l total hd hs hb ht1 ht2.
  have hn : hb_scale_norm before1 before2 samples signs scale l total =
    hb_scale_norm after1 after2 samples' signs' scale l total by
    rewrite /hb_scale_norm hr.
  by rewrite /hb_scale_check_result hr hn.
qed.

lemma hb_counts_low l total : hb_scale_bounds l total =>
  W64.of_int (total * 4294967296 + l) `&` W64.of_int 4294967295 = W64.of_int l.
proof.
  rewrite /hb_scale_bounds; move=> [hl [hk ht]].
  have -> : W64.of_int 4294967295 = W64.of_int (2^32 - 1) by trivial.
  rewrite W64.and_mod 1:// W64.of_uintK /=.
  rewrite (modz_small (total * 4294967296 + l) 18446744073709551616) 1:/#.
  by rewrite modzMDl modz_small 1:/#.
qed.

lemma hb_counts_high l total : hb_scale_bounds l total =>
  W64.of_int (total * 4294967296 + l) `>>>` 32 = W64.of_int total.
proof.
  rewrite /hb_scale_bounds; move=> [hl [hk ht]].
  apply W64.to_uint_eq.
  rewrite W64.to_uint_shr 1:// !W64.of_uintK /=.
  rewrite (modz_small (total * 4294967296 + l) 18446744073709551616) 1:/#.
  rewrite (modz_small total 18446744073709551616) 1:/#.
  by rewrite divz_eqP //; smt().
qed.

end HyperballScaleSpec.
