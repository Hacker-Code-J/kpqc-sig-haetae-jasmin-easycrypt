require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import SigmaSpec HyperballFixedPointSpec.

(* All integer casts below retain their modular semantics. No limb is
   assumed to be canonical or to encode a nonnegative signed word. *)
lemma hwe_uint a : W64.to_uint (W64.of_int a) = a %% 18446744073709551616.
proof. by rewrite W64.of_uintK. qed.

lemma hwe_sint a : W64.to_sint (W64.of_int a) =
  if 9223372036854775808 <= a %% 18446744073709551616
  then a %% 18446744073709551616 - 18446744073709551616
  else a %% 18446744073709551616.
proof. by rewrite W64.of_sintK /W64.smod. qed.

lemma hwe_sint32 a : W32.to_sint (W32.of_int a) =
  if 2147483648 <= a %% 4294967296 then a %% 4294967296 - 4294967296
  else a %% 4294967296.
proof. by rewrite W32.of_sintK /W32.smod. qed.

lemma hwe_add a b : W64.of_int a + W64.of_int b = W64.of_int (a+b).
proof. exact (W64.of_intD' a b). qed.

lemma hwe_sub a b : W64.of_int a - W64.of_int b = W64.of_int (a-b).
proof. by rewrite W64.of_intD W64.of_intN. qed.

lemma hwe_mul a b : W64.of_int a * W64.of_int b = W64.of_int (a*b).
proof. exact (W64.of_intM a b). qed.

lemma hwe_shl a k : 0 <= k =>
  W64.of_int a `<<<` k = W64.of_int (a * 2^k).
proof. exact (W64.shlMP a k). qed.

lemma hwe_shr a k : 0 <= k =>
  W64.of_int a `>>>` k = W64.of_int ((a %% 18446744073709551616) %/ 2^k).
proof. exact (W64.shrDP a k). qed.

lemma hwe_shr_word (a : W64.t) k : 0 <= k =>
  a `>>>` k = W64.of_int (W64.to_uint a %/ 2^k).
proof.
  move=> hk; rewrite -{1}(W64.to_uintK (a `>>>` k)).
  by rewrite W64.to_uint_shr.
qed.

lemma hwe_mask a k : 0 <= k =>
  W64.of_int a `&` W64.of_int (2^k-1) =
    W64.of_int ((a %% 18446744073709551616) %% 2^k).
proof. move=> hk; by rewrite W64.and_mod 1:hk W64.of_uintK. qed.

lemma hwe_not a : invw (W64.of_int a) = W64.of_int (-a-1).
proof.
  have h := W64.twos_compl (W64.of_int a).
  rewrite W64.of_intD !W64.of_intN h; ring.
qed.

lemma hwe_xor_disjoint (a b : W64.t) : a `&` b = W64.zero => a `^` b = a+b.
proof.
  move=> hd; by rewrite -(W64.orw_disjoint a b hd) W64.orw_xorw hd W64.xorw0_s.
qed.

lemma hwe_xor_arithmetic (a b : W64.t) :
  a `^` b = a+b-((a `&` b)+(a `&` b)).
proof.
  have hd : (a `^` b) `&` (a `&` b) = W64.zero.
  + apply W64.wordP => i hi.
    rewrite !W64.andwE !W64.xorwE W64.zerowE; smt().
  have hj : a `|` b = (a `^` b)+(a `&` b).
  + by rewrite W64.orw_xorw (hwe_xor_disjoint _ _ hd).
  have he : a `^` b = (a `|` b)-(a `&` b) by rewrite hj; ring.
  rewrite he W64.orw_xpnd; ring.
qed.

lemma hwe_xor_mask a k : 0 <= k =>
  W64.of_int a `^` W64.of_int (2^k-1) =
    W64.of_int ((a %% 18446744073709551616)+(2^k-1)-
      2*((a %% 18446744073709551616) %% 2^k)).
proof.
  move=> hk; rewrite hwe_xor_arithmetic (hwe_mask a k hk).
  rewrite -(W64.of_int_mod a) !hwe_add hwe_sub.
  congr; ring.
qed.

lemma hwe_mulu_word (a b : W64.t) :
  mulu_64 a b =
    (W64.of_int ((W64.to_uint a * W64.to_uint b) %/ 18446744073709551616),
      W64.of_int (W64.to_uint a * W64.to_uint b)).
proof. by rewrite W64.muluE /W64.mulhi -W64.of_intM !W64.to_uintK. qed.

lemma hwe_mulu a b :
  mulu_64 (W64.of_int a) (W64.of_int b) =
    (W64.of_int (((a %% 18446744073709551616)*(b %% 18446744073709551616)) %/
      18446744073709551616),
      W64.of_int ((a %% 18446744073709551616)*(b %% 18446744073709551616))).
proof. by rewrite hwe_mulu_word !W64.of_uintK. qed.

lemma hwe_split48 (product : int) :
  product %/ 281474976710656 =
    (product %/ 18446744073709551616)*65536 +
      (product %% 18446744073709551616) %/ 281474976710656.
proof.
  have hd := divz_eq product 18446744073709551616.
  have he : product =
    ((product %/ 18446744073709551616)*65536)*281474976710656 +
      product %% 18446744073709551616 by smt().
  by rewrite {1}he divzMDl.
qed.

lemma hwe_mul48_word (a b : W64.t) :
  mul48_word a b =
    (W64.of_int ((W64.to_uint a * W64.to_uint b) %% 281474976710656),
      W64.of_int ((W64.to_uint a * W64.to_uint b) %/ 281474976710656)).
proof.
  have hd : (W64.mulhi a b `<<<` 16) `&` ((a*b) `>>>` 48) = W64.zero.
  + rewrite W64.andwC; apply W64.shrw_shlw_disjoint; trivial.
  have hlo : (a*b) `&` W64.of_int 281474976710655 =
      W64.of_int ((W64.to_uint a * W64.to_uint b) %% 281474976710656).
  + have -> : 281474976710655 = 2^48-1 by trivial.
    rewrite W64.and_mod // W64.to_uintM /= modz_dvd; trivial.
  have hhi : (W64.mulhi a b `<<<` 16) `^` ((a*b) `>>>` 48) =
      W64.of_int ((W64.to_uint a * W64.to_uint b) %/ 281474976710656).
  + rewrite (hwe_xor_disjoint _ _ hd) /W64.mulhi hwe_shl 1://
      hwe_shr_word 1:// W64.to_uintM /=.
    rewrite -hwe_split48.
    trivial.
  by rewrite /mul48_word W64.muluE /= hlo hhi.
qed.

lemma hwe_mul48 a b :
  mul48_word (W64.of_int a) (W64.of_int b) =
    (W64.of_int (((a %% 18446744073709551616)*(b %% 18446744073709551616)) %%
      281474976710656),
      W64.of_int (((a %% 18446744073709551616)*(b %% 18446744073709551616)) %/
        281474976710656)).
proof. by rewrite hwe_mul48_word !W64.of_uintK. qed.

lemma hwe_mask48 a : W64.of_int a `&` W64.of_int 281474976710655 =
  W64.of_int ((a %% 18446744073709551616) %% 281474976710656).
proof. have h := hwe_mask a 48 _; first trivial. by move: h; rewrite /=. qed.

lemma hwe_mask32 a : W64.of_int a `&` W64.of_int 4294967295 =
  W64.of_int ((a %% 18446744073709551616) %% 4294967296).
proof. have h := hwe_mask a 32 _; first trivial. by move: h; rewrite /=. qed.

lemma hwe_mask1 a : W64.of_int a `&` W64.one =
  W64.of_int ((a %% 18446744073709551616) %% 2).
proof. have h := hwe_mask a 1 _; first trivial. by move: h; rewrite /=. qed.

lemma hwe_xor48 a : W64.of_int a `^` W64.of_int 281474976710655 =
  W64.of_int ((a %% 18446744073709551616)+281474976710655-
    2*((a %% 18446744073709551616) %% 281474976710656)).
proof. have h := hwe_xor_mask a 48 _; first trivial. by move: h; rewrite /=. qed.

lemma hwe_xor_minus_one a : W64.of_int a `^` W64.of_int (-1) = W64.of_int (-a-1).
proof. by rewrite W64.of_intN W64.minus_one W64.xorw1 hwe_not. qed.

lemma hwe_xor48_inc a :
  (W64.of_int a `^` W64.of_int 281474976710655)+W64.one =
    W64.of_int ((a %% 18446744073709551616)+281474976710656-
      2*((a %% 18446744073709551616) %% 281474976710656)).
proof. rewrite hwe_xor48 ?hwe_add; congr; ring. qed.

lemma hwe_norm a b : hb_norm (W64.of_int a,W64.of_int b) =
  (W64.of_int ((a %% 18446744073709551616) %% 281474976710656),
    W64.of_int (b + (a %% 18446744073709551616) %/ 281474976710656)).
proof. by rewrite /hb_norm /= hwe_mask48 hwe_shr 1:// /=. qed.

lemma hwe_cneg0 a b :
  hb_cneg (W64.of_int a,W64.of_int b) W64.zero = hb_norm (W64.of_int a,W64.of_int b).
proof. by rewrite /hb_cneg /=. qed.

lemma hwe_cneg1 a b : hb_cneg (W64.of_int a,W64.of_int b) W64.one =
  hb_norm
    (W64.of_int ((a %% 18446744073709551616)+281474976710656-
      2*((a %% 18446744073709551616) %% 281474976710656)),
      W64.of_int (-b-1)).
proof.
  rewrite /hb_cneg /= hwe_mask48 /=.
  rewrite (W64.xorwC (W64.of_int 281474976710655) (W64.of_int a))
    hwe_xor48_inc hwe_xor_minus_one.
  trivial.
qed.

(* For concrete replay, unfold one hb operation at a time, rewrite products
   with hwe_mul48/hwe_mulu, then use hwe_shl/hwe_shr, hwe_mask48/32/1 and
   hwe_add/sub/mul. Finally use hwe_norm and evaluate the integer div/mod.
   Signs 0/1 use hwe_cneg0/1. Never discard an intermediate modulo on the
   assumption that a fixed-point limb is canonical. *)
