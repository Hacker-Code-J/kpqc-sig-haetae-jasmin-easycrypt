require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import ApiTarget HyperballNormSpec.

theory HyperballNormCorrectness.
module Signer = ApiTarget.M(ApiTarget.Syscall).

lemma signed32_square_word (x : W32.t) :
  sigextu64 x * sigextu64 x = W64.of_int (W32.to_sint x * W32.to_sint x).
proof. by rewrite /sigextu64 -W64.of_intM. qed.

lemma signed32_square_uint (x : W32.t) :
  W64.to_uint (sigextu64 x * sigextu64 x) = W32.to_sint x * W32.to_sint x.
proof.
have /= hx := W32.to_sint_cmp x.
rewrite signed32_square_word W64.to_uint_small 1:/#.
trivial.
qed.

lemma norm_counter_next (i : W64.t) :
  0 <= W64.to_uint i < 2048 =>
  W64.to_uint (i + W64.one) = W64.to_uint i + 1.
proof.
move=> hi; rewrite W64.to_uintD W64.to_uint1 modz_small 1:/#; trivial.
qed.

lemma polyfixveclk_sqnorm2_correct
    (ap0 : BArray8192.t) (na : int) (bp0 : BArray8192.t) (nb : int) :
  hoare [Signer._polyfixveclk_sqnorm2_2048 :
    ap = ap0 /\ acount = W64.of_int na /\ bp = bp0 /\ bcount = W64.of_int nb /\
    0 <= na <= 2048 /\ 0 <= nb <= 2048
    ==>
    res = W64.of_int (hyperball_sqnorm ap0 na bp0 nb)].
proof.
proc.
while (bp = bp0 /\ bcount = W64.of_int nb /\ 0 <= nb <= 2048 /\
       0 <= W64.to_uint i <= nb /\
       total = W64.of_int (hyperball_prefix_sqnorm ap0 na +
         hyperball_prefix_sqnorm bp0 (W64.to_uint i))).
+ auto => /> &hr hnb0 hnbmax hi0 hin hguard.
  have hi : W64.to_uint i{hr} < nb by
    move: hguard; rewrite W64.ultE W64.to_uint_small 1:/#.
  rewrite norm_counter_next 1:/# signed32_square_word -W64.of_intD.
  split; first smt().
  rewrite hyperball_prefix_sqnormS 1:hi0 /hyperball_coeff_square.
  congr; ring.
wp.
while (ap = ap0 /\ acount = W64.of_int na /\
       bp = bp0 /\ bcount = W64.of_int nb /\
       0 <= na <= 2048 /\ 0 <= nb <= 2048 /\
       0 <= W64.to_uint i <= na /\
       total = W64.of_int (hyperball_prefix_sqnorm ap0 (W64.to_uint i))).
+ auto => /> &hr hna0 hnamax hnb0 hnbmax hi0 hin hguard.
  have hi : W64.to_uint i{hr} < na by
    move: hguard; rewrite W64.ultE W64.to_uint_small 1:/#.
  rewrite norm_counter_next 1:/# signed32_square_word -W64.of_intD.
  split; first smt().
  by rewrite hyperball_prefix_sqnormS 1:hi0 /hyperball_coeff_square.
auto => /> hna0 hnamax hnb0 hnbmax.
rewrite !hyperball_prefix_sqnorm0 /=.
move=> i hdone hi0 hin.
have hi : W64.to_uint i = na by
  move: hdone; rewrite W64.ultE W64.to_uint_small 1:/#; smt().
rewrite hi /=.
move=> j hdonej hj0 hjn.
have hj : W64.to_uint j = nb by
  move: hdonej; rewrite W64.ultE W64.to_uint_small 1:/#; smt().
by rewrite hj /hyperball_sqnorm.
qed.

lemma polyfixveclk_sqnorm2_ll : islossless Signer._polyfixveclk_sqnorm2_2048.
proof.
proc.
while (W64.to_uint i <= W64.to_uint bcount)
      (W64.to_uint bcount - W64.to_uint i).
+ move=> z; auto => /> &hr hi hguard.
  have /= hb := W64.to_uint_cmp bcount{hr}.
  rewrite W64.ultE in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
wp.
while (W64.to_uint i <= W64.to_uint acount)
      (W64.to_uint acount - W64.to_uint i).
+ move=> z; auto => /> &hr hi hguard.
  have /= ha := W64.to_uint_cmp acount{hr}.
  rewrite W64.ultE in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
auto => />.
smt(W64.to_uint_cmp W64.ultE).
qed.

lemma polyfixveclk_sqnorm2_total_correct
    (ap0 : BArray8192.t) (na : int) (bp0 : BArray8192.t) (nb : int) :
  phoare [Signer._polyfixveclk_sqnorm2_2048 :
    ap = ap0 /\ acount = W64.of_int na /\ bp = bp0 /\ bcount = W64.of_int nb /\
    0 <= na <= 2048 /\ 0 <= nb <= 2048
    ==>
    res = W64.of_int (hyperball_sqnorm ap0 na bp0 nb)] = 1%r.
proof.
by conseq polyfixveclk_sqnorm2_ll (polyfixveclk_sqnorm2_correct ap0 na bp0 nb).
qed.

lemma polyfixveclk_sqnorm2_uint_total
    (ap0 : BArray8192.t) (na : int) (bp0 : BArray8192.t) (nb : int) :
  phoare [Signer._polyfixveclk_sqnorm2_2048 :
    ap = ap0 /\ acount = W64.of_int na /\ bp = bp0 /\ bcount = W64.of_int nb /\
    0 <= na <= 2048 /\ 0 <= nb <= 2048
    ==>
    W64.to_uint res = hyperball_sqnorm ap0 na bp0 nb %% W64.modulus] = 1%r.
proof.
conseq polyfixveclk_sqnorm2_ll (polyfixveclk_sqnorm2_correct ap0 na bp0 nb) => //.
move=> &hr hpre result.
have hcast := W64.of_uintK (hyperball_sqnorm ap0 na bp0 nb).
split.
+ by move=> [_ hr]; split.
+ move=> [_ ->]; by split.
qed.

lemma polyfixveclk_sqnorm2_integer_total
    (ap0 : BArray8192.t) (na : int) (bp0 : BArray8192.t) (nb : int) :
  hyperball_sqnorm ap0 na bp0 nb < W64.modulus =>
  phoare [Signer._polyfixveclk_sqnorm2_2048 :
    ap = ap0 /\ acount = W64.of_int na /\ bp = bp0 /\ bcount = W64.of_int nb /\
    0 <= na <= 2048 /\ 0 <= nb <= 2048
    ==>
    W64.to_uint res = hyperball_sqnorm ap0 na bp0 nb] = 1%r.
proof.
move=> hfit.
conseq polyfixveclk_sqnorm2_ll (polyfixveclk_sqnorm2_correct ap0 na bp0 nb) => //.
move=> &hr hpre result.
have hna : 0 <= na by smt().
have hnb : 0 <= nb by smt().
have hnonneg := hyperball_sqnorm_nonnegative ap0 na bp0 nb hna hnb.
have hbound : 0 <= hyperball_sqnorm ap0 na bp0 nb < W64.modulus by split.
have hcast := W64.to_uint_small (hyperball_sqnorm ap0 na bp0 nb) hbound.
split.
+ by move=> [_ hr]; split.
+ move=> [_ ->]; by split.
qed.

lemma polyfixveclk_sqnorm2_compare_total
    (ap0 : BArray8192.t) (na : int) (bp0 : BArray8192.t) (nb : int) (bound : W64.t) :
  phoare [Signer._polyfixveclk_sqnorm2_2048 :
    ap = ap0 /\ acount = W64.of_int na /\ bp = bp0 /\ bcount = W64.of_int nb /\
    0 <= na <= 2048 /\ 0 <= nb <= 2048
    ==>
    (res \ule bound) =
      (hyperball_sqnorm ap0 na bp0 nb %% W64.modulus <= W64.to_uint bound)] = 1%r.
proof.
conseq polyfixveclk_sqnorm2_ll (polyfixveclk_sqnorm2_correct ap0 na bp0 nb) => //.
move=> &hr hpre result.
have hcmp := hyperball_norm_word_le ap0 na bp0 nb bound.
split.
+ by move=> [_ hr]; split.
+ move=> [_ ->]; by split.
qed.

lemma polyfixveclk_sqnorm2_compare_exact_total
    (ap0 : BArray8192.t) (na : int) (bp0 : BArray8192.t) (nb : int) (bound : W64.t) :
  hyperball_sqnorm ap0 na bp0 nb < W64.modulus =>
  phoare [Signer._polyfixveclk_sqnorm2_2048 :
    ap = ap0 /\ acount = W64.of_int na /\ bp = bp0 /\ bcount = W64.of_int nb /\
    0 <= na <= 2048 /\ 0 <= nb <= 2048
    ==>
    (res \ule bound) = (hyperball_sqnorm ap0 na bp0 nb <= W64.to_uint bound)] = 1%r.
proof.
move=> hfit.
conseq polyfixveclk_sqnorm2_ll (polyfixveclk_sqnorm2_correct ap0 na bp0 nb) => //.
move=> &hr hpre result.
have hna : 0 <= na by smt().
have hnb : 0 <= nb by smt().
have hcmp := hyperball_norm_word_le_exact ap0 na bp0 nb bound hna hnb hfit.
split.
+ by move=> [_ hr]; split.
+ move=> [_ ->]; by split.
qed.

(* This sufficient bound is conditional: proving it for the output of the
   scaling procedure is a separate obligation. *)
lemma polyfixveclk_sqnorm2_26bit_total
    (ap0 : BArray8192.t) (na : int) (bp0 : BArray8192.t) (nb : int) :
  0 <= na => 0 <= nb => na + nb <= 2816 =>
  hyperball_coeff_bound ap0 na 67108864 => hyperball_coeff_bound bp0 nb 67108864 =>
  phoare [Signer._polyfixveclk_sqnorm2_2048 :
    ap = ap0 /\ acount = W64.of_int na /\ bp = bp0 /\ bcount = W64.of_int nb /\
    0 <= na <= 2048 /\ 0 <= nb <= 2048
    ==>
    W64.to_uint res = hyperball_sqnorm ap0 na bp0 nb] = 1%r.
proof.
move=> ha hb hn hca hcb.
have [_ hfit] := hyperball_sqnorm_26bit_no_overflow ap0 na bp0 nb ha hb hn hca hcb.
exact (polyfixveclk_sqnorm2_integer_total ap0 na bp0 nb hfit).
qed.

end HyperballNormCorrectness.
