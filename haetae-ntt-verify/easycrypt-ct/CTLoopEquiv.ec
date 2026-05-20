require import AllCore IntDiv Ring StdOrder BitEncoding.

from Jasmin require import JModel_x86.
import SLH64.

require import Hpoly_extract Hpoly_loop.

import IntOrder.

theory CTLoopEquiv.

lemma int_shr1_div2 x :
  0 <= x =>
  x `|>>` 1 = x %/ 2.
proof.
move=> _.
by rewrite /(`|>>`) /(`<<`) /=.
qed.

lemma int_shl1_mul2 x :
  x `<<` 1 = x * 2.
proof. by rewrite /(`<<`) /=. qed.

lemma int_shl2_mul4 x :
  x `<<` 2 = x * 4.
proof. by rewrite /(`<<`) /=. qed.

lemma int_shl3_mul8 x :
  x `<<` 3 = x * 8.
proof. by rewrite /(`<<`) /=. qed.

lemma int_shl4_mul16 x :
  x `<<` 4 = x * 16.
proof. by rewrite /(`<<`) /=. qed.

lemma int_shl5_mul32 x :
  x `<<` 5 = x * 32.
proof. by rewrite /(`<<`) /=. qed.

lemma int_shl6_mul64 x :
  x `<<` 6 = x * 64.
proof. by rewrite /(`<<`) /=. qed.

lemma int_shl7_mul128 x :
  x `<<` 7 = x * 128.
proof. by rewrite /(`<<`) /=. qed.

lemma int_shl8_mul256 x :
  x `<<` 8 = x * 256.
proof. by rewrite /(`<<`) /=. qed.

equiv fqmul_ct_loop :
  Hpoly_extract.M.__fqmul ~ Hpoly_loop.M.__fqmul :
  ={a, b} ==> ={res}.
proof.
proc.
inline {2} Hpoly_loop.M.__fqmul.
inline {2} Hpoly_extract.M.__fqmul.
sim.
qed.

equiv poly_ntt_ct_loop :
  Hpoly_extract.M._poly_ntt ~ Hpoly_loop.M._poly_ntt :
  ={rp} ==> ={res}.
proof.
proc.
unroll {2} 5.
seq 1 5 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas /\
   zetasctr{2} = 1 /\ len{2} = 64).
+ inline {1} Hpoly_extract.M._poly_ntt_stage_128.
  rcondt{2} 5; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas /\
    zetasctr{2} = 0 + block{1} /\
    start{2} = 256 * block{1} /\
    len{2} = 128 /\
    0 <= block{1} <= 1
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 256 * block{1} /\
      len{2} = 128 /\
      cmp{2} = start{2} + 128 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 128
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl8_mul256).
  wp.
  skip => />; smt(int_shr1_div2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas /\
   zetasctr{2} = 3 /\ len{2} = 32).
+ inline {1} Hpoly_extract.M._poly_ntt_stage_64.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas /\
    zetasctr{2} = 1 + block{1} /\
    start{2} = 128 * block{1} /\
    len{2} = 64 /\
    0 <= block{1} <= 2
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 128 * block{1} /\
      len{2} = 64 /\
      cmp{2} = start{2} + 64 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 64
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl7_mul128).
  wp.
  skip => />; smt(int_shr1_div2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas /\
   zetasctr{2} = 7 /\ len{2} = 16).
+ inline {1} Hpoly_extract.M._poly_ntt_stage_32.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas /\
    zetasctr{2} = 3 + block{1} /\
    start{2} = 64 * block{1} /\
    len{2} = 32 /\
    0 <= block{1} <= 4
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 64 * block{1} /\
      len{2} = 32 /\
      cmp{2} = start{2} + 32 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 32
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl6_mul64).
  wp.
  skip => />; smt(int_shr1_div2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas /\
   zetasctr{2} = 15 /\ len{2} = 8).
+ inline {1} Hpoly_extract.M._poly_ntt_stage_16.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas /\
    zetasctr{2} = 7 + block{1} /\
    start{2} = 32 * block{1} /\
    len{2} = 16 /\
    0 <= block{1} <= 8
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 32 * block{1} /\
      len{2} = 16 /\
      cmp{2} = start{2} + 16 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 16
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl5_mul32).
  wp.
  skip => />; smt(int_shr1_div2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas /\
   zetasctr{2} = 31 /\ len{2} = 4).
+ inline {1} Hpoly_extract.M._poly_ntt_stage_8.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas /\
    zetasctr{2} = 15 + block{1} /\
    start{2} = 16 * block{1} /\
    len{2} = 8 /\
    0 <= block{1} <= 16
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 16 * block{1} /\
      len{2} = 8 /\
      cmp{2} = start{2} + 8 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 8
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl4_mul16).
  wp.
  skip => />; smt(int_shr1_div2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas /\
   zetasctr{2} = 63 /\ len{2} = 2).
+ inline {1} Hpoly_extract.M._poly_ntt_stage_4.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas /\
    zetasctr{2} = 31 + block{1} /\
    start{2} = 8 * block{1} /\
    len{2} = 4 /\
    0 <= block{1} <= 32
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 8 * block{1} /\
      len{2} = 4 /\
      cmp{2} = start{2} + 4 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 4
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl3_mul8).
  wp.
  skip => />; smt(int_shr1_div2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas /\
   zetasctr{2} = 127 /\ len{2} = 1).
+ inline {1} Hpoly_extract.M._poly_ntt_stage_2.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas /\
    zetasctr{2} = 63 + block{1} /\
    start{2} = 4 * block{1} /\
    len{2} = 2 /\
    0 <= block{1} <= 64
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 4 * block{1} /\
      len{2} = 2 /\
      cmp{2} = start{2} + 2 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 2
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl2_mul4).
  wp.
  skip => />; smt(int_shr1_div2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas /\
   zetasctr{2} = 255 /\ len{2} = 0).
+ inline {1} Hpoly_extract.M._poly_ntt_stage_1.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas /\
    zetasctr{2} = 127 + block{1} /\
    start{2} = 2 * block{1} /\
    len{2} = 1 /\
    0 <= block{1} <= 128
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 2 * block{1} /\
      len{2} = 1 /\
      cmp{2} = start{2} + 1 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 1
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl1_mul2).
  wp.
  skip => />; smt(int_shr1_div2).
rcondf{2} 1; first by auto.
by wp; skip.
qed.

equiv poly_invntt_ct_loop :
  Hpoly_extract.M._poly_invntt ~ Hpoly_loop.M._poly_invntt :
  ={rp} ==> ={res}.
proof.
proc.
unroll {2} 5.
seq 1 5 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas_inv /\
   zetasctr{2} = 128 /\ len{2} = 2).
+ inline {1} Hpoly_extract.M._poly_invntt_stage_1.
  rcondt{2} 5; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas_inv /\
    zetasctr{2} = 0 + block{1} /\
    start{2} = 2 * block{1} /\
    len{2} = 1 /\
    0 <= block{1} <= 128
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 2 * block{1} /\
      len{2} = 1 /\
      cmp{2} = start{2} + 1 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 1
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl1_mul2).
  wp.
  skip => />; smt(int_shl1_mul2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas_inv /\
   zetasctr{2} = 192 /\ len{2} = 4).
+ inline {1} Hpoly_extract.M._poly_invntt_stage_2.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas_inv /\
    zetasctr{2} = 128 + block{1} /\
    start{2} = 4 * block{1} /\
    len{2} = 2 /\
    0 <= block{1} <= 64
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 4 * block{1} /\
      len{2} = 2 /\
      cmp{2} = start{2} + 2 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 2
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl2_mul4).
  wp.
  skip => />; smt(int_shl1_mul2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas_inv /\
   zetasctr{2} = 224 /\ len{2} = 8).
+ inline {1} Hpoly_extract.M._poly_invntt_stage_4.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas_inv /\
    zetasctr{2} = 192 + block{1} /\
    start{2} = 8 * block{1} /\
    len{2} = 4 /\
    0 <= block{1} <= 32
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 8 * block{1} /\
      len{2} = 4 /\
      cmp{2} = start{2} + 4 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 4
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl3_mul8).
  wp.
  skip => />; smt(int_shl1_mul2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas_inv /\
   zetasctr{2} = 240 /\ len{2} = 16).
+ inline {1} Hpoly_extract.M._poly_invntt_stage_8.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas_inv /\
    zetasctr{2} = 224 + block{1} /\
    start{2} = 16 * block{1} /\
    len{2} = 8 /\
    0 <= block{1} <= 16
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 16 * block{1} /\
      len{2} = 8 /\
      cmp{2} = start{2} + 8 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 8
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl4_mul16).
  wp.
  skip => />; smt(int_shl1_mul2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas_inv /\
   zetasctr{2} = 248 /\ len{2} = 32).
+ inline {1} Hpoly_extract.M._poly_invntt_stage_16.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas_inv /\
    zetasctr{2} = 240 + block{1} /\
    start{2} = 32 * block{1} /\
    len{2} = 16 /\
    0 <= block{1} <= 8
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 32 * block{1} /\
      len{2} = 16 /\
      cmp{2} = start{2} + 16 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 16
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl5_mul32).
  wp.
  skip => />; smt(int_shl1_mul2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas_inv /\
   zetasctr{2} = 252 /\ len{2} = 64).
+ inline {1} Hpoly_extract.M._poly_invntt_stage_32.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas_inv /\
    zetasctr{2} = 248 + block{1} /\
    start{2} = 64 * block{1} /\
    len{2} = 32 /\
    0 <= block{1} <= 4
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 64 * block{1} /\
      len{2} = 32 /\
      cmp{2} = start{2} + 32 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 32
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl6_mul64).
  wp.
  skip => />; smt(int_shl1_mul2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas_inv /\
   zetasctr{2} = 254 /\ len{2} = 128).
+ inline {1} Hpoly_extract.M._poly_invntt_stage_64.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas_inv /\
    zetasctr{2} = 252 + block{1} /\
    start{2} = 128 * block{1} /\
    len{2} = 64 /\
    0 <= block{1} <= 2
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 128 * block{1} /\
      len{2} = 64 /\
      cmp{2} = start{2} + 64 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 64
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl7_mul128).
  wp.
  skip => />; smt(int_shl1_mul2).
unroll {2} 1.
seq 1 1 :
  (={rp} /\ zetasp{2} = Hpoly_loop.jzetas_inv /\
   zetasctr{2} = 255 /\ len{2} = 256).
+ inline {1} Hpoly_extract.M._poly_invntt_stage_128.
  rcondt{2} 1; first by auto.
  wp.
  while (
    rp0{1} = rp{2} /\ ={zetasp} /\
    zetasp{2} = Hpoly_loop.jzetas_inv /\
    zetasctr{2} = 254 + block{1} /\
    start{2} = 256 * block{1} /\
    len{2} = 128 /\
    0 <= block{1} <= 1
  ).
  + wp.
    while (
      rp0{1} = rp{2} /\
      zeta_0{1} = zeta_0{2} /\
      start{1} = start{2} /\
      start{2} = 256 * block{1} /\
      len{2} = 128 /\
      cmp{2} = start{2} + 128 /\
      j{2} = start{2} + j{1} /\
      0 <= j{1} <= 128
    ).
    + wp.
      call fqmul_ct_loop.
      wp.
      skip => /#.
    wp.
    skip => />; smt(int_shl8_mul256).
  wp.
  skip => />; smt(int_shl1_mul2).
rcondf{2} 1; first by auto.
inline {1} Hpoly_extract.M._poly_invntt_scale.
wp.
while (
  rp0{1} = rp{2} /\
  ={zeta_0} /\
  j{1} = j{2} /\
  0 <= j{1} <= 256
).
+ wp.
  call fqmul_ct_loop.
  wp.
  skip => /#.
wp.
skip => /#.
qed.

equiv poly_ntt_jazz_ct_loop :
  Hpoly_extract.M.poly_ntt_jazz ~ Hpoly_loop.M.poly_ntt_jazz :
  ={rp} ==> ={res}.
proof.
proc.
wp.
call poly_ntt_ct_loop.
by wp.
qed.

equiv poly_invntt_jazz_ct_loop :
  Hpoly_extract.M.poly_invntt_jazz ~ Hpoly_loop.M.poly_invntt_jazz :
  ={rp} ==> ={res}.
proof.
proc.
wp.
call poly_invntt_ct_loop.
by wp.
qed.

end CTLoopEquiv.
