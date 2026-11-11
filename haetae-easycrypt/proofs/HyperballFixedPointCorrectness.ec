require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import ApiTarget HyperballFixedPointSpec SigmaSpec GaussianTraceSpec GaussianAccumulatorCorrectness.

module HB = ApiTarget.M(ApiTarget.Syscall).

lemma hb_store_pack p x : hb_store p x = hb_pack x.
proof.
  apply BArray16.ext_eq64 => i hi.
  rewrite /hb_store /hb_pack /hb_store !BArray16.get_set64E //=.
  smt().
qed.

lemma hb_load_pack x : hb_load (hb_pack x) = x.
proof. by case: x => a b; rewrite /hb_load /hb_pack /hb_store /=. qed.

lemma hb_mul48_correct a0 b0 :
  hoare [HB.__mul48 : a = a0 /\ b = b0 ==> res = mul48_word a0 b0].
proof. proc; wp; skip; auto => />; rewrite /mul48_word /=. qed.

lemma hb_norm_correct a b :
  hoare [HB.__renormalize48 : x0 = a /\ x1 = b ==> res = hb_norm (a,b)].
proof. proc; wp; skip; auto => />; rewrite /hb_norm /=. qed.

lemma hb_cneg_correct a b s :
  hoare [HB.__copy_cneg_regs : x0 = a /\ x1 = b /\ sign = s ==> res = hb_cneg (a,b) s].
proof.
  proc; ecall (hb_norm_correct y0 y1); wp; skip; auto => />; rewrite /hb_cneg /=.
qed.

lemma hb_sub_correct a b c d :
  hoare [HB.__sub_regs : x0=a /\ x1=b /\ y0=c /\ y1=d ==> res=hb_sub (a,b) (c,d)].
proof.
  proc; wp; ecall (hb_cneg_correct y0 y1 W64.one); wp; skip; auto => />; rewrite /hb_sub /=.
qed.

lemma hb_threehalves_correct a b :
  hoare [HB.__sub_from_threehalves_regs : x0=a /\ x1=b ==> res=hb_threehalves_minus (a,b)].
proof.
  proc; ecall (hb_norm_correct x0 x1); wp; ecall (hb_cneg_correct x0 x1 W64.one).
  wp; skip; auto => />; rewrite /hb_threehalves_minus /=.
qed.

lemma hb_mul_regs_correct a b c d :
  hoare [HB.__fixpoint_mul_regs : x0=a /\ x1=b /\ y0=c /\ y1=d ==> res=hb_mul (a,b) (c,d)].
proof.
  proc; wp; ecall (hb_mul48_correct x1 y0).
  wp; ecall (hb_mul48_correct x0 y1).
  wp; ecall (hb_mul48_correct x0 y0).
  wp; skip; auto => />; rewrite /hb_mul /hb_norm /=.
qed.

lemma hb_square_regs_correct a b :
  hoare [HB.__fixpoint_square_regs : x0=a /\ x1=b ==> res=hb_square (a,b)].
proof.
  proc; wp; ecall (hb_mul48_correct x0 x1).
  wp; ecall (hb_mul48_correct x0 x0).
  wp; skip; auto => />; rewrite /hb_square /square_word /=.
qed.

lemma hb_signed_mul_regs_correct a b c d :
  hoare [HB.__fixpoint_unsigned_signed_mul_regs : xy0=a /\ xy1=b /\ y0=c /\ y1=d
    ==> res=hb_signed_mul (a,b) (c,d)].
proof.
  proc; ecall (hb_cneg_correct z0 z1 sign).
  wp; ecall (hb_mul_regs_correct x0 x1 xy0 xy1).
  wp; ecall (hb_cneg_correct y0 y1 sign).
  wp; skip; auto => />; rewrite /hb_signed_mul /=.
qed.

lemma hb_mul_rnd13_regs_correct xx a b ss :
  hoare [HB.__fixpoint_mul_rnd13_regs : x=xx /\ y0=a /\ y1=b /\ sign=ss
    ==> res=hb_mul_rnd13 xx (a,b) ss].
proof.
  proc; wp; ecall (hb_mul_regs_correct x0 x1 y0 y1).
  wp; skip; auto => />; rewrite /hb_mul_rnd13 /=.
qed.

lemma hb_mul_high_regs_correct a b yy :
  hoare [HB.__fixpoint_mul_high_regs : x0=a /\ x1=b /\ y=yy ==> res=hb_mul_high (a,b) yy].
proof.
  proc; ecall (hb_norm_correct r0 r1); wp; ecall (hb_mul48_correct x1 y).
  wp; ecall (hb_mul48_correct x0 y).
  wp; skip; auto => />; rewrite /hb_mul_high /=.
qed.

lemma hb_mul_rnd13_correct xx yp0 ss :
  hoare [HB._fixpoint_mul_rnd13 : x=xx /\ yp=yp0 /\ sign=ss
    ==> res=hb_scale_sample xx yp0 ss].
proof.
  proc; ecall (hb_mul_rnd13_regs_correct x y0 y1 s).
  wp; skip; auto => />; rewrite /hb_scale_sample /hb_load.
qed.

lemma hb_square_correct xp0 :
  hoare [HB._fixpoint_square : xp=xp0 ==> res=hb_pack (hb_square (hb_load xp0))].
proof.
  proc; wp; ecall (hb_square_regs_correct x0 x1).
  wp; skip; auto => /> &m.
  exact (hb_store_pack rp{m} (hb_square (hb_load xp0))).
qed.

lemma hb_mul_high_correct xp0 yy :
  hoare [HB._fixpoint_mul_high : xp=xp0 /\ y=yy ==> res=hb_pack (hb_mul_high (hb_load xp0) yy)].
proof.
  proc; wp; ecall (hb_mul_high_regs_correct x0 x1 y).
  wp; skip; auto => /> &m.
  exact (hb_store_pack rp{m} (hb_mul_high (hb_load xp0) yy)).
qed.

lemma hb_half_round_correct xp0 :
  hoare [HB._fixpoint_half_round : xp=xp0 ==> res=hb_pack (hb_half_round (hb_load xp0))].
proof.
  proc; wp; ecall (hb_norm_correct x0 x1).
  wp; skip; auto => />.
  rewrite /hb_half_round /hb_load /=.
  apply hb_store_pack.
qed.

lemma hb_mul48_ll : islossless HB.__mul48.
proof. proc; auto. qed.
lemma hb_norm_ll : islossless HB.__renormalize48.
proof. proc; auto. qed.
lemma hb_cneg_ll : islossless HB.__copy_cneg_regs.
proof. proc; call hb_norm_ll; auto. qed.
lemma hb_sub_ll : islossless HB.__sub_regs.
proof. proc; wp; call hb_cneg_ll; auto. qed.
lemma hb_threehalves_ll : islossless HB.__sub_from_threehalves_regs.
proof. proc; call hb_norm_ll; wp; call hb_cneg_ll; auto. qed.
lemma hb_mul_regs_ll : islossless HB.__fixpoint_mul_regs.
proof. proc; do 3!(wp; call hb_mul48_ll); auto. qed.
lemma hb_square_regs_ll : islossless HB.__fixpoint_square_regs.
proof. proc; do 2!(wp; call hb_mul48_ll); auto. qed.
lemma hb_signed_mul_regs_ll : islossless HB.__fixpoint_unsigned_signed_mul_regs.
proof. proc; call hb_cneg_ll; call hb_mul_regs_ll; call hb_cneg_ll; auto. qed.
lemma hb_mul_rnd13_regs_ll : islossless HB.__fixpoint_mul_rnd13_regs.
proof. proc; wp; call hb_mul_regs_ll; auto. qed.
lemma hb_mul_high_regs_ll : islossless HB.__fixpoint_mul_high_regs.
proof. proc; call hb_norm_ll; do 2!(wp; call hb_mul48_ll); auto. qed.
lemma hb_mul_rnd13_ll : islossless HB._fixpoint_mul_rnd13.
proof. proc; call hb_mul_rnd13_regs_ll; auto. qed.
lemma hb_square_ll : islossless HB._fixpoint_square.
proof. proc; wp; call hb_square_regs_ll; auto. qed.
lemma hb_mul_high_ll : islossless HB._fixpoint_mul_high.
proof. proc; wp; call hb_mul_high_regs_ll; auto. qed.
lemma hb_half_round_ll : islossless HB._fixpoint_half_round.
proof. proc; wp; call hb_norm_ll; auto. qed.

lemma hb_mul_rnd13_total xx yp0 ss :
  phoare [HB._fixpoint_mul_rnd13 : x=xx /\ yp=yp0 /\ sign=ss
    ==> res=hb_scale_sample xx yp0 ss] = 1%r.
proof. by conseq hb_mul_rnd13_ll (hb_mul_rnd13_correct xx yp0 ss). qed.
lemma hb_mul_high_total xp0 yy :
  phoare [HB._fixpoint_mul_high : xp=xp0 /\ y=yy
    ==> res=hb_pack (hb_mul_high (hb_load xp0) yy)] = 1%r.
proof. by conseq hb_mul_high_ll (hb_mul_high_correct xp0 yy). qed.
lemma hb_half_round_total xp0 :
  phoare [HB._fixpoint_half_round : xp=xp0
    ==> res=hb_pack (hb_half_round (hb_load xp0))] = 1%r.
proof. by conseq hb_half_round_ll (hb_half_round_correct xp0). qed.

lemma hb_newton_iter0 half start : hb_newton_iter half start 0 = start.
proof. by rewrite /hb_newton_iter iota0 //=. qed.

lemma hb_newton_iterS half start k : 0 <= k =>
  hb_newton_iter half start (k+1) = hb_newton_step half (hb_newton_iter half start k).
proof. by move=> hk; rewrite /hb_newton_iter iotaSr 1:hk -cats1 foldl_cat /=. qed.

lemma hb_counter6 (i : W64.t) : W64.to_uint i < 6 =>
  W64.to_uint (i + W64.one) = W64.to_uint i + 1.
proof.
  move=> hi; rewrite W64.to_uintD W64.to_uint1 modz_small //.
  have /= := W64.to_uint_cmp i; smt().
qed.

lemma hb_newton_correct xp0 cube0 three0 :
  hoare [HB._fixpoint_newton_invsqrt :
    xhalfp=xp0 /\ start_cubep=cube0 /\ start_threep=three0 ==>
    res=hb_pack (hb_newton (hb_load xp0) (hb_load cube0) (hb_load three0))].
proof.
  proc; wp.
  conseq (_ : _ ==> (inv0,inv1)=hb_newton (hb_load xp0) (hb_load cube0) (hb_load three0)).
  + move=> &m _ a b he; rewrite -he.
    exact (hb_store_pack rp{m} (a,b)).
  while ((x0,x1)=hb_load xp0 /\ 0 <= W64.to_uint i <= 6 /\
    (inv0,inv1)=hb_newton_iter (hb_load xp0)
      (hb_newton_initial (hb_load xp0) (hb_load cube0) (hb_load three0)) (W64.to_uint i)).
  + wp; ecall (hb_signed_mul_regs_correct inv0 inv1 tmp20 tmp21).
    wp; ecall (hb_threehalves_correct tmp20 tmp21).
    wp; ecall (hb_mul_regs_correct x0 x1 tmp0 tmp1).
    wp; ecall (hb_square_regs_correct inv0 inv1).
    wp; skip; auto => />.
    move=> &m hlo hhi hinv hguard.
    have hg : W64.to_uint i{m} < 6 by move: hguard; rewrite W64.ultE /=.
    rewrite hb_counter6 1:hg hb_newton_iterS 1:hlo /hb_newton_step.
    smt().
  wp; ecall (hb_sub_correct st0 st1 tmp0 tmp1).
  wp; ecall (hb_mul_regs_correct x0 x1 sc0 sc1).
  wp; skip; auto => />.
  rewrite hb_newton_iter0 /hb_newton_initial /hb_load /hb_newton /hb_newton_initial /= -!pairS /=.
  move=> i a b; rewrite W64.ultE /=; move=> hguard hlo hhi hinv.
  have hi6 : W64.to_uint i = 6 by smt().
  by move: hinv; rewrite hi6.
qed.

lemma hb_newton_ll : islossless HB._fixpoint_newton_invsqrt.
proof.
  proc; wp; while (true) (6 - W64.to_uint i).
  + move=> z; wp; call hb_signed_mul_regs_ll; wp; call hb_threehalves_ll.
    wp; call hb_mul_regs_ll; wp; call hb_square_regs_ll; wp; skip; auto => />.
    move=> &m; rewrite W64.ultE /=; move=> hi.
    rewrite hb_counter6 1:hi; smt().
  wp; call hb_sub_ll; wp; call hb_mul_regs_ll; wp; skip; auto => />.
  move=> i; rewrite W64.ultE /=; smt().
qed.

lemma hb_newton_total xp0 cube0 three0 :
  phoare [HB._fixpoint_newton_invsqrt :
    xhalfp=xp0 /\ start_cubep=cube0 /\ start_threep=three0 ==>
    res=hb_pack (hb_newton (hb_load xp0) (hb_load cube0) (hb_load three0))] = 1%r.
proof. by conseq hb_newton_ll (hb_newton_correct xp0 cube0 three0). qed.

lemma hb_norm_value_mod x :
  hb_value (hb_norm x) = hb_value x %% 5192296858534827628530496329220096.
proof.
  have h := gauss_normalize_value_mod x.`1 x.`2.
  by move: h; rewrite /gauss_normalize /gauss_limb_value /hb_value /hb_norm /=.
qed.

lemma hb_norm_value_exact (x : hb_fp) :
  W64.to_uint x.`2 + W64.to_uint x.`1 %/ 281474976710656 < 18446744073709551616 =>
  hb_value (hb_norm x) = hb_value x.
proof.
  move=> hroom.
  have h := gauss_normalize_value_exact x.`1 x.`2 hroom.
  by move: h; rewrite /gauss_normalize /gauss_limb_value /hb_value /hb_norm /=.
qed.

lemma hb_norm_low_bound x : 0 <= W64.to_uint (hb_norm x).`1 < 281474976710656.
proof.
  rewrite /hb_norm /=.
  have -> : 281474976710655 = 2^48 - 1 by trivial.
  rewrite W64.to_uint_and_mod //=; apply modz_cmp; trivial.
qed.

lemma hb_half_integer_split a b :
  (a + 281474976710656*b + 1) %/ 2 = (a+1) %/ 2 + 140737488355328*b.
proof.
  have -> : a + 281474976710656*b + 1 = (140737488355328*b)*2 + (a+1) by ring.
  rewrite divzMDl //; ring.
qed.

lemma hb_half_round_integer (x : hb_fp) : W64.to_uint x.`1 < 281474976710656 =>
  hb_value (hb_half_round x) = (hb_value x + 1) %/ 2.
proof.
  case: x => a b /= ha.
  have /= hau := W64.to_uint_cmp a.
  have /= hbu := W64.to_uint_cmp b.
  have hda := divz_eq (W64.to_uint a + 1) 2.
  have /= hra := modz_cmp (W64.to_uint a + 1) 2.
  have hdb := divz_eq (W64.to_uint b) 2.
  have /= hrb := modz_cmp (W64.to_uint b) 2.
  have hinc : W64.to_uint (a+W64.one) = W64.to_uint a+1.
  + rewrite W64.to_uintD W64.to_uint1 modz_small; smt().
  have hlo : W64.to_uint ((a+W64.one) `>>>` 1) = (W64.to_uint a+1) %/ 2.
  + by rewrite W64.to_uint_shr //= hinc.
  have hbit : W64.to_uint (b `&` W64.one) = W64.to_uint b %% 2.
  + have h := W64.to_uint_and_mod 1 b _; first trivial.
    by move: h; rewrite /=.
  have hcarry : W64.to_uint ((b `&` W64.one) `<<<` 47) =
      (W64.to_uint b %% 2)*140737488355328.
  + rewrite W64.to_uint_shl //= hbit modz_small; smt().
  pose lo := ((a+W64.one) `>>>` 1) + ((b `&` W64.one) `<<<` 47).
  pose hi := b `>>>` 1.
  have hlor : W64.to_uint lo = (W64.to_uint a+1) %/ 2 +
      (W64.to_uint b %% 2)*140737488355328.
  + rewrite /lo W64.to_uintD hlo hcarry modz_small; smt().
  have hhir : W64.to_uint hi = W64.to_uint b %/ 2 by rewrite /hi W64.to_uint_shr.
  have hlowrange : 0 <= W64.to_uint lo <= 281474976710656 by smt().
  have hdl := divz_eq (W64.to_uint lo) 281474976710656.
  have /= hrl := modz_cmp (W64.to_uint lo) 281474976710656.
  have hroom : W64.to_uint hi + W64.to_uint lo %/ 281474976710656 < 18446744073709551616
    by smt().
  rewrite /hb_half_round /= -/lo -/hi (hb_norm_value_exact (lo,hi) hroom).
  rewrite /hb_value /= hlor hhir hb_half_integer_split; smt().
qed.

lemma hb_half_round_integer_correct xp0 :
  hoare [HB._fixpoint_half_round : xp=xp0 /\
    W64.to_uint (hb_load xp0).`1 < 281474976710656 ==>
    hb_value (hb_load res) = (hb_value (hb_load xp0)+1) %/ 2].
proof.
  conseq (hb_half_round_correct xp0) => />.
  smt(hb_load_pack hb_half_round_integer).
qed.

lemma hb_half_round_integer_total xp0 :
  phoare [HB._fixpoint_half_round : xp=xp0 /\
    W64.to_uint (hb_load xp0).`1 < 281474976710656 ==>
    hb_value (hb_load res) = (hb_value (hb_load xp0)+1) %/ 2] = 1%r.
proof. by conseq hb_half_round_ll (hb_half_round_integer_correct xp0). qed.

lemma hb_truncate_of_int n : truncateu32 (W64.of_int n) = W32.of_int n.
proof.
  apply W32.to_uint_eq.
  rewrite /W2u32.truncateu32 !W32.of_uintK W64.of_uintK /=.
  apply modz_dvd; trivial.
qed.

lemma hb_signed_truncate_fit (r sign : W64.t) :
  sign = W64.zero \/ sign = W64.one => W64.to_uint r <= 2147483647 =>
  W32.to_sint (truncateu32 ((r `^` (W64.zero - sign)) + sign)) =
    if sign = W64.zero then W64.to_uint r else - W64.to_uint r.
proof.
  move=> hs hfit.
  have /= hr := W64.to_uint_cmp r.
  case: hs => ->.
  + rewrite W64.WRingA.oppr0 W64.xorw0_s W64.WRingA.addr0 /= /W2u32.truncateu32.
    apply W32.to_sintK_small; smt().
  have hnz : W64.one <> W64.zero by rewrite W64.to_uint_eq W64.to_uint1 W64.to_uint0.
  rewrite W64.minus_one W64.xorw1 -W64.twos_compl hnz /=.
  rewrite -{1}(W64.to_uintK r) -W64.of_intN hb_truncate_of_int.
  apply W32.to_sintK_small; smt().
qed.

lemma hb_mul_rnd13_signed_fit sample scale sign :
  sign = W64.zero \/ sign = W64.one => hb_rnd13_magnitude sample scale <= 2147483647 =>
  W32.to_sint (hb_mul_rnd13 sample scale sign) =
    if sign = W64.zero then hb_rnd13_magnitude sample scale else -hb_rnd13_magnitude sample scale.
proof.
  rewrite /hb_mul_rnd13 /hb_rnd13_magnitude /=.
  exact: hb_signed_truncate_fit.
qed.

lemma hb_norm_total a b :
  phoare [HB.__renormalize48 : x0=a /\ x1=b ==> res=hb_norm (a,b)] = 1%r.
proof. by conseq hb_norm_ll (hb_norm_correct a b). qed.
lemma hb_cneg_total a b s :
  phoare [HB.__copy_cneg_regs : x0=a /\ x1=b /\ sign=s ==> res=hb_cneg (a,b) s] = 1%r.
proof. by conseq hb_cneg_ll (hb_cneg_correct a b s). qed.
lemma hb_sub_total a b c d :
  phoare [HB.__sub_regs : x0=a /\ x1=b /\ y0=c /\ y1=d ==> res=hb_sub (a,b) (c,d)] = 1%r.
proof. by conseq hb_sub_ll (hb_sub_correct a b c d). qed.
lemma hb_threehalves_total a b :
  phoare [HB.__sub_from_threehalves_regs : x0=a /\ x1=b ==> res=hb_threehalves_minus (a,b)] = 1%r.
proof. by conseq hb_threehalves_ll (hb_threehalves_correct a b). qed.
lemma hb_mul_regs_total a b c d :
  phoare [HB.__fixpoint_mul_regs : x0=a /\ x1=b /\ y0=c /\ y1=d ==> res=hb_mul (a,b) (c,d)] = 1%r.
proof. by conseq hb_mul_regs_ll (hb_mul_regs_correct a b c d). qed.
lemma hb_square_regs_total a b :
  phoare [HB.__fixpoint_square_regs : x0=a /\ x1=b ==> res=hb_square (a,b)] = 1%r.
proof. by conseq hb_square_regs_ll (hb_square_regs_correct a b). qed.
lemma hb_signed_mul_regs_total a b c d :
  phoare [HB.__fixpoint_unsigned_signed_mul_regs : xy0=a /\ xy1=b /\ y0=c /\ y1=d
    ==> res=hb_signed_mul (a,b) (c,d)] = 1%r.
proof. by conseq hb_signed_mul_regs_ll (hb_signed_mul_regs_correct a b c d). qed.
lemma hb_mul_rnd13_regs_total xx a b ss :
  phoare [HB.__fixpoint_mul_rnd13_regs : x=xx /\ y0=a /\ y1=b /\ sign=ss
    ==> res=hb_mul_rnd13 xx (a,b) ss] = 1%r.
proof. by conseq hb_mul_rnd13_regs_ll (hb_mul_rnd13_regs_correct xx a b ss). qed.
lemma hb_mul_high_regs_total a b yy :
  phoare [HB.__fixpoint_mul_high_regs : x0=a /\ x1=b /\ y=yy ==> res=hb_mul_high (a,b) yy] = 1%r.
proof. by conseq hb_mul_high_regs_ll (hb_mul_high_regs_correct a b yy). qed.
lemma hb_square_total xp0 :
  phoare [HB._fixpoint_square : xp=xp0 ==> res=hb_pack (hb_square (hb_load xp0))] = 1%r.
proof. by conseq hb_square_ll (hb_square_correct xp0). qed.
