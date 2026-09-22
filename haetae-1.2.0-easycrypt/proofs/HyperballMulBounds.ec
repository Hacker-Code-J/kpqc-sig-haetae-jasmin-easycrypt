require import AllCore IntDiv StdOrder.
from Jasmin require import JModel_x86.
require import HyperballFixedPointSpec HyperballFixedPointCorrectness
  HyperballSafeSpec HyperballWordEvaluation SigmaSpec SigmaSquareExact.

lemma hmb_value_nonnegative (x : hb_fp) : 0 <= hb_value x.
proof.
  have hx := W64.to_uint_cmp x.`1; have hy := W64.to_uint_cmp x.`2.
  rewrite /hb_value; smt().
qed.

lemma hmb_operand_limbs (x : hb_fp) : hbs_operand x =>
  0 <= W64.to_uint x.`1 < 562949953421312 /\
  0 <= W64.to_uint x.`2 <= 1099511627776.
proof.
  have hx := W64.to_uint_cmp x.`1; have hy := W64.to_uint_cmp x.`2.
  rewrite /hbs_operand /hbs_radix /hbs_operand_cap /hb_value; smt().
qed.

lemma hmb_mul48_exact (a b : W64.t) :
  W64.to_uint a * W64.to_uint b < 5192296858534827628530496329220096 =>
  W64.to_uint (mul48_word a b).`1 =
    (W64.to_uint a * W64.to_uint b) %% 281474976710656 /\
  W64.to_uint (mul48_word a b).`2 =
    (W64.to_uint a * W64.to_uint b) %/ 281474976710656.
proof.
  move=> hp.
  have ha := W64.to_uint_cmp a; have hb := W64.to_uint_cmp b.
  have hp0 : 0 <= W64.to_uint a * W64.to_uint b by apply IntOrder.mulr_ge0; smt().
  have hq : 0 <= (W64.to_uint a * W64.to_uint b) %/ 281474976710656 <
      18446744073709551616 by apply divz_cmp; smt().
  have hr := modz_cmp (W64.to_uint a * W64.to_uint b) 281474976710656 _;
    first trivial.
  rewrite hwe_mul48_word /= !W64.of_uintK.
  split; rewrite modz_small; smt().
qed.

lemma hmb_rounding_bit (a : W64.t) : W64.to_uint a < 281474976710656 =>
  W64.to_uint (((a `>>>` 47)+W64.one) `>>>` 1) =
    ((W64.to_uint a %/ 140737488355328)+1) %/ 2 /\
  0 <= W64.to_uint (((a `>>>` 47)+W64.one) `>>>` 1) <= 1.
proof.
  move=> ha; have hau := W64.to_uint_cmp a.
  have hq : 0 <= W64.to_uint a %/ 140737488355328 < 2 by apply divz_cmp; smt().
  have hs : W64.to_uint (a `>>>` 47) = W64.to_uint a %/ 140737488355328
    by rewrite W64.to_uint_shr.
  have hadd : W64.to_uint ((a `>>>` 47)+W64.one) =
      W64.to_uint a %/ 140737488355328+1.
  + rewrite W64.to_uintD hs W64.to_uint1 modz_small; smt().
  rewrite W64.to_uint_shr //= hadd; split; first trivial.
  have hd := divz_eq (W64.to_uint a %/ 140737488355328+1) 2.
  have hr := modz_cmp (W64.to_uint a %/ 140737488355328+1) 2 _; first trivial.
  smt().
qed.

lemma hmb_high_product (a b : W64.t) :
  W64.to_uint a <= 1099511627776 => W64.to_uint b <= 1099511627776 =>
  W64.to_uint (mulu_64 a b).`1 <= 65536 /\
  W64.to_uint (mulu_64 a b).`2 + 18446744073709551616*W64.to_uint (mulu_64 a b).`1 =
    W64.to_uint a * W64.to_uint b.
proof.
  move=> ha hb.
  have har := W64.to_uint_cmp a; have hbr := W64.to_uint_cmp b.
  have hp : W64.to_uint a * W64.to_uint b <= 1208925819614629174706176 by smt().
  have he := W64.mulhiP a b.
  have hlo := W64.to_uint_cmp (a*b).
  rewrite W64.muluE /=; smt().
qed.

lemma hmb_add5_uint (a b c d e : W64.t) :
  W64.to_uint a+W64.to_uint b+W64.to_uint c+W64.to_uint d+W64.to_uint e <
    18446744073709551616 =>
  W64.to_uint (a+b+c+d+e) =
    W64.to_uint a+W64.to_uint b+W64.to_uint c+W64.to_uint d+W64.to_uint e.
proof.
  move=> hsum; have hd := W64.to_uint_cmp d; have he := W64.to_uint_cmp e.
  have hfirst := ss_add3_uint a b c _; first smt().
  rewrite (ss_add3_uint (a+b+c) d e _) 1:/# hfirst.
  trivial.
qed.

(* Shared final packing of multiplication and square. Masked left shifts
   keep their exact radix slices even where the 64-bit shift wraps. *)
op hmb_join (r0 r1 high low : W64.t) : hb_fp =
  hb_norm
    ((r0 `>>>` 28)+((r1 `<<<` 20) `&` W64.of_int 281474976710655)+
      ((low `<<<` 20) `&` W64.of_int 281474976710655),
     (r1 `>>>` 28)+((low `>>>` 28)+(high `<<<` 36))).

lemma hmb_join_exact (r0 r1 high low : W64.t) :
  W64.to_uint r0 < 1970324836974592 =>
  W64.to_uint r1 < 4398046511104 => W64.to_uint high <= 65536 =>
  hbs_canonical (hmb_join r0 r1 high low) /\
  hb_value (hmb_join r0 r1 high low) =
    W64.to_uint r0 %/ 268435456 + 1048576*W64.to_uint r1 +
    1048576*(W64.to_uint low + 18446744073709551616*W64.to_uint high).
proof.
  move=> hr0 hr1 hh.
  have h0 := W64.to_uint_cmp r0; have h1 := W64.to_uint_cmp r1.
  have hhi := W64.to_uint_cmp high; have hl := W64.to_uint_cmp low.
  have h028 : 0 <= W64.to_uint (r0 `>>>` 28) < 7340032.
  + rewrite W64.to_uint_shr //=; apply divz_cmp; smt().
  have h128 : 0 <= W64.to_uint (r1 `>>>` 28) < 16384.
  + rewrite W64.to_uint_shr //=; apply divz_cmp; smt().
  have hl28 : 0 <= W64.to_uint (low `>>>` 28) < 68719476736.
  + rewrite W64.to_uint_shr //=; apply divz_cmp; smt().
  have hh36 : W64.to_uint (high `<<<` 36) = W64.to_uint high*68719476736.
  + rewrite W64.to_uint_shl //= modz_small; smt().
  have hm1 := modz_cmp (W64.to_uint r1) 268435456 _; first trivial.
  have hml := modz_cmp (W64.to_uint low) 268435456 _; first trivial.
  pose s0 := (r0 `>>>` 28)+((r1 `<<<` 20) `&` W64.of_int 281474976710655)+
    ((low `<<<` 20) `&` W64.of_int 281474976710655).
  pose s1 := (r1 `>>>` 28)+((low `>>>` 28)+(high `<<<` 36)).
  have hs0 : W64.to_uint s0 = W64.to_uint r0 %/ 268435456 +
      (W64.to_uint r1 %% 268435456)*1048576 +
      (W64.to_uint low %% 268435456)*1048576.
  + rewrite /s0 ss_add3_uint.
    - rewrite !ss_shift20_mask_exact; smt().
    by rewrite W64.to_uint_shr //= !ss_shift20_mask_exact.
  have hs0b : 0 <= W64.to_uint s0 < 844424930131968.
  + move: h028; rewrite W64.to_uint_shr //=; smt().
  have hs1 : W64.to_uint s1 = W64.to_uint r1 %/ 268435456 +
      W64.to_uint low %/ 268435456 + W64.to_uint high*68719476736.
  + rewrite /s1 W64.WRingA.addrA ss_add3_uint.
    - rewrite hh36; smt().
    by rewrite !W64.to_uint_shr //= hh36.
  have hs1b : 0 <= W64.to_uint s1 < 9007199254740992.
  + move: h128 hl28; rewrite !W64.to_uint_shr //=; smt().
  have hcarry : 0 <= W64.to_uint s0 %/ 281474976710656 < 3
    by apply divz_cmp; smt().
  have hnorm := hb_norm_value_exact (s0,s1) _; first rewrite /=; smt().
  rewrite /hmb_join -/s0 -/s1; split.
  + rewrite /hbs_canonical /hbs_radix.
    have [_ hc] := hb_norm_low_bound (s0,s1); exact hc.
  rewrite hnorm /hb_value /= hs0 hs1.
  have hd1 := divz_eq (W64.to_uint r1) 268435456.
  have hdl := divz_eq (W64.to_uint low) 268435456.
  smt().
qed.

lemma hmb_integer_mul_identity (a b c d roundbit : int) :
  (a*c %/ 281474976710656 + roundbit + (a*d) %% 281474976710656 +
    (b*c) %% 281474976710656 + 134217728) %/ 268435456 +
    1048576*((a*d) %/ 281474976710656+(b*c) %/ 281474976710656+b*d) =
  (((a+281474976710656*b)*(c+281474976710656*d)) %/ 281474976710656 +
    roundbit+134217728) %/ 268435456.
proof.
  have he : (a+281474976710656*b)*(c+281474976710656*d) =
    (a*d+b*c+281474976710656*b*d)*281474976710656+a*c by ring.
  rewrite he divzMDl 1://.
  have ha := divz_eq (a*d) 281474976710656.
  have hb := divz_eq (b*c) 281474976710656.
  have hsplit : a*d+b*c+281474976710656*b*d+a*c %/ 281474976710656+roundbit+134217728 =
    (1048576*((a*d) %/ 281474976710656+(b*c) %/ 281474976710656+b*d))*268435456 +
    (a*c %/ 281474976710656+roundbit+(a*d) %% 281474976710656+
      (b*c) %% 281474976710656+134217728) by smt().
  rewrite hsplit divzMDl 1://; ring.
qed.

lemma hmb_integer_round_bounds (product roundbit : int) : 0 <= roundbit <= 1 =>
  product %/ hbs_q <= (product %/ hbs_radix+roundbit+134217728) %/ 268435456 <=
    product %/ hbs_q+1.
proof.
  move=> hd; rewrite /hbs_q /hbs_radix.
  have hbase : product %/ 75557863725914323419136 =
      (product %/ 281474976710656) %/ 268435456.
  + have -> : 75557863725914323419136 = 281474976710656*268435456 by trivial.
    by rewrite divz_mulp.
  have hq := divz_eq (product %/ 281474976710656) 268435456.
  have hr := modz_cmp (product %/ 281474976710656) 268435456 _; first trivial.
  have he : product %/ 281474976710656+roundbit+134217728 =
    ((product %/ 281474976710656) %/ 268435456)*268435456 +
    ((product %/ 281474976710656) %% 268435456+roundbit+134217728) by smt().
  rewrite hbase he divzMDl 1://.
  have hsmall : 0 <= ((product %/ 281474976710656) %% 268435456+roundbit+134217728) %/
      268435456 < 2 by apply divz_cmp; smt().
  smt().
qed.

lemma hmb_floor_scaled_error product value :
  product %/ hbs_q <= value <= product %/ hbs_q+1 =>
  `|hbs_q*value-product| <= hbs_q.
proof.
  rewrite /hbs_q => hv.
  have hd := divz_eq product 75557863725914323419136.
  have hr := modz_cmp product 75557863725914323419136 _; first trivial.
  smt().
qed.

lemma hmb_mul_rounding (x y : hb_fp) : hbs_operand x => hbs_operand y =>
  hbs_canonical (hb_mul x y) /\
  exists roundbit, 0 <= roundbit <= 1 /\
    hb_value (hb_mul x y) =
      ((hb_value x*hb_value y) %/ hbs_radix+roundbit+134217728) %/ 268435456.
proof.
  move=> hx hy.
  have [hxl hxh] := hmb_operand_limbs x hx.
  have [hyl hyh] := hmb_operand_limbs y hy.
  have hpa : 0 <= W64.to_uint x.`1*W64.to_uint y.`1 < 316912650057057350374175801344 by smt().
  have hpb : 0 <= W64.to_uint x.`1*W64.to_uint y.`2 < 618970019642690137449562112 by smt().
  have hpc : 0 <= W64.to_uint x.`2*W64.to_uint y.`1 < 618970019642690137449562112 by smt().
  pose aa := mul48_word x.`1 y.`1.
  pose bb := mul48_word x.`1 y.`2.
  pose cc := mul48_word x.`2 y.`1.
  pose dd := mulu_64 x.`2 y.`2.
  have [ha0 ha1] := hmb_mul48_exact x.`1 y.`1 _; first smt().
  have [hb0 hb1] := hmb_mul48_exact x.`1 y.`2 _; first smt().
  have [hc0 hc1] := hmb_mul48_exact x.`2 y.`1 _; first smt().
  have ha0b : 0 <= W64.to_uint aa.`1 < 281474976710656.
  + rewrite /aa ha0; apply modz_cmp; trivial.
  have ha1b : 0 <= W64.to_uint aa.`2 < 1125899906842624.
  + rewrite /aa ha1; apply divz_cmp; smt().
  have hb0b : 0 <= W64.to_uint bb.`1 < 281474976710656.
  + rewrite /bb hb0; apply modz_cmp; trivial.
  have hb1b : 0 <= W64.to_uint bb.`2 < 2199023255552.
  + rewrite /bb hb1; apply divz_cmp; smt().
  have hc0b : 0 <= W64.to_uint cc.`1 < 281474976710656.
  + rewrite /cc hc0; apply modz_cmp; trivial.
  have hc1b : 0 <= W64.to_uint cc.`2 < 2199023255552.
  + rewrite /cc hc1; apply divz_cmp; smt().
  have [hdhi hdproduct] := hmb_high_product x.`2 y.`2 _ _; first 2 smt().
  pose roundbit := ((aa.`1 `>>>` 47)+W64.one) `>>>` 1.
  have [_ hroundbit] := hmb_rounding_bit aa.`1 _; first smt().
  have hroundbit_b : 0 <= W64.to_uint roundbit <= 1 by exact hroundbit.
  have hconst : W64.to_uint (W64.one `<<<` 27) = 134217728 by
    rewrite W64.to_uint_shl //=.
  pose r0 := aa.`2+roundbit+bb.`1+cc.`1+(W64.one `<<<` 27).
  pose r1 := bb.`2+cc.`2.
  have hr0 : W64.to_uint r0 = W64.to_uint aa.`2+W64.to_uint roundbit+
      W64.to_uint bb.`1+W64.to_uint cc.`1+134217728.
  + by rewrite /r0 hmb_add5_uint 1:/# hconst.
  have hr0b : W64.to_uint r0 < 1970324836974592 by smt().
  have hr1 : W64.to_uint r1 = W64.to_uint bb.`2+W64.to_uint cc.`2.
  + by rewrite /r1 W64.to_uintD_small 1:/#.
  have hr1b : W64.to_uint r1 < 4398046511104 by smt().
  have hform : hb_mul x y = hmb_join r0 r1 dd.`1 dd.`2.
  + by rewrite /hb_mul /hmb_join /r0 /r1 /roundbit /aa /bb /cc /dd /=.
  have [hcanon hvalue] := hmb_join_exact r0 r1 dd.`1 dd.`2 hr0b hr1b hdhi.
  split; first by rewrite hform.
  exists (W64.to_uint roundbit); split; first exact hroundbit_b.
  rewrite hform hvalue hr0 hr1 hdproduct /aa /bb /cc ha1 hb0 hc0 hb1 hc1.
  have h := hmb_integer_mul_identity (W64.to_uint x.`1) (W64.to_uint x.`2)
    (W64.to_uint y.`1) (W64.to_uint y.`2) (W64.to_uint roundbit).
  rewrite /hb_value /hbs_radix; smt().
qed.

lemma hmb_mul_floor_bounds (x y : hb_fp) : hbs_operand x => hbs_operand y =>
  hbs_canonical (hb_mul x y) /\
  (hb_value x*hb_value y) %/ hbs_q <= hb_value (hb_mul x y) <=
    (hb_value x*hb_value y) %/ hbs_q+1.
proof.
  move=> hx hy; have [hc [roundbit [hd he]]] := hmb_mul_rounding x y hx hy.
  split; first exact hc.
  rewrite he; exact (hmb_integer_round_bounds (hb_value x*hb_value y) roundbit hd).
qed.

lemma hmb_mul_error (x y : hb_fp) : hbs_operand x => hbs_operand y =>
  `|hbs_q*hb_value (hb_mul x y)-hb_value x*hb_value y| <= hbs_q.
proof.
  move=> hx hy; have [_ h] := hmb_mul_floor_bounds x y hx hy.
  exact (hmb_floor_scaled_error _ _ h).
qed.

(* square_word truncates at the final radix shift. Unlike hb_mul it does
   not add either of the multiplication rounding terms. *)
lemma hmb_square_floor (x : hb_fp) : hbs_operand x =>
  hbs_canonical (hb_square x) /\
  hb_value (hb_square x) = (hb_value x*hb_value x) %/ hbs_q.
proof.
  move=> hx; have [hxl hxh] := hmb_operand_limbs x hx.
  have hpa : 0 <= W64.to_uint x.`1*W64.to_uint x.`1 < 316912650057057350374175801344 by smt().
  have hpb : 0 <= W64.to_uint x.`1*W64.to_uint x.`2 < 618970019642690137449562112 by smt().
  pose aa := mul48_word x.`1 x.`1.
  pose bb := mul48_word x.`1 x.`2.
  pose dd := mulu_64 x.`2 x.`2.
  have [ha0 ha1] := hmb_mul48_exact x.`1 x.`1 _; first smt().
  have [hb0 hb1] := hmb_mul48_exact x.`1 x.`2 _; first smt().
  have ha0b : 0 <= W64.to_uint aa.`1 < 281474976710656.
  + rewrite /aa ha0; apply modz_cmp; trivial.
  have ha1b : 0 <= W64.to_uint aa.`2 < 1125899906842624.
  + rewrite /aa ha1; apply divz_cmp; smt().
  have hb0b : 0 <= W64.to_uint bb.`1 < 281474976710656.
  + rewrite /bb hb0; apply modz_cmp; trivial.
  have hb1b : 0 <= W64.to_uint bb.`2 < 2199023255552.
  + rewrite /bb hb1; apply divz_cmp; smt().
  have [hdhi hdproduct] := hmb_high_product x.`2 x.`2 _ _; first 2 smt().
  have hzero : aa.`1 `>>>` 48 = W64.zero by apply ss_shr48_zero; smt().
  have hbshift : W64.to_uint (bb.`1 `<<<` 1) = 2*W64.to_uint bb.`1.
  + rewrite W64.to_uint_shl //= modz_small; smt().
  pose r0 := (aa.`1 `>>>` 48)+aa.`2+(bb.`1 `<<<` 1).
  pose r1 := bb.`2 `<<<` 1.
  have hr0 : W64.to_uint r0 = W64.to_uint aa.`2+2*W64.to_uint bb.`1.
  + by rewrite /r0 hzero /= W64.to_uintD_small 1:/# hbshift.
  have hr0b : W64.to_uint r0 < 1970324836974592 by smt().
  have hr1 : W64.to_uint r1 = 2*W64.to_uint bb.`2.
  + rewrite /r1 W64.to_uint_shl //= modz_small; smt().
  have hr1b : W64.to_uint r1 < 4398046511104 by smt().
  have hform : hb_square x = hmb_join r0 r1 dd.`1 dd.`2.
  + by rewrite /hb_square /square_word /hmb_join /hb_norm /r0 /r1 /aa /bb /dd /=.
  have [hcanon hvalue] := hmb_join_exact r0 r1 dd.`1 dd.`2 hr0b hr1b hdhi.
  split; first by rewrite hform.
  rewrite hform hvalue hr0 hr1 hdproduct /aa /bb ha1 hb0 hb1 /hb_value /hbs_q.
  exact (ss_integer_square_identity (W64.to_uint x.`1) (W64.to_uint x.`2)).
qed.

lemma hmb_square_error (x : hb_fp) : hbs_operand x =>
  `|hbs_q*hb_value (hb_square x)-hb_value x*hb_value x| <= hbs_q.
proof.
  move=> hx; have [_ he] := hmb_square_floor x hx.
  apply hmb_floor_scaled_error; rewrite he; smt().
qed.
