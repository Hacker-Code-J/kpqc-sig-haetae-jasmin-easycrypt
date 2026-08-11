require import AllCore List IntDiv RealExp StdBigop.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Gamma1.
from JazzEC require import Array256 Array61 Array1536 Array3309.
from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.
import BitEncoding BitChunking.

import Round ZModQ Zq.

require import ArrayExtra.
from CryptoSpecs require import JWord_extra EclibExtra JWordList.

import VecMat PolyKVec.


lemma decode_hint :
    equiv [ HintPackUnpack.hintBitUnpack ~ M.signature____decode_hint :
       arg{1} = to_list arg{2}.`2 
     ==>
      (res{1} = None  => res{2}.`2 = -W64.one) /\
      (res{1} <> None =>
         res{2}.`2 = W64.zero /\
         liftu_wpolykvec (kvec_unflatten256 res{2}.`1) = oget res{1} /\
         wpolykvec_urng (kvec_unflatten256 res{2}.`1) 2)
   ].
proof.
have whint := mldsa65_w_hint.
have kvec := mldsa65_kvec.
proc => /=.
wp; conseq (_: _ ==>
      (error{1} => ill_formed_hint{2} = W64.one) /\
      (!error{1} =>
         ill_formed_hint{2} = W64.zero /\
   liftu_wpolykvec (kvec_unflatten256 hints{2}) = h{1} /\
   wpolykvec_urng (kvec_unflatten256 hints{2}) 2)).
+ auto => /> error1 h1 h2 error2 He Hne;split;1:smt().
  move => ?; move : Hne; have ->/= : error1 = false; 1:smt().
  move => [#] ->?? /=;split;1:by ring.
  by smt().

(* Initialization *)
seq 3 2  :
  (#pre /\
   !error{1} /\
   index{1} = previous_true_hints_seen{2} /\
   (error{1} => ill_formed_hint{2} = W64.one) /\
   (!error{1} => ill_formed_hint{2} = W64.zero));
   1: by auto => />.

(* Check for zero *)
seq 2 5 :
  (#{/~!error{1}}{~index{1} = previous_true_hints_seen{2}}pre /\
   (!error{1} => index{1} = previous_true_hints_seen{2}) /\
   (error{1} => ill_formed_hint{2} = W64.one) /\
   (!error{1} => ill_formed_hint{2} = W64.zero) /\
   (!error{1} =>
      liftu_wpolykvec (kvec_unflatten256 hints{2}) = h{1} /\
      wpolykvec_urng (kvec_unflatten256 hints{2}) 2)
  ); last first.
+ while (#post /\
     y{1} = to_list hint_encoded{2} /\
     (!error{1} => index{1} = encoded_offset {2})); last first.
   + auto => /> &1 &2 ??Hne?;split; 1: smt().
     do split;rewrite /SETcc.
     + move => ??;case (55 <= previous_true_hints_seen{2}) => ?.
       + rewrite wordP => i ib; rewrite orwE /=;smt(W8.nth_one). 
       by rewrite Hne 1:/# or0w /truncateu8 /= /#.
     + case (55 <= previous_true_hints_seen{2}) => ?.
       + rewrite wordP => Hw; have /= := Hw 0 _;1:smt().
       by rewrite W8.nth_one /=.
    by rewrite or0w /truncateu8 /= to_uint_eq /= => ?;smt(W64.to_uint1 W64.to_uint0).
   case (to_uint (nth witness y{1} index{1}) <> 0).
   + rcondt {1} ^if;1: by auto.
     rcondt {2} ^if; 1: by  auto => /> *; rewrite to_uint_eq to_uint_zeroextu64 /#.
     rcondf {2} ^if; 1: by auto => />;by smt(W64.to_uint1 W64.to_uint0).
     auto => /> &1 &2 ?????;rewrite /SETcc.
     case (55 <= encoded_offset{2}) => ?;1: smt(W8.wordP orwE W8.nth_one).
     by rewrite or0w /truncateu8 /= to_uint_eq /=.
   + rcondf {1} ^if;1: by auto.
     rcondf {2} ^if; 1: by auto => /> *;rewrite to_uint_eq  to_uint_zeroextu64 /#.
     rcondt {2} ^if; 1: by auto => />;by smt(W64.to_uint1 W64.to_uint0).
     auto => /> &1 &2 ??????;split;1:smt().
     rewrite /SETcc;split.
     +  case (55 <= encoded_offset{2} + 1) => ?;1: smt(W8.wordP orwE W8.nth_one).
        by rewrite or0w /truncateu8 /= to_uint_eq /=;by smt(W64.to_uint1 W64.to_uint0).
     case (55 <= encoded_offset{2} + 1) => ?;2: smt(W64.to_uint1 W64.to_uint0).
     rewrite wordP => Hw; have /= := Hw 0 _;1:smt().
     by rewrite W8.nth_one /=.

(* Main loop *)
while (0 <= i{1} <= kvec /\
    i{1} = encoded_offset{2} /\
   y{1} = to_list hint_encoded{2} /\
   (error{1} => ill_formed_hint{2} = W64.one) /\
  (!error{1} => index{1} = previous_true_hints_seen{2}) /\
  (error{1} => ill_formed_hint{2} = W64.one) /\
  (!error{1} => ill_formed_hint{2} = W64.zero) /\
  (!error{1} =>
     forall k, 0 <= k < i{1} =>
       (liftu_wpolykvec (kvec_unflatten256 hints{2})).[k] = h{1}.[k] /\
       wpoly_urng 2 (kvec_unflatten256 hints{2}).[k])); last first.
+ auto => /> &1 &2 *;do split;1..3:smt().
  move => e1 h1 d12 eo2 h2 if2 ?????????H H0;split.
  + rewrite tP => k kb.
    have := H H0 k _;smt().
  rewrite /wpolykvec_urng allP => k kb.
  by have := H H0 k _;smt().

seq 0 2 : (#pre /\ decoded_offset{2} = 256*encoded_offset{2});
  1: by auto => /> &1 &2 ???????;rewrite /(`<<`) /= /#.

(* Set Zero *)
seq 1 2 : (#pre /\ 
      (liftu_wpolykvec (kvec_unflatten256 hints{2})).[i{1}] = h{1}.[i{1}] /\
      wpoly_urng 2 (kvec_unflatten256 hints{2}).[i{1}]).
 + wp; conseq />;1:smt().
   while {2} (0 <= j{2} <= n /\ 0 <= encoded_offset{2} < kvec /\
      decoded_offset{2} = encoded_offset{2} * n /\
     (forall (k : int),
        0 <= k < encoded_offset{2} =>
          (liftu_wpolykvec (kvec_unflatten256 hints{2})).[k] =
            h{1}.[k] /\
     wpoly_urng 2 (kvec_unflatten256 hints{2}).[k]) /\
     (forall jj, 0 <= jj < j{2} =>
  (kvec_unflatten256 hints{2}).[encoded_offset{2}].[jj] = W32.zero)) (n - j{2}); last first.
   + auto => /> &1 &2 ????????;split;1:smt().
      move  => h2 j2;split;1:smt().
      move => ??????H; do split.
      + move => k kbl kbh.
        split.
        + by rewrite mapiE 1:/# get_setE 1:/# ifF 1:/#; smt(KArray.mapiE).
        by smt(KArray.allP).
      + rewrite get_setE 1:/# ifT 1:/# tP => k kb.
        by  rewrite mapiE 1:/# /= Array256.initiE 1:/# /=  mapiE 1:/# /= H 1:/# /=.
      + rewrite /wpoly_urng allP => k kb /=.
        by rewrite H /#.
 + move => &1 _z;auto => /> &2 ???? H H0 ?; do split; 1,2,5:smt().
   + move => k kbl kbh.
     have  := H k _;1:smt().
     rewrite mapiE 1:/# /= tP /wpoly_urng allP => [# HH HH0].
     split.
     + rewrite mapiE 1:/# /= tP => kk kkb.
       rewrite mapiE 1:/# /= initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /=.
       by have := HH kk kkb; rewrite  initiE 1:/# /= mapiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= get_setE /#.
   +  rewrite allP => kk kkb /=;rewrite initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= get_setE 1:/#.
     have /= := HH0 kk kkb.
     rewrite initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= => HH1.
     by smt().
   + move => jj jjbl jjbh.
     rewrite initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /=.
     case (jj = j{2}) => ?.
     + by rewrite get_setE 1:/# ifT 1:/#.
     rewrite get_setE 1:/# ifF 1:/#.
     have /= := H0 jj _;1:smt().
     by rewrite initiE 1:/# /= get_of_list 1:/# nth_sub /#.

 sp 0 1;if{2}.
 + rcondt{1} 1.
   + auto => /> &2 ??????????H;left.
     by move : H; rewrite to_uint_zeroextu64 /#.
     auto => /> &1 &2 *;do split;1:smt(W64.to_uint_eq W64.to_uint0 W64.to_uint1). 
     move => ?; rewrite /SETcc /= wordP.
     by rewrite /truncateu8 /=;smt(W8.orwE W8.nth_one  W8.to_uint1 W8.to_uint0).
 if{2}.
 + rcondt{1} 1;1: by auto => /> &2 ??????????; rewrite to_uint_zeroextu64 /= /#.
   auto => /> &1 &2 *;do split;1:smt(W64.to_uint_eq W64.to_uint0 W64.to_uint1). 
   move => ?; rewrite /SETcc /= wordP.
   by rewrite /truncateu8 /=;smt(W8.orwE W8.nth_one  W8.to_uint1 W8.to_uint0).

   
rcondf{1} 1.
+ auto => /> &2 ?????????H H0.
  move :H H0; rewrite !to_uint_zeroextu64 /= => *.
  by rewrite oraE  negb_or /#.

seq 1 4 : (#pre /\
    j{2} = index{1} /\
    _first{1} = previous_true_hints_seen{2} /\
    ((done2{2} = W8.zero) =
      (index{1} < to_uint (nth witness y{1} (w_hint + i{1})) && !error{1}))).
 + auto => /> &1 &2 ?????????.
   rewrite /SETcc to_uint_zeroextu64 /= => H H0.
   have -> : truncateu8 ill_formed_hint{2} = W8.zero; last by rewrite W8.orw0;smt(W8.to_uint_eq W8.to_uint0 W8.to_uint1).
   have -> : ill_formed_hint{2} = W64.zero by smt().
   by simplify.


 seq 1 1 : (
  (* Core equalities and bounds *)
  0 <= i{1} <= kvec /\
  i{1} < kvec /\
  i{1} = encoded_offset{2} /\
  y{1} = to_list hint_encoded{2} /\
  j{2} = index{1} /\
  _first{1} = previous_true_hints_seen{2} /\
  index{1} <= to_uint hint_encoded{2}.[w_hint + encoded_offset{2}] /\

  
  (* Hint encoding *)
  current_true_hints_seen{2} = to_uint (zeroextu64 hint_encoded{2}.[55 + encoded_offset{2}]) /\
  
  (* Offset relation *)
  decoded_offset{2} = n * encoded_offset{2} /\
  
  (* Ill-formed hint state *)
  (error{1} => ill_formed_hint{2} = W64.one) /\
  (!error{1} => ill_formed_hint{2} = W64.zero) /\
  
  (* Correctness invariants *)
  (!error{1} =>
    forall (k : int), 0 <= k < i{1} + 1=>
      (liftu_wpolykvec (kvec_unflatten256 hints{2})).[k] = h{1}.[k] /\
      wpoly_urng 2 (kvec_unflatten256 hints{2}).[k]) /\
  
  (* Loop control *)
  done2{2} <> W8.zero /\
  ((done2{2} = W8.zero) <=>
    (index{1} < to_uint (nth witness y{1} (w_hint + i{1})) && !error{1}))

 ); last first.
 + if{2}; auto => /> &1 &2 [#] *; do split;3:smt(W8u8.to_uint_zeroextu64).
   move => ?; do split;1..3:smt(W8u8.to_uint_zeroextu64).
   + by move => ?; rewrite /SETcc /truncateu8 /= /#.
   + rewrite /SETcc /truncateu8 /=;smt(W8.orwE W8.nth_one  W8.to_uint1 W8.to_uint0).
   + rewrite /SETcc /truncateu8 /=; smt( W64.to_uint1 W64.to_uint0).
   + move => ?;rewrite /SETcc /truncateu8 /=.
     have -> : W8.of_int (to_uint ill_formed_hint{2}) = W8.one; last
       by rewrite wordP; smt(W8.orwE W8.nth_one  W8.to_uint_eq W8.to_uint1 W8.to_uint0).
     by rewrite to_uint_eq /=;smt(W64.to_uint1).

 while (#{/~done2{2} <> W8.zero}post); last by auto => />;smt(W8u8.to_uint_zeroextu64).

if {1}.
+ seq 1 2 : (#{/~!error{1}}pre /\ error{1} /\ ill_formed_hint{2} = W64.one).
  + rcondt {2} 2; 1: by  auto => /> /#.
    rcondt {2} 3;1: by auto => /> &hr *;rewrite uleE /= !to_uint_zeroextu64 /#.
    by auto.
    auto => /> => &1 &2 [#] ????????;split;1: smt(W64.to_uint1 W64.to_uint0).
    move => ?; rewrite /SETcc !to_uint_zeroextu64 /truncateu8 /=.
    by rewrite !wordP;split =>  *;smt(W8.orwE W8.nth_one W8.to_uint1 W8.to_uint0).

seq 0 2 : (#pre /\
    hint_at_j{2} = zeroextu64 hint_encoded{2}.[j{2}]).
+ auto => /> &1 &2 ???????????.
  by rewrite !to_uint_eq !uleE /= !to_uint_zeroextu64 /#.

rcondt {2} 1; 1: by auto => /> /#.

auto => /> &1 &2 ????? H0 H????.
have ? : 0<= to_uint hint_encoded{2}.[index{1}]  < 256 by smt(W8.to_uint_cmp pow2_8).
  
do split; 1:smt().

+ move => k kbl kbh;split.
  rewrite mapiE 1:/# initiE 1:/# /= tP => kk kkb.
  rewrite mapiE 1:/# /= get_of_list 1:/# /= nth_sub 1:/# /=.
  have := H _ k _;1,2:smt().
  rewrite mapiE 1:/# initiE 1:/# /= tP => [# H1 H2].
  have := H1 kk _;1:smt().
  rewrite mapiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= => H3.
  rewrite !to_uint_zeroextu64 !get_setE 1,2:/#. 
  case (k = encoded_offset{2}) => ? ; last by smt().
  case (kk = to_uint hint_encoded{2}.[index{1}]) => ?;2: by smt(Array256.get_setE).
  by rewrite ifT 1:/# /=; smt(Array256.get_setE).

+ rewrite to_uint_zeroextu64 /wpoly_urng allP => kk kkb /=.
  have [?+] := H _ k _;1,2:smt().
  rewrite /wpoly_urng allP /= => H1.
  rewrite initiE 1:/# /= get_of_list 1:/# /= nth_sub 1:/# /= get_setE 1:/#.
  have := H1 kk _;1:smt().
  rewrite initiE 1:/# initiE 1:/# /= nth_sub 1:/#.
  by case (n * k + kk = n * encoded_offset{2} + to_uint hint_encoded{2}.[index{1}]) => //=.

+ by rewrite /SETcc H0 // to_uint_zeroextu64 /= wordP;smt(W8.wordP W8.orwE W8.to_uint_eq W8.to_uint1 W8.to_uint0 W64.to_uint1 W64.to_uint0).

+ by move =>?;rewrite /SETcc H0 // to_uint_zeroextu64 /= wordP => *; smt(W8.wordP W8.zerowE W8.orwE W8.to_uint_eq W8.to_uint1 W8.to_uint0 W64.to_uint1 W64.to_uint0).

  + by move =>?;rewrite /SETcc H0 // to_uint_zeroextu64 /= wordP => *; smt(W8.wordP W8.zerowE W8.orwE W8.to_uint_eq W8.to_uint1 W8.to_uint0 W64.to_uint1 W64.to_uint0).

 + by rewrite /SETcc H0 // to_uint_zeroextu64 /= wordP;smt(W8.wordP W8.orwE W8.to_uint_eq W8.to_uint1 W8.to_uint0 W64.to_uint1 W64.to_uint0).
    
qed.

op count_nonzero_coeffs(p : poly) = count (fun c => c = Zq.one) (to_list p).

import Bigint BIA. 
op count_nonzero_coeffs_kvec(v : polykvec) =
     big predT count_nonzero_coeffs (to_list v).

op count_nonzero_prefix(v : polykvec) (i j : int) : int =
  big predT count_nonzero_coeffs (take i (to_list v)) +
  (if 0 <= i < kvec then
     count (fun c => c = Zq.one) (take j (to_list v.[i]))
   else 0).

lemma count_nonzero_prefix_one(v : W32.t Array1536.t) (i j : int)  :
   0 <= i < kvec =>
   0 <= j < n =>
   (liftu_wpolykvec (kvec_unflatten256 v)).[i].[j] = Zq.one =>
   count_nonzero_coeffs_kvec (liftu_wpolykvec (kvec_unflatten256 v)) <= w_hint =>
      count_nonzero_prefix (liftu_wpolykvec (kvec_unflatten256 v)) i j < w_hint.
have eq_kvec := mldsa65_kvec.
have eq_w_hint := mldsa65_w_hint.
move => ???.
rewrite /count_nonzero_coeffs_kvec /count_nonzero_prefix ifT 1:/#.
have {1}<- := cat_take_drop i (to_list (liftu_wpolykvec (kvec_unflatten256 v))).
rewrite big_cat.
have {1}<- := cat_take_drop 1 (drop i (to_list (liftu_wpolykvec (kvec_unflatten256 v)))).
rewrite (drop_take1_nth witness);1: by rewrite size_to_list 1:/#.
rewrite big_cat /= drop_drop 1,2:/# /= big_cons big_nil /= ifT 1:/#.
have :  count (fun (c : coeff) => c = Zq.one) (take j (to_list (liftu_wpolykvec (kvec_unflatten256 v)).[i])) <
  count_nonzero_coeffs (liftu_wpolykvec (kvec_unflatten256 v)).[i]; last by smt(count_ge0 sumr_ge0_seq).
rewrite /count_nonzero_coeffs.
have {2}<- := cat_take_drop j (to_list (liftu_wpolykvec (kvec_unflatten256 v)).[i]).
rewrite count_cat.
have {1}<- := cat_take_drop 1 (drop j (to_list (liftu_wpolykvec (kvec_unflatten256 v)).[i])).
rewrite (drop_take1_nth witness);1: by rewrite size_to_list 1:/#.
by rewrite count_cat /= drop_drop 1,2:/# /=;smt(count_ge0).
qed.

op touch_hint(sig_in sig_out : W8.t Array3309.t) =
    forall k, 0<=k<3248 =>
       sig_in.[k] = sig_out.[k].

lemma encode_hint _signature _hint :
    equiv [ HintPackUnpack.hintBitPack ~ M.signature____encode_hint :
       wpolykvec_urng (kvec_unflatten256 hint_0{2}) 2
    /\ count_nonzero_coeffs_kvec _hint <= w_hint
    /\ arg{1} = _hint
    /\ arg{2}.`1 = _signature
    /\ liftu_wpolykvec (kvec_unflatten256 arg{2}.`2) =  _hint
     ==>
      res{1} = mkseq (fun i => res{2}.[3248 + i]) (w_hint+kvec) /\
      touch_hint _signature res{2}
   ].
proof.
have eq_kvec := mldsa65_kvec.
have eq_w_hint := mldsa65_w_hint.
proc => /=.
seq 3 4 : (#{/~signature{2} = _signature}pre
   /\ y{1} = mkseq (fun i => signature{2}.[3248 + i]) (w_hint+kvec)
   /\ touch_hint _signature signature{2}
   /\ index{1} = 0
   /\ hints_written{2} = 0
   /\ i{1} = 0
   /\ i{2} = 0).
+ (* Initialize y to zeros and set counters to 0 *)
  conseq (: _ ==>
     y{1} = mkseq (fun (i0 : int) => signature{2}.[3248 + i0]) hint_bytes
     /\ touch_hint _signature signature{2}
     /\ index{1} = 0
     /\ i{1} = 0
     /\ hints_written{2} = 0
     /\ i{2} = 0); 1: by smt().
  inline *; wp.
  while {2} (0 <= i{2} <= w_hint+kvec
   /\ (forall k, 0 <= k < i{2} =>
               signature{2}.[3248 + k] = W8.zero)
   /\ touch_hint _signature signature{2});
   last by auto => />; smt(eq_in_mkseq).
  by auto => /> &hr; smt(Array3309.get_setE).
  by move => ?;while(true) (61-i); auto => /> /#.
(* Main nested loops *)
seq 1 2 : (#{/~i{1}}{i{2}}{index{1}}{hints_written{2}}pre
    /\ count_nonzero_coeffs_kvec  _hint <= w_hint
   /\ touch_hint _signature signature{2}
   /\ size y{1} = w_hint + kvec
   /\ i{1} = kvec
   /\ i{2} = i{1}
   /\ index{1} = hints_written{2}
   /\ index{1} <= w_hint
   /\  y{1} = mkseq (fun (i0 : int) => signature{2}.[3248 + i0]) hint_bytes); last by auto.
+ (* Outer loop over polynomials *)
  while (
    wpolykvec_urng (kvec_unflatten256 hint_0{2}) 2 /\
    count_nonzero_coeffs_kvec _hint <= w_hint /\
    h{1} =  _hint /\
    liftu_wpolykvec (kvec_unflatten256 hint_0{2}) =  _hint /\           
    size y{1} = hint_bytes /\
    0 <= i{1} <= kvec /\
    i{1} = i{2} /\
    0 <= index{1} <= w_hint /\
    index{1} = hints_written{2} /\
    index{1} = count_nonzero_prefix _hint i{1} 0 /\
   y{1} = mkseq (fun (i0 : int) => signature{2}.[3248 + i0]) hint_bytes /\
    touch_hint _signature signature{2} /\
    condition1{2} = (i{2} < 6)
  ); last first.
 + auto => /> &1 &2 ??;do split;1..3,5..6:smt(size_mkseq).
    + by rewrite /count_nonzero_prefix /= !take0 big_nil /#. 
  wp. (* Inner while loop *)
  while (
       wpolykvec_urng (kvec_unflatten256 hint_0{2}) 2 /\
       count_nonzero_coeffs_kvec _hint <= w_hint /\
        h{1} =  _hint /\
        liftu_wpolykvec (kvec_unflatten256 hint_0{2}) =  _hint /\           
        size y{1} = hint_bytes /\
        0 <= i{1} < kvec /\
        i{1} = i{2} /\
        0 <= index{1} <= w_hint /\
        index{1} = hints_written{2} /\
        index{1} = count_nonzero_prefix _hint i{1} j{1} /\
        0 <= j{1} <= 256 /\
        j{1} = j{2} /\
        y{1} = mkseq (fun (i0 : int) => signature{2}.[3248 + i0]) hint_bytes /\
        touch_hint _signature signature{2} /\
        condition2{2} = (j{2} < 256)
  ); last first.
  + auto => /> &1 &2 Hrng ???????? c1 j2 s2 *; do split;1..3,7..:smt(size_put).
    + rewrite /count_nonzero_prefix ifT 1:/#.
      case (i{1} + 1 = kvec) => ?. 
      + rewrite ifF 1:/# /= (take_nth witness) /=;1:smt(KArray.size_to_list).
        by rewrite big_rcons ifT 1:/# (take_oversize j2) ?size_to_list /#.
      rewrite ifT 1:/# (take_nth witness);1:smt(KArray.size_to_list).
      by rewrite big_rcons ifT 1:/# /= take0 /= (take_oversize j2) ?size_to_list /#.
   + apply (eq_from_nth witness);1:smt(size_put size_mkseq).
     move => k; rewrite size_put size_mkseq /max ifT 1:/# /= => kb.
     rewrite nth_put 1:/# /= !nth_mkseq 1,2:/# /= /=.
     rewrite get_setE 1:/#  /truncateu8 /= of_uintK /=;smt(W8.to_uint_cmp pow2_8).
   + by smt(Array3309.get_setE).

 seq 0 4 : (#pre /\
     to_uint hint_coefficient{2} = asint h{1}.[i{1}].[j{1}]).
 + auto => /> &2 Hrng ? Hh2 ????????. 
   have  /= Hrngp := kvec_unflatten256E i{2} j{2} hint_0{2} (fun (ii : W32.t) => 0 <= to_uint ii < 2) _ _ _;1..3:smt().
   have  /= Hh2p := kvec_unflatten256P i{2} j{2} hint_0{2} (liftu_wpolykvec (kvec_unflatten256 hint_0{2})) (fun (ii : W32.t) => incoeff (to_uint ii)) _ _ _;1..3: smt(). 
   rewrite /(`<<`) /= -Hh2p;smt( incoeffK).

   
if.
 + auto => /> &2 Hrng ? Hh2 ?????????.
   have  /= Hrngp := kvec_unflatten256E i{2} j{2} hint_0{2} (fun (ii : W32.t) => 0 <= to_uint ii < 2) _ _ _;1..3:smt().
   have  /= Hh2p := kvec_unflatten256P i{2} j{2} hint_0{2} (liftu_wpolykvec (kvec_unflatten256 hint_0{2})) (fun (ii : W32.t) => incoeff (to_uint ii)) _ _ _;1..3: smt(). 
   by rewrite !to_uint_eq /=;smt( incoeffK).

 + auto => /> &1 &2 ???????????Hone; do split; 1..2,5..6,8:smt(Array3309.get_setE size_put). 

   + by smt(count_nonzero_prefix_one). 
   + move : Hone;rewrite /kvec_unflatten256 /count_nonzero_prefix ifT 1:/# ifT 1:/# /= (take_nth witness);1: by rewrite size_to_list /#.
     rewrite mapiE 1:/# /= initiE 1:/# /= mapiE 1:/# get_of_list 1:/# nth_sub 1:/# /= => -> /=.
     by rewrite -cats1 count_cat /= /#.
   + apply (eq_from_nth witness);1:smt(size_put size_mkseq).
     move => k; rewrite size_put size_mkseq /max ifT 1:/# /= => kb.
     rewrite nth_put 1:/# /= !nth_mkseq 1,2:/# /= /=.
     rewrite get_setE 1:/#  /truncateu8 /= of_uintK /=;smt(W8.to_uint_cmp pow2_8).
+ auto => /> &1 &2 ???????????Hone; do split; 2..:smt().
   + move : Hone;rewrite /kvec_unflatten256 /count_nonzero_prefix ifT 1:/# ifT 1:/# /=  (take_nth witness);1: by rewrite size_to_list /#.
     rewrite mapiE 1:/# /= initiE 1:/# /= mapiE 1:/# /=get_of_list 1:/# nth_sub 1:/# /=.
     by rewrite -cats1 count_cat /= /#.
qed.

(* ================================================================ *)
(*            Full Signature Encode/Decode Equivalence              *)
(* ================================================================ *)

require import Array48 Array640 Array1280 Array3200 WArray48 Array3309 WArray3309.

(* --------------------------------------------------------------- *)
(*                  Lossless Lemmas                                   *)
(* ---------------------------------------------------------------- *)

lemma signature____encode_hint_ll : islossless M.signature____encode_hint.
proof.
proc;wp.
while (0<=i<=6 /\ condition1 = (i<6)) (6-i); last by unroll for ^while; auto => /> /#. 
+ move => ?; wp; while (0<=i<=6 /\ condition1 = (i<6) /\ (i < 6) /\
                        0<=j<=256 /\ condition2 = (j<256)) (256-j); last by auto => /#.
by move => ?; auto => /> /#.
qed.

lemma signature____encode_ll : islossless M.signature____encode.
proof.
proc.
call signature____encode_hint_ll.
wp.
call (: true ==> true); first by apply gamma1_encode_ll.
by while true (48 - i); auto => /#.
qed.

(* --------------------------------------------------------------- *)
(*                  Full Signature Encode Lemma                      *)
(* ---------------------------------------------------------------- *)
import BytesCT.
lemma signature_encode  (_commitment_hash : W8.t Array48.t) _signer_response _hint :
    equiv [ SigEncDec.sigEncode ~ M.signature____encode :
       arg{1}.`1 = init (fun i => _commitment_hash.[i])
    /\ arg{1}.`2 = lifts_wpolylvec (lvec_unflatten256 _signer_response)
    /\ arg{1}.`3 = liftu_wpolykvec (kvec_unflatten256 _hint)
    /\ wpolykvec_urng (kvec_unflatten256 _hint) 2
    /\ count_nonzero_coeffs_kvec (liftu_wpolykvec (kvec_unflatten256 _hint)) <= w_hint
    /\ wpolylvec_srng (lvec_unflatten256 _signer_response) (gamma1-1) gamma1
    /\ arg{2}.`2 = _commitment_hash
    /\ arg{2}.`3 = _signer_response
    /\ arg{2}.`4 = _hint
       ==>
       BytesSig.to_list res{1} = to_list res{2}
   ].
proof.
have lambda_eq := mldsa65_lambda.
have w_hint_eq := mldsa65_w_hint.
have lvec_eq := mldsa65_lvec.
have kvec_eq := mldsa65_kvec.
have gamma1_eq := mldsa65_gamma1.
proc => /=.
wp.

(* Copy commitment hash to beginning of signature *)
seq 1 2 : (#pre /\ sigbytes{1} = to_list ct{1} /\
      forall k, 0<=k<48 => nth witness sigbytes{1} k =
            signature{2}.[k]).
+ sp 1 0;while {2} (#pre /\ 0 <= i{2} <= 48 /\ i{2} %% 16 = 0 /\
         forall k, 0<=k<i{2} => nth witness sigbytes{1} k =
            signature{2}.[k]).
  + move => &1;auto => /> &2 ??????H?;do split;1..3:smt().
    move => k kbl kbh;rewrite initiE 1:/# /=  initiE 1:/#.
    rewrite WArray3309.get8_set128_directE 1,2:/#.
    case (i{2} <= k < i{2} + 16).
    + by move => ?; rewrite get128E W16u8.pack16bE 1:/# initiE 1:/# /init8 /= WArray48.initiE /#.
    move => ?; have := H k _;1:smt().
    rewrite initiE 1:/# => ->;rewrite /get8 initiE /#.
    
  + by move => &1;while (0 <= i <= 48 /\ i %% 16 = 0) (48-i);  auto  => /> /#.
  auto => /> &2 ???;split;1:smt().
  move => i2 s2 ???? H k kbl kbh.
  have := H k _;1:smt().
  by rewrite initiE 1:/# /=.
  

ecall  (encode_hint signature{2} (liftu_wpolykvec (kvec_unflatten256 _hint))).
while{1} (#{/~sigbytes{1}}pre /\
        0 <= i{1} <= lvec /\
        sigbytes{1} = to_list ct{1}  ++ flatten (mkseq (fun i => BitPack z{1}.[i] (gamma1 - 1) gamma1) i{1})) (lvec - i{1}).
+ move => &2.
  auto => /> &1 ??????;do split;1..2:smt().
  by rewrite mkseqS 1:/# /= flatten_rcons catA /#.
+ by smt().

wp;ecall {2} (gamma1_encode_ph signer_response{2}).
auto => /> &2 ???Hc?rr1 Hrr1;do split; 1,2:smt(mkseq0 cats0).

move => i1;split;1:smt().
move => ????rr2 Hrr2.
have -> : i1 = lvec by smt().

pose ll1 := (to_list (BytesCT.init ("_.[_]" _commitment_hash))).
have ? : size ll1 = 48 by smt(BytesCT.size_to_list).
pose ll2 := (fun (i0 : int) => BitPack (lifts_wpolylvec (lvec_unflatten256 _signer_response)).[i0] (gamma1 - 1) gamma1).
have Hbp : forall i0, 0 <= i0 < kvec => size (ll2 i0) = 640.
+ move => i0 i0b; rewrite /ll2 /= /BitPack /=.
  pose p := (lifts_wpolylvec (lvec_unflatten256 _signer_response)).[i0].
  pose l := (ilog 2 (gamma1 - 1 + gamma1)).
  pose lli := (flatten (map (fun (wi : coeff) => IntegerToBits (gamma1 - crepr wi) (l + 1)) (to_list p))).
  have ? : size lli = 256*20.
+  rewrite /lli (size_flatten_ctt (l+1)).
  +  move => x; rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs //;smt(ilog_gamma1). 
  rewrite size_map /= size_to_list  /l /=;smt(ilog_gamma1).  
  by rewrite /BitsToBytes size_map size_chunk /#. 
pose ll3 := mkseq (fun (i0 : int) => rr2.[3248 + i0]) hint_bytes.
have ? : size ll3 = hint_bytes by smt(size_mkseq).

have ? : size (flatten (mkseq ll2 lvec)) = lvec * 640.
+ rewrite (size_flatten_ctt 640).
  + by move => x; rewrite /mkseq mapP => He; elim He => xx; rewrite mem_iota /ll2 /= /#.
  by smt(size_mkseq).

rewrite BytesSig.of_listK;1:smt(size_cat).
apply (eq_from_nth witness);1: by rewrite size_to_list /=; smt(size_cat).
move => ii; rewrite !size_cat => iib.
case (0 <= ii < 48) => ?.
+ rewrite nth_cat ifT; 1:smt(size_cat).
  rewrite nth_cat ifT; 1:smt(size_cat).
  have := Hrr2;rewrite /touch_hint => Hth.
  rewrite get_to_list /= -Hth 1:/# initiE 1:/# /= initiE 1:/# /=  ifF 1:/#.
  by rewrite -Hc // BytesCT.initiE 1:/# /=.

  
case (3309 - hint_bytes <= ii < 3309) => ?.
+ rewrite nth_cat ifF; 1:smt(size_cat size_mkseq).
  rewrite /ll3 nth_mkseq /=;smt(size_cat).

rewrite nth_cat ifT; 1:smt(size_cat).
rewrite nth_cat ifF; 1:smt(size_cat).
rewrite get_to_list.
have := Hrr2;rewrite /touch_hint => Hth.
rewrite -Hth 1:/# initiE 1:/# /= ifT 1:/#.
have := Hrr1; rewrite tP => Hrr1k.
have := Hrr1k ((ii-48)%/640) _; 1:smt(size_cat).
rewrite mapiE 1:/# /= initiE 1:/# /= tP => Hkk.
have := Hkk ((ii-48)%%640) _; 1:smt().
rewrite !get_of_list 1,2:/# nth_sub 1:/#.
have -> : 640 * ((ii - 48) %/ 640) + (ii - 48) %% 640 = ii - 48 by smt().
move => ->; rewrite /ll2 /= (nth_flatten witness 640).
+ rewrite allP => x; rewrite /mkseq mapP /= => He.
  elim He => xx; rewrite mem_iota => Hxx.
  have := Hbp xx _;1:smt().
  by rewrite /ll2 /= /#.

by rewrite nth_mkseq /#.

qed.

(* ---------------------------------------------------------------- *)
(*                  Full Signature Decode Lemma                      *)
(* ---------------------------------------------------------------- *)
import BytesSig.

lemma signature_decode (_signature : W8.t Array3309.t) :
    equiv [ SigEncDec.sigDecode ~ M.signature____decode :
       arg{1} = BytesSig.init (fun i => _signature.[i])
    /\ arg{2}.`3 = _signature
       ==>
       res{1}.`1 = init (fun i => _signature.[i])
    /\ lifts_wpolylvec (lvec_unflatten256 res{2}.`1) = res{1}.`2
    /\ wpolylvec_srng (lvec_unflatten256 res{2}.`1) (gamma1-1) gamma1
    /\ (res{1}.`3 = None  => res{2}.`3 = -W64.one)
    /\ (res{1}.`3 <> None =>
          res{2}.`3 = W64.zero
       /\ liftu_wpolykvec (kvec_unflatten256 res{2}.`2) = oget res{1}.`3
       /\ wpolykvec_urng (kvec_unflatten256 res{2}.`2) 2)
   ].
proof.
have lambda_eq := mldsa65_lambda.
have w_hint_eq := mldsa65_w_hint.
have lvec_eq := mldsa65_lvec.
have kvec_eq := mldsa65_kvec.
have gamma1_eq := mldsa65_gamma1.
proc => /=.

(* Extract commitment hash (ct) from beginning of signature *)
seq 3 0 : (#pre
   /\ ct{1} = init (fun ii => sigma{1}.[ii])
   /\ i{1} = 0); 1: by auto.

ecall (decode_hint).
wp; ecall {2} (gamma1_decode_ph (Array3200.init  (fun (i0 : int) => signature_encoded{2}.[48 + i0]))).
conseq (: _ ==>
    forall k, 0 <= k < lvec =>
    z{1}.[k] = BitUnpack
     (mkseq (fun (ii : int) =>  sigma{1}.[lambda %/ w1_bits +
               640 * k + ii]) 640) (gamma1 - 1) gamma1).
+ auto => /> z1 Hz1_eq rr0 Hrr0_eq Hrr0_rng; split.
  + apply (eq_from_nth witness);
     1: by  rewrite size_take 1:/# size_drop 1:/# !size_to_list /= /#.
    move => k; rewrite size_take 1:/# size_drop 1:/# !size_to_list /= => kb.
    rewrite nth_take 1,2:/# nth_drop 1,2:/# get_to_list initiE 1:/#.
    by rewrite initiE /#.
  move => H2 rr1 rr2 ? ?; do split.
  + by apply BytesCT.tP => k kb; rewrite !initiE /#.
  + rewrite tP => k kb;  rewrite Hz1_eq 1:/# /= Hrr0_eq mapiE 1:/# /= /lvec_unflatten640.
    congr.
    apply (eq_from_nth W8.zero); 1: by rewrite size_to_list size_mkseq //=.
    move => i; rewrite size_to_list => ib.
    rewrite (nth_change_dfl witness);1:smt(Array640.size_to_list).
    rewrite get_to_list initiE 1:/# /= initiE 1:/# /= nth_mkseq 1:/# /= initiE 1:/# /=.
    rewrite nth_mkseq 1:/# /= BytesSig.initiE /#.

while{1} (0 <= i{1} <= lvec /\
  forall (k : int),
    0 <= k < i{1} =>
    z{1}.[k] =
    BitUnpack (mkseq (fun (ii : int) => sigma{1}.[lambda %/ w1_bits + 640 * k + ii]) 640) (gamma1 - 1) gamma1) (lvec - i{1}); last by auto => /> /#.
move => ??; auto => /> &hr ????;split;last by smt().
do split; 1,2:smt().
move => k ??.
case (i{hr} = k); 1: by move => Hi; rewrite Hi get_setE 1:/# /=.
by move => ?; rewrite get_setE /= /#.
qed.
