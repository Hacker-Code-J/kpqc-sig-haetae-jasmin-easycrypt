require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import CircuitBindings Bindings JWordExtra.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.
from JazzEC require import Array256 Array640.
from Spec require import GFq Rq Serialization Conversion Parameters MLDSA_W32_Rep.
import BitEncoding BitChunking.

import Round ZModQ Zq.

require import ArrayExtra.
from CryptoSpecs require import JWord_extra EclibExtra JWordList.

require import XArray256 XArray640 XArray16 XWord20.

lemma truncateu_32_20E (w : W32.t) : BS_W32_W20_U.truncateu20 w = W20.bits2w (take 20 (W32.w2bits w)).
proof.
rewrite /truncateu20 W20.of_intE W32.to_uintE BS2Int.bs2int_mod //;congr.
have {1}-> : gamma1_bits = size (take gamma1_bits (w2bits w)) by rewrite size_take //.
by rewrite BS2Int.bs2intK.
qed.

import W20.
lemma to_sint_uint_rng_pos_20(xx : W20.t) :
    0 <= to_sint xx  <=> 0 <= to_uint xx < 524288.
 have /= Hxx := W20.to_uint_cmp xx.
 rewrite /to_sint /smod /= /#.
qed.

lemma to_sint_uint_rng_neg_20(xx : W20.t) :
    to_sint xx < 0  <=> 524288 <= to_uint xx <1048576.
 have /= Hxx := W20.to_uint_cmp xx.
 rewrite /to_sint /smod /= /#.
qed.

(* Circuit spec *)

lemma ilog_gamma1 : ilog 2 (gamma1 - 1 + gamma1) = 19 by rewrite mldsa65_gamma1 /=.

op gamma1_encode_polynomial_lane(c : W32.t) : W20.t =
    BS_W32_W20_U.truncateu20 ((W32.of_int 524288) + (-c)).


lemma BitPack_liftE (p : wpoly) :
  wpoly_srng (gamma1 - 1) gamma1 p =>
    BitPack (lifts_wpoly p) (gamma1 - 1) gamma1
  = to_list (let mapped = BSWA_256u20.init (fun i => gamma1_encode_polynomial_lane p.[i]) in
             BSWA_640u8.init (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 20].[(i*8+j) %% 20]))).
proof.
have gamma1_val := mldsa65_gamma1.
move=> h @/BitPack; (pose l := ilog 2 _) => /=.
have Hlog := ilog_gamma1.
have ? : size
  (flatten (map (fun (x : W32.t) => IntegerToBits (gamma1 - crepr (incoeff (to_sint x))) (l + 1)) (to_list p))) = 256*20.
+  rewrite  (size_flatten_ctt (l+1)).
  +  by move => x; rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs // /#.
  by rewrite size_map /= size_to_list  /l /= /#.

rewrite /BitsToBytes !array256_mapE /=.
rewrite  -map_comp &(eq_sym) -map_comp /(\o) /=.
apply (eq_from_nth witness);1: by rewrite size_to_list /= size_map size_iota /#.
move => i; rewrite size_to_list => Hi.
rewrite get_to_list (nth_map witness) /=; 1: by rewrite size_iota /#.
rewrite wordP => j jb.
rewrite !initiE //= initiE 1:/# /= get_bits2w // nth_take // 1:/# nth_drop;2: by smt().
+ rewrite nth_iota /#.
rewrite (nth_flatten false (l+1)).
+ by rewrite allP => x;rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs // /#.
rewrite nth_iota 1:/#  (nth_map witness) /=; 1: by rewrite size_to_list /= /#.
rewrite /gamma1_encode_polynomial_lane .
pose v:=p.[(i * 8 + j) %/ gamma1_bits].
have -> : p.[(8 * i + j) %/ (l + 1)] = v by smt().
move: h => @/wpoly_srng /array256_allP /(_ v _) //= /=.
+ rewrite /to_list /mkseq mapP; exists ((i * 8 + j) %/ gamma1_bits); smt(mem_iota).
move => h.
rewrite incoeffK_centered 1,2:/# truncateu_32_20E get_bits2w 1:/#.
rewrite nth_take 1,2:/# w2bits_int2bsE.
have  -> := BS2Int.int2bs_cat 20 32 (to_uint (W32.of_int 524288 - v)) _;1:smt().
rewrite /IntegerToBits nth_cat ifT;1: by rewrite BS2Int.size_int2bs /#.
congr;2:smt().
congr;1:smt().
have := (W32.of_uintK (gamma1 - to_sint v)).
rewrite modz_small;1:by smt(pow2_64).
move => <-; rewrite -W32.of_intD';congr.
rewrite W32.of_intN;congr.
rewrite /=.
case (2147483648 <= to_uint v) => ?;last by smt(W32.to_uintK pow2_32).
move : h; rewrite /to_sint /smod ifT /#.
congr;rewrite to_uint_eq of_uintK /=;smt(W32.to_uint_cmp pow2_32).
qed.

require import WArray640 WArray1024.

lemma gamma1_encode_polynomial _a :
   hoare [ M.gamma1____encode_polynomial :
       polynomial = _a /\ wpoly_srng 524287 524288 _a
     ==>
       to_list res = BitPack (lifts_wpoly _a) (gamma1-1) gamma1
   ].
have gamma1_val := mldsa65_gamma1.
proc;inline * => /=.
proc change 2 : { temp <- W64.of_int 524288;}; 1: by  auto; rewrite /(`<<`) /= /#.
proc change 3 : { gamma1 <- zeroextu256 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu256E zeroextu256E.
  rewrite wordP => i ib.
  rewrite pack2E pack2E pack4E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?; 1: by rewrite ifT 1:/# initiE 1:/# /= get_of_list /#.
  case (i %/ 128 = 0) => ?; 2: by auto.
  rewrite initiE 1:/# /= get_of_list 1:/#.
  by have -> /= : (i %% 128 %/ 64) = 1 by smt().
proc change ^while.1 : { coefficients <- if (0 <= input_offset*8 <= 32*256-256)
                                         then BSWAS_256u32_256.sliceget polynomial (input_offset*8)
                                         else get256_direct (WArray1024.init32 (fun (i_0 : int) => polynomial.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.13 : {output <- if (0 <= output_offset*8 <= 8*640-128)
                                    then BSWAS_640u8_128.sliceset output (output_offset*8) lower
                                    else Array640.init (get8 (set128_direct (WArray640.init8 (fun (i_0 : int) => output.[i_0])) output_offset lower));}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 4992); last by auto.
                 by move => ?; rewrite BSWAS_640u8_128_slicesetE /#.
proc change ^while.15 : {output <- if (0 <= output_offset*8 <= 8*640-128)
                                    then BSWAS_640u8_128.sliceset output (output_offset*8) upper
                                    else Array640.init (get8 (set128_direct (WArray640.init8 (fun (i_0 : int) => output.[i_0])) output_offset upper));}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 4992); last by auto.
                 by move => ?; rewrite BSWAS_640u8_128_slicesetE /#.
proc change 8 : { coefficients <- if (0 <= input_offset*8 <= 32*256-256)
                                  then BSWAS_256u32_256.sliceget polynomial (input_offset*8)
                                  else get256_direct (WArray1024.init32 (fun (i_0 : int) => polynomial.[i_0])) input_offset;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change 20 : {output <- if (0 <= output_offset*8 <= 8*640-128)
                             then BSWAS_640u8_128.sliceset output (output_offset*8) lower
                             else Array640.init (get8 (set128_direct (WArray640.init8 (fun (i_0 : int) => output.[i_0])) output_offset lower));}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 4992); last by auto.
                 by move => ?; rewrite BSWAS_640u8_128_slicesetE /#.
proc change 22 : { final_output_block <- BSWAS_16u8_128.sliceset final_output_block 0 upper;}.
               + by auto => /> &2;have /= -> := BSWAS_16u8_128_slicesetE final_output_block{2} 0 upper{2} _;1:smt().
unroll for ^while.
unroll for ^while.
cfold 5.
cfold 439.
wp -3.

conseq (:  _ ==>
           output = let mapped = BSWA_256u20.init (fun i => gamma1_encode_polynomial_lane _a.[i]) in
             BSWA_640u8.init (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 20].[(i*8+j) %% 20])));last by circuit.

+ by move => &hr [<- Hrng] ? /= => ->;rewrite BitPack_liftE //= /#.

qed.


op gamma1_decode_to_polynomial_lane(c : W20.t) : W32.t =
    ((W32.of_int 524288) + (- (BS_W32_W20_U.zeroextu32 c))).

lemma gamma1_decode_lane_sint (c : W20.t) :
    W32.to_sint (gamma1_decode_to_polynomial_lane c) = gamma1 - W20.to_uint c.
have gamma1_val := mldsa65_gamma1.
have Hc := W20.to_uint_cmp c.
rewrite /gamma1_decode_to_polynomial_lane /zeroextu32.
have := W32.to_sintK_small (gamma1 - W20.to_uint c).
have /= /#:= W20.to_uint_cmp .
qed.

lemma BitUnack_liftE (bytes : W8.t Array640.t) :
    BitUnpack (to_list bytes) (gamma1 - 1) gamma1
  =
  (map (fun (w : W32.t) => incoeff (to_sint w))
     (BSWA_256u32.init
        (fun (i : int) =>
           gamma1_decode_to_polynomial_lane
             (W20.init (fun (j : int) => bytes.[(gamma1_bits * i + j) %/ 8].[(gamma1_bits * i + j) %% 8]))))).
proof.
have gamma1_val := mldsa65_gamma1.
move=>  @/BitUnpack /=; rewrite tP => i ib.
rewrite initiE 1:// mapiE //= initiE 1:/# /=.
pose l1 := List.map _ _.
have sl1 : size l1 = n.
+   rewrite /l1;rewrite !size_map size_iota ilog_gamma1 /= /BytesToBits.
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
rewrite (nth_map []) /=.
+ rewrite size_chunk ilog_gamma1 //=.
  rewrite /BytesToBits.
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
congr; rewrite  /gamma1_decode_to_polynomial_lane.
rewrite ilog_gamma1 /= /zeroextu32.
rewrite nth_chunk // 1:/#.
+ rewrite /BytesToBits.
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
have  := BS2Int.bs2int_le2Xs ((take gamma1_bits (drop (gamma1_bits * i) (BytesToBits (to_list bytes))))).
+ rewrite size_take // size_drop 1:/# /max /= (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite !size_map !size_iota /max /=.
  pose ll := if _ then _ else _.
  have -> /= : ll = 20;1: by smt().
rewrite /BitsToInteger.
pose p := BS2Int.bs2int  (take gamma1_bits (drop (gamma1_bits * i) (BytesToBits (to_list bytes)))) .
move => ?.
have ? : 0 <= p by smt(BS2Int.bs2int_ge0).
have <- : p = to_uint (W20.init (fun (j : int) => bytes.[(gamma1_bits * i + j) %/ 8].[(gamma1_bits * i + j) %% 8])); last by have /= :=  W32.to_sintK_small (gamma1 - p); smt().
rewrite /to_uint /p;congr.
apply (eq_from_nth false).
+ rewrite size_take // size_drop 1:/# size_w2bits /BytesToBits.
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
move => k kb.
have ? : size (take gamma1_bits (drop (gamma1_bits * i) (BytesToBits (to_list bytes)))) = gamma1_bits.
+ rewrite size_take // size_drop 1:/# /BytesToBits.
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
rewrite nth_take 1,2:/# nth_drop 1,2:/# /BytesToBits.
rewrite (nth_flatten false 8).
+ rewrite allP => j /=.
  rewrite mapP => Hx;elim Hx;smt(W8.size_w2bits).
rewrite (nth_map witness) /=; 1: by rewrite size_to_list /#.
by rewrite initiE 1:/# /=.
qed.


lemma gamma1_decode_to_polynomial _a :
   hoare [ M.gamma1____decode_to_polynomial :
       bytes = _a
     ==>
       lifts_wpoly res = BitUnpack (to_list _a) (gamma1-1) gamma1 /\
       wpoly_srng (gamma1-1) gamma1 res
   ].
proc => /=.
proc change 1 : { temp <- W64.of_int 524288;}; 1: by  auto; rewrite /(`<<`) /= /#.
proc change 2 : { temp1 <- zeroextu128 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu128E.
  rewrite wordP => i ib.
  rewrite pack2E  initiE 1:/# /= pack2E initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?;1: by rewrite get_of_list /#.
  by rewrite get_of_list 1:/# /= ifF 1:/# /=.
proc change 4 : { temp <- W64.of_int 1048575;}; 1: by auto.
proc change 5 : { temp1 <- zeroextu128 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu128E.
  rewrite wordP => i ib.
  rewrite pack2E  initiE 1:/# /= pack2E initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?;1: by rewrite get_of_list /#.
  by rewrite get_of_list 1:/# /= ifF 1:/# /=.
proc change ^while.1 : { sixteen_bytes <- if (0 <= input_offset*8 <= 8*640-128)
                                          then BSWAS_640u8_128.sliceget bytes (input_offset*8)
                                          else get128_direct (WArray640.init8 (fun (i_0 : int) => bytes.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 4992); last by auto.
                  by move => ?; rewrite -BSWAS_640u8_128_slicegetE /#.
proc change ^while.4 : { sixteen_bytes <- if (0 <= input_offset*8 <= 8*640-128)
                                          then BSWAS_640u8_128.sliceget bytes (input_offset*8)
                                          else get128_direct (WArray640.init8 (fun (i_0 : int) => bytes.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 4992); last by auto.
                  by move => ?; rewrite -BSWAS_640u8_128_slicegetE /#.
proc change ^while.13 : {polynomial <- if (0 <= output_offset*8 <= 32*256-256)
                                        then BSWAS_256u32_256.sliceset polynomial (output_offset*8) coefficients
                                        else Array256.init (get32 (set256_direct (WArray1024.init32 (fun (i_0 : int) => polynomial.[i_0])) output_offset coefficients));}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 7936); last by auto.
                 by move => ?; rewrite BSWAS_256u32_256_slicesetE /#.

unroll for ^while.

cfold 8.
wp -2.
conseq (_: _ ==>
    polynomial = BSWA_256u32.init (fun i => gamma1_decode_to_polynomial_lane (W20.init (fun j =>
               _a.[(20*i+j) %/ 8].[(20*i+j) %% 8])))); last by circuit.

(* Part 1: lifts_wpoly equality, Part 2: wpoly_srng range *)
move=> &hr |>; split.
+ rewrite /lifts_wpoly /=; apply (inj_eq Array256.to_list Array256.to_list_inj).
  by rewrite BitUnack_liftE ~-1:// !array256_mapE; do 2!congr => //.

rewrite /wpoly_srng array256_allP /= => w.
rewrite /to_list mkseqP => He;elim He => k [Hk ->] /=.
rewrite initiE 1:/# /=.
rewrite gamma1_decode_lane_sint.
rewrite mldsa65_gamma1 /=.
have /= /#:= W20.to_uint_cmp.
qed.

import VecMat PolyLVec.

require import Array1280 Array3200.

lemma gamma1_encode _a :
    hoare [ M.gamma1____encode :
       decoded = _a /\ wpolylvec_srng (lvec_unflatten256 _a) (gamma1-1) gamma1
     ==>
       lvec_unflatten640 res =
           LArray.map (fun (p : poly) => Array640.of_list witness (BitPack p (gamma1-1) gamma1)) (lifts_wpolylvec (lvec_unflatten256 _a))
   ].
have Hlvec := mldsa65_lvec.
have Hgamma1 := mldsa65_gamma1.
proc => /=.
while (0 <= i <= 5 /\ decoded = _a /\
       wpolylvec_srng (lvec_unflatten256 _a) (gamma1-1) gamma1  /\
       forall k, 0 <= k < i =>
       (lvec_unflatten640 encoded).[k] =
       (map (fun (p : poly) => Array640.of_list witness (BitPack p (gamma1-1) gamma1)) (lifts_wpolylvec (lvec_unflatten256 _a))).[k]);
       last first.
       + auto => /> &hr *;do split;1: smt().
         by move => r0 j0 *;rewrite tP => k kb; smt().
wp; ecall (gamma1_encode_polynomial (Array256.init (fun (i_0 : int) => _a.[i * 256 + i_0]))).
auto => /> &hr ?? Hrng H ?;do split.
+ move : Hrng; rewrite /wpolylvec_srng /wpoly_srng !allP /=  => Hrng ii iib.
  have := Hrng i{hr} _; 1:smt().
  rewrite allP /= initiE 1:/# /= => Hrngj.
  have := Hrngj ii _; 1:smt().
  rewrite initiE 1:/# /= initiE 1:/# /= nth_sub 1:/# /#.
move => ? rr Hrr; do split;1,2: smt().
move => k kbl kbh.
case(0<=k<i{hr}) => *.
+
   have -> : (lvec_unflatten640
   (Array3200.init
      (fun (i_0 : int) => if i{hr} * 640 <= i_0 < i{hr} * 640 + 640 then rr.[i_0 - i{hr} * 640] else encoded{hr}.[i_0]))).[k] =
    ((lvec_unflatten640 encoded{hr})).[k]; last by smt().
  rewrite !initiE 1..2:/# /= /of_list /= tP => kk kkb.
  rewrite !initiE 1,2:/# !nth_sub 1,2:/# initiE 1:/# /= /#.
have -> : k = i{hr} by smt().
+ have -> :
   (lvec_unflatten640
   (Array3200.init
      (fun (i_0 : int) => if i{hr} * 640 <= i_0 < i{hr} * 640 + 640 then rr.[i_0 - i{hr} * 640] else encoded{hr}.[i_0]))).[i{hr}]  =
    (rr); last first.
  + have <- := Array640.to_listK witness rr;rewrite Hrr mapiE 1:/# /=;congr;congr.
    rewrite /lifts_wpolylvec mapiE 1:/#;congr;rewrite initiE 1:/# /=.
    rewrite tP => kk kkb; rewrite !initiE 1,2:/# /= nth_sub /#.

rewrite initiE 1:/# /= tP => ii iib.
rewrite  initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
qed.

lemma gamma2_encode_polynomial_ll : islossless M.gamma1____encode_polynomial.
proc.
while (0 <= i <= 10) (10 - i); 1: by auto => /> /#.
inline 9; wp;conseq (: _ ==> true); 1: by smt().
by while (0 <= input_offset <= 992 /\ input_offset %% 32 = 0) (992 - input_offset); move => *; inline *; auto => /> /#.
qed.

lemma gamma1_encode_ll : islossless  M.gamma1____encode.
proc;unroll for ^while.
by do 5!(wp;call gamma2_encode_polynomial_ll).
qed.

lemma gamma1_encode_ph _a :
    phoare [ M.gamma1____encode :
       decoded = _a /\ wpolylvec_srng (lvec_unflatten256 _a) (gamma1-1) gamma1
     ==>
       lvec_unflatten640 res =
           LArray.map (fun (p : poly) => Array640.of_list witness (BitPack p (gamma1-1) gamma1)) (lifts_wpolylvec (lvec_unflatten256 _a))
   ] = 1%r by conseq gamma1_encode_ll (gamma1_encode _a).


lemma gamma1_decode _a :
    hoare [ M.gamma1____decode :
       encoded = _a
     ==>
       lifts_wpolylvec (lvec_unflatten256 res) =
           LArray.map (fun p => BitUnpack (to_list p) (gamma1-1) gamma1) (lvec_unflatten640 _a) /\
       wpolylvec_srng (lvec_unflatten256 res) (gamma1-1) gamma1
   ].
have Hlvec := mldsa65_lvec.
have Hgamma1 := mldsa65_gamma1.
proc => /=.
while (0 <= i <= 5 /\ encoded = _a /\
       (forall k, 0 <= k < i =>
           (lifts_wpolylvec (lvec_unflatten256 decoded)).[k] =
           (map (fun (p : W8.t Array640.t) => BitUnpack (to_list p) (gamma1 - 1) gamma1) (lvec_unflatten640 _a)).[k]) /\
       (forall k, 0 <= k < i =>
           wpoly_srng (gamma1-1) gamma1 (lvec_unflatten256 decoded).[k]));
       last first.
       + auto => /> &hr *;do split;1,2: smt().
         move => r0 k ? r1 i0 Heq Hrng; split; 1: by rewrite tP => /#. 
         rewrite /wpolylvec_srng allP => i ib.
         by apply Hrng; smt(mldsa65_lvec).
wp; ecall (gamma1_decode_to_polynomial (Array640.init (fun (i_0 : int) => _a.[i * (gamma1_bits * n %/ 8) + i_0]))).
auto => /> &hr ?? Heq Hrng  ? rr Hrr1 Hrr2;do split;1,2:smt().
+ move => k kbl kbh.
  case(0<=k<i{hr}) => *.
  + have -> : (lifts_wpolylvec
     (lvec_unflatten256
        (Array1280.init
           (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else decoded{hr}.[i_0])))).[k] =
      (lifts_wpolylvec (lvec_unflatten256 decoded{hr})).[k]; last by smt().
    rewrite !mapiE 1..2:/# initiE 1:/# /= initiE 1:/# /= tP =>  ii iib.
    rewrite mapiE 1:/# /= initiE 1:/# /= mapiE 1:/# /= initiE 1:/# /= !nth_sub 1,2:/# initiE 1:/# /= /#.
  have -> : k = i{hr} by smt().
  + have -> : (lifts_wpolylvec
     (lvec_unflatten256
        (Array1280.init
           (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else decoded{hr}.[i_0])))).[i{hr}]  =
      (lifts_wpoly rr); last first.
    + rewrite Hrr1 mapiE 1:/# /=;congr;congr;rewrite  initiE 1:/# /= tP => ii iib.
      by rewrite initiE 1:/# get_of_list 1:/# /= nth_sub /#.
  rewrite mapiE 1:/# /= initiE 1:/# /= tP => ii iib.
  rewrite !mapiE 1,2:/# /= initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
move => k kbl kbh.
case(0<=k<i{hr}) => *.
+ have -> : (lvec_unflatten256
     (Array1280.init
        (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else decoded{hr}.[i_0]))).[k] =
    (lvec_unflatten256 decoded{hr}).[k]; last by (apply Hrng; smt()).
  rewrite initiE 1:/# /= tP => ii iib.
  rewrite initiE 1:/# /= get_of_list // nth_sub 1:/# initiE 1:/# /= get_of_list 1:/# nth_sub /#.
have -> : k = i{hr} by smt().
have -> : (lvec_unflatten256
     (Array1280.init
        (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else decoded{hr}.[i_0]))).[i{hr}] =
    rr.
+ rewrite initiE 1:/# /= tP => ii iib.
  rewrite initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
exact Hrr2.
qed.

lemma gamma2_decode_to_polynomial_ll : islossless M.gamma1____decode_to_polynomial.
proc.
while (0 <= output_offset <= 1024 /\ output_offset %% 32 = 0) (1024 - output_offset); 1: by auto => /> /#.
by auto => /> /#.
qed.

lemma gamma1_decode_ll : islossless  M.gamma1____decode.
proc;unroll for ^while.
by do 5!(wp;call gamma2_decode_to_polynomial_ll).
qed.


lemma gamma1_decode_ph _a :
    phoare [ M.gamma1____decode :
       encoded = _a
     ==>
       lifts_wpolylvec (lvec_unflatten256 res) =
           LArray.map (fun p => BitUnpack (to_list p) (gamma1-1) gamma1) (lvec_unflatten640 _a) /\
       wpolylvec_srng (lvec_unflatten256 res) (gamma1-1) gamma1
   ] = 1%r
 by conseq gamma1_decode_ll (gamma1_decode _a).
