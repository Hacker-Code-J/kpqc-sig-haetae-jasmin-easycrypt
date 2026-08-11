require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import CircuitBindings Bindings JWordExtra.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.
from JazzEC require import Array256 Array320.
from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.
import BitEncoding BitChunking.

import Round ZModQ Zq.

from CryptoSpecs require import JWord_extra EclibExtra JWordList.

require import XArray256 XArray320 XArray16 XWord10 ArrayExtra.

lemma truncateu_32_10E (w : W32.t) : BS_W32_W10_U.truncateu10 w = W10.bits2w (take 10 (W32.w2bits w)).
proof.
rewrite /truncateu10 W10.of_intE W32.to_uintE BS2Int.bs2int_mod //;congr.
have {1}-> : 10 = size (take 10 (w2bits w)) by rewrite size_take //.
by rewrite BS2Int.bs2intK.
qed.

op bitlenqm1md : int = 10 . (* bitlen (q-1) - d = 23 - 13 *)
op b_t1 = 1023. (* 2^bitlenqm1md - 1 *)
lemma ilog_b_t1 : ilog 2 b_t1 = bitlenqm1md - 1 by rewrite /b_t1 /=.

(* Circuit spec  *)

op t1_encode_polynomial_lane(c : W32.t) : W10.t =
    BS_W32_W10_U.truncateu10  c.


lemma SimpleBitPack_liftE (p : wpoly) :
  wpoly_urng (b_t1 + 1) p =>
    SimpleBitPack (liftu_wpoly p) b_t1
  = to_list
  (BSWA_320u8.init
     (fun (i0 : int) =>
        W8.init
          (fun (j : int) =>
             (BSWA_256u10.init (fun (i1 : int) => t1_encode_polynomial_lane p.[i1])).[(i0 * 8 + j) %/ 10].[
             (i0 * 8 + j) %% 10]))).
proof.
move=> h @/SimpleBitPack; (pose l := ilog 2 _) => /=.
have := ilog_b_t1; rewrite /bitlenqm1md /= => ?.
have ? : size
   (flatten (map (fun (x : W32.t) => IntegerToBits (asint (incoeff (to_uint x))) (l + 1)) (to_list p))) = 256*10.
+  rewrite  (size_flatten_ctt (l+1)).
  +  by move => x; rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs //.
  by rewrite size_map /= size_to_list  /l /= /#.

rewrite /BitsToBytes !array256_mapE /=.
rewrite  -map_comp &(eq_sym) -map_comp /(\o) /=.
apply (eq_from_nth witness); 1: by rewrite size_to_list /= size_map size_iota /#.
move => i; rewrite size_to_list => Hi.
rewrite get_to_list (nth_map witness) /=; 1: by rewrite size_iota /#.
rewrite wordP => j jb.
rewrite !initiE //= initiE 1:/# /= get_bits2w // nth_take // 1:/# nth_drop;2: by smt().
+ rewrite nth_iota /#.
rewrite (nth_flatten false (l+1)).
+ by rewrite allP => x;rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs //.
rewrite nth_iota 1:/#  (nth_map witness) /=; 1: by rewrite size_to_list /= /#.
rewrite /t1_encode_polynomial_lane .
pose v:=p.[(i * 8 + j) %/ 10].
have -> : p.[(8 * i + j) %/ (l + 1)] = v by smt().
move: h => @/wpoly_urng /array256_allP /(_ v _) //= /=.
+ rewrite /to_list /mkseq mapP; exists ((i * 8 + j) %/ 10); smt(mem_iota).
move => h.
rewrite incoeffK truncateu_32_10E get_bits2w 1:/#.
rewrite nth_take 1,2:/#.
rewrite /IntegerToBits w2bits_int2bsE /l ilog_b_t1 /bitlenqm1md /= (modz_small _ q) 1:/# /BS2Int.int2bs.
by rewrite !nth_mkseq 1,2:/# /= /#.
qed.

require import WArray1024 WArray320.

lemma t1_encode_polynomial _a :
   hoare [ M.t1__encode_polynomial :
       t1 = _a /\ wpoly_urng (b_t1 + 1) _a
     ==>
       to_list res = SimpleBitPack (liftu_wpoly _a) b_t1
   ].
proc => /=;inline *.
proc change ^while.1 : { coefficients <- if (0 <= input_offset*8 <= 32*256-256)
                                         then BSWAS_256u32_256.sliceget t1 (input_offset*8)
                                         else get256_direct (WArray1024.init32 (fun (i_0 : int) => t1.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.16 : {t1_encoded <- if (0 <= output_offset*8 <= 8*320-128)
                                       then BSWAS_320u8_128.sliceset t1_encoded (output_offset*8) bytestream
                                       else Array320.init (get8 (set128_direct (WArray320.init8 (fun (i_0 : int) => t1_encoded.[i_0])) output_offset bytestream));}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 2432); last by auto.
                 by move => ?; rewrite BSWAS_320u8_128_slicesetE /#.
proc change 5 : { coefficients <- if (0 <= input_offset*8 <= 32*256-256)
                                  then BSWAS_256u32_256.sliceget t1 (input_offset*8)
                                  else get256_direct (WArray1024.init32 (fun (i_0 : int) => t1.[i_0])) input_offset;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change 20 : { final_encoded_output <- BSWAS_16u8_128.sliceset final_encoded_output 0 bytestream;}.
               + by auto => /> &2;have /= -> := BSWAS_16u8_128_slicesetE final_encoded_output{2} 0 bytestream{2} _;1:smt().
unroll for ^while.
unroll for ^while.
cfold 2.
cfold 498.
wp -3.

conseq (:  t1 = BSWA_256u32.init (fun i => BS_W32_W10_U.zeroextu32 (BS_W32_W10_U.truncateu10 _a.[i])) ==>
    t1_encoded  = let mapped = BSWA_256u10.init (fun i => t1_encode_polynomial_lane _a.[i]) in
    BSWA_320u8.init (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 10].[(i*8+j) %% 10]))); last by circuit.

+ move => &hr [->+]; rewrite /wpoly_urng allP => ?.
  by rewrite tP => k kb; rewrite initiE 1:/# /= /zeroextu32 /truncateu10 /= of_uintK /= modz_small 1:/# to_uintK.
+ by move => &hr [<- Hrng] ? /= => ->;rewrite SimpleBitPack_liftE //=.

qed.

op t1_decode_to_polynomial_lane(c : W10.t) : W32.t =
    BS_W32_W10_U.zeroextu32 c.


lemma SimpleBitUnpack_liftE (bytes : W8.t Array320.t) :
    SimpleBitUnpack (to_list bytes) b_t1
  =
  liftu_wpoly
  (BSWA_256u32.init
     (fun (i0 : int) =>
        BS_W32_W10_U.zeroextu32 (W10.init (fun (j : int) => bytes.[(i0 * 10 + j) %/ 8].[(i0 * 10 + j) %% 8])))).
proof.
move=>  @/SimpleBitUnpack /=; rewrite tP => i ib.
rewrite initiE 1://  /liftu_wpoly mapiE 1:// /= (nth_map []) /=.
+ rewrite size_chunk ilog_b_t1 /= 1:/#.
+ rewrite /BytesToBits (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
congr.
rewrite initiE 1:/# /= /zeroextu32 of_uintK /= modz_small;1: by have /= /#:=W10.to_uint_cmp.
rewrite /W10.to_uint /BitsToInteger;congr.
apply (eq_from_nth false).
+ rewrite size_nth_chunk ilog_b_t1  /= 1:/# 2:/#.
+ rewrite /BytesToBits (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
move => kk.
rewrite size_nth_chunk ilog_b_t1  /= 1:/#.
+ rewrite /BytesToBits (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
move => kkb.
rewrite (nth_chunk 10) 1,2:/#.
+ rewrite /BytesToBits (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
rewrite initiE 1:/# /= nth_take 1,2:/# /= nth_drop 1,2:/# /= /BytesToBits.
rewrite (nth_flatten false 8);1: by rewrite allP => x /=; rewrite mapP => Hx;elim Hx;smt(W8.size_w2bits).
rewrite (nth_map witness);1:smt(Array320.size_to_list).
by rewrite get_w2bits get_to_list /#. 
qed.

lemma t1_decode_polynomial _a :
   hoare [ M.t1__decode_polynomial :
       t1_encoded = _a
     ==>
       liftu_wpoly res = SimpleBitUnpack (to_list _a) b_t1
       /\ wpoly_urng (b_t1 + 1) res
   ].
proc => /=.
proc change ^while.1 : { bytestream <- if (0 <= input_offset*8 <= 8*320-128)
                                       then BSWAS_320u8_128.sliceget t1_encoded (input_offset*8)
                                       else get128_direct (WArray320.init8 (fun (i_0 : int) => t1_encoded.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 2432); last by auto.
                  by move => ?; rewrite -BSWAS_320u8_128_slicegetE /#.
proc change ^while.10 : {t1 <- if (0 <= output_offset*8 <= 32*256-256)
                                then BSWAS_256u32_256.sliceset t1 (output_offset*8) coefficients
                                else Array256.init (get32 (set256_direct (WArray1024.init32 (fun (i_0 : int) => t1.[i_0])) output_offset coefficients));}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 7936); last by auto.
                 by move => ?; rewrite BSWAS_256u32_256_slicesetE /#.
proc change 5 : { bytestream <- BSWAS_320u8_128.sliceget t1_encoded (304*8);}.
                + auto => />.
                  by have /# /= := BSWAS_320u8_128_slicegetE  304 _a _.
proc change 14 : {t1 <- if (0 <= output_offset*8 <= 32*256-256)
                         then BSWAS_256u32_256.sliceset t1 (output_offset*8) coefficients
                         else Array256.init (get32 (set256_direct (WArray1024.init32 (fun (i_0 : int) => t1.[i_0])) output_offset coefficients));}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 7936); last by auto.
                 by move => ?; rewrite BSWAS_256u32_256_slicesetE /#.
unroll for ^while.

cfold 2.
cfold 281.
wp -2.

conseq (: t1_encoded = _a ==>
     t1 = BSWA_256u32.init (fun i => BS_W32_W10_U.zeroextu32 (W10.init (fun j => _a.[(i*10+j) %/ 8].[(i*10+j) %% 8])))); last by circuit.


move=> &hr <- decoded Hdecoded.
split.
- by rewrite Hdecoded SimpleBitUnpack_liftE ~-1://.
- rewrite /wpoly_urng Hdecoded allP => w Hw /=.
  rewrite initiE 1:/# /= /BS_W32_W10_U.zeroextu32 of_uintK /= modz_small /=.
  + by have /= /#:= W10.to_uint_cmp.
  + by have /= /#:= W10.to_uint_cmp.
qed.

lemma t1__decode_polynomial_ll : islossless M.t1__decode_polynomial.
proof.
proc; wp.
while (true) ((256 - 8) * 4 - output_offset); last by auto => /#.
by move => *; auto => /#.
qed.

import VecMat PolyKVec.

require import Array256 Array320 Array1536 Array1920.

lemma t1_encode _a :
    hoare [ M.t1____encode :
       t1 = _a /\ wpolykvec_urng (kvec_unflatten256 _a) (b_t1 + 1)
     ==>
       kvec_unflatten320 res =
           KArray.map (fun (p : poly) => Array320.of_list witness (SimpleBitPack  p b_t1)) (liftu_wpolykvec (kvec_unflatten256 _a))
   ].
have Hkvec := mldsa65_kvec.
proc => /=.
while (0 <= j <= 6 /\ t1 = _a /\ wpolykvec_urng (kvec_unflatten256 _a) (b_t1 + 1)  /\
       forall k, 0 <= k < j =>
       (kvec_unflatten320 encoded).[k] =
       (map (fun (p : poly) => Array320.of_list witness (SimpleBitPack  p b_t1)) (liftu_wpolykvec (kvec_unflatten256 _a))).[k]);
       last first.
       + auto => /> &hr *;do split;1: smt().
         move => r0 j0 *;rewrite tP => k kb; smt().
wp; ecall (t1_encode_polynomial (Array256.init (fun (i_0 : int) => _a.[j * 256 + i_0]))).
auto => /> &hr ?? Hrng H ?;do split;1:smt().
+ move : Hrng; rewrite /wpolykvec_urng /wpoly_urng !allP /=  => Hrng i ib.
  have := Hrng j{hr} _; 1:smt().
  rewrite allP /= initiE 1:/# /= => Hrngj.
  have := Hrngj i _; 1:smt().
  rewrite initiE 1:/# /= initiE 1:/# /= nth_sub 1:/# /#.
move => ?? rr Hrr; do split;1,2: smt().
move => k kbl kbh.
case(0<=k<j{hr}) => *.
+
   have -> : (kvec_unflatten320
   (Array1920.init
      (fun (i : int) => if j{hr} * 320 <= i < j{hr} * 320 + 320 then rr.[i - j{hr} * 320] else encoded{hr}.[i]))).[k] =
    ((kvec_unflatten320 encoded{hr})).[k]; last by smt().
  rewrite !initiE 1..2:/# /= /of_list /= tP => kk kkb.
  rewrite !initiE 1,2:/# !nth_sub 1,2:/# initiE 1:/# /= /#.
have -> : k = j{hr} by smt().
+ have -> :
   (kvec_unflatten320
   (Array1920.init
      (fun (i : int) => if j{hr} * 320 <= i < j{hr} * 320 + 320 then rr.[i - j{hr} * 320] else encoded{hr}.[i]))).[j{hr}]  =
    (rr); last first.
  + have <- := Array320.to_listK witness rr;rewrite Hrr mapiE 1:/# /=;congr;congr.
    rewrite /liftu_wpolykvec mapiE 1:/#;congr;rewrite initiE 1:/# /=.
    rewrite tP => kk kkb; rewrite !initiE 1,2:/# /= nth_sub /#.

rewrite initiE 1:/# /= tP => ii iib.
rewrite  initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
qed.


lemma t1_encode_ll : islossless  M.t1____encode.
proof.
proc => /=.
inline *;while (0<=j<=6) (6-j);auto; last by smt().
unroll for 24;wp.
conseq(_: _ ==> true);1:smt().
while (0 <= input_offset <=  n * 32 %/ 8 - 32 /\ input_offset %% 32 = 0) (n * 32 %/ 8 - 32 - input_offset); auto => /> /#.
qed.

lemma t1_encode_ph _a  :
    phoare [ M.t1____encode :
       t1 = _a /\ wpolykvec_urng (kvec_unflatten256 _a) (b_t1 + 1)
     ==>
       kvec_unflatten320 res =
           KArray.map (fun (p : poly) => Array320.of_list witness (SimpleBitPack  p b_t1)) (liftu_wpolykvec (kvec_unflatten256 _a)) ] = 1%r by conseq t1_encode_ll (t1_encode _a).
