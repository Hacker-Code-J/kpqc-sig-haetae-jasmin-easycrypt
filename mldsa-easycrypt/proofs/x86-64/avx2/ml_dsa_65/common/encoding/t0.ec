require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import CircuitBindings Bindings JWordExtra.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.
from JazzEC require import Array256 Array416.
from Spec require import GFq Rq Serialization Conversion Parameters MLDSA_W32_Rep.
import BitEncoding BitChunking.

import Round ZModQ Zq.

require import ArrayExtra.
from CryptoSpecs require import JWord_extra EclibExtra JWordList.

require import XArray256 XArray416 XArray16 XWord13.

lemma truncateu_32_13E (w : W32.t) : BS_W32_W13_U.truncateu13 w = W13.bits2w (take 13 (W32.w2bits w)).
proof.
rewrite /truncateu13 W13.of_intE W32.to_uintE BS2Int.bs2int_mod //;congr.
have {1}-> : 13 = size (take 13 (w2bits w)) by rewrite size_take //.
by rewrite BS2Int.bs2intK.
qed.

lemma to_sint_uint_rng_pos_13(xx : W13.t) :
    0 <= to_sint xx  <=> 0 <= to_uint xx < 4096.
 have /= Hxx := W13.to_uint_cmp xx. 
 rewrite /to_sint /smod /= /#.
qed.

lemma to_sint_uint_rng_neg_13(xx : W13.t) :
    to_sint xx < 0  <=> 4096 <= to_uint xx < 8192.
 have /= Hxx := W13.to_uint_cmp xx. 
 rewrite /to_sint /smod /= /#.
qed.

(* Circuit spec *)

op dpow : int = 4096. (* 2**(d-1) *) 
lemma ilog_dpow : ilog 2 (dpow - 1 + dpow) = 12 by rewrite /dpow /=.

op t0_encode_polynomial_lane(c : W32.t) : W13.t = 
    BS_W32_W13_U.truncateu13 ((W32.of_int dpow) + ([-] c)).

lemma BitPack_liftE (p : wpoly) :
  wpoly_srng (dpow - 1) dpow p =>
    BitPack (lifts_wpoly p) (dpow - 1) dpow
  = to_list (let mapped = BSWA_256u13.init(fun i => t0_encode_polynomial_lane p.[i]) in
             BSWA_416u8.init (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 13].[(i*8+j) %% 13]))).
proof.
move=> h @/BitPack; (pose l := ilog 2 _) => /=.
have Hlog := ilog_dpow.

have ? : size
  (flatten (map (fun (x : W32.t) => IntegerToBits (Top.dpow - crepr (incoeff (to_sint x))) (l + 1)) (to_list p))) = 256*13.
+  rewrite  (size_flatten_ctt (l+1)).
  +  by move => x; rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs //.
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
+ by rewrite allP => x;rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs //.
rewrite nth_iota 1:/#  (nth_map witness) /=; 1: by rewrite size_to_list /= /#. 
rewrite /t0_encode_polynomial_lane .
pose v:=p.[(i * 8 + j) %/ d].
have -> : p.[(8 * i + j) %/ (l + 1)] = v by smt().
move: h => @/wpoly_srng /array256_allP /(_ v _) //= /=.
+ rewrite /to_list /mkseq mapP; exists ((i * 8 + j) %/ d); smt(mem_iota).
move => h. 
rewrite incoeffK_centered 1,2:/# truncateu_32_13E get_bits2w 1:/#.
rewrite nth_take 1,2:/# w2bits_int2bsE.
have  -> := BS2Int.int2bs_cat 13 32 (to_uint (W32.of_int dpow - v)) _;1:smt().
rewrite /IntegerToBits nth_cat ifT;1: by rewrite BS2Int.size_int2bs /#.
congr;2:smt().
congr;1:smt(). 
have := (W32.of_uintK (Top.dpow - to_sint v)).
rewrite modz_small;1:by smt(pow2_64).
move => <-; rewrite -W32.of_intD';congr.
rewrite W32.of_intN;congr. 
rewrite /to_sint /smod /=.
case (2147483648 <= to_uint v) => ?;last by smt(W32.to_uintK pow2_32).
move : h; rewrite /to_sint /smod ifT //= => ?.
congr;rewrite to_uint_eq of_uintK /=;smt(W32.to_uint_cmp pow2_32). 
qed.

require import WArray1024 WArray416 WArray16 Array16.

lemma t0_encode_polynomial _a :
   hoare [ M.t0__encode_polynomial :
       t0 = _a /\ wpoly_srng (dpow-1) dpow _a
     ==>
       to_list res = BitPack (lifts_wpoly _a) (dpow-1) dpow
   ].
proc;inline * => /=. 
proc change ^while.1 : { coefficients <- if (0 <= input_offset*8 <= 32*256-256)
                                         then BSWAS_256u32_256.sliceget t0 (input_offset*8)
                                         else get256_direct (WArray1024.init32 (fun (i_0 : int) => t0.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.20 : { t0_encoded <- if (0 <= output_offset*8 <= 8*416-128)
                                        then BSWAS_416u8_128.sliceset t0_encoded (output_offset*8) bytestream
                                        else Array416.init (get8 (set128_direct (WArray416.init8 (fun (i_0 : int) => t0_encoded.[i_0])) output_offset bytestream));}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 3200); last by auto.
                 by move => ?; rewrite BSWAS_416u8_128_slicesetE /#.
proc change 5 : { coefficients <- if (0 <= input_offset*8 <= 32*256-256)
                                  then BSWAS_256u32_256.sliceget t0 (input_offset*8)
                                  else get256_direct (WArray1024.init32 (fun (i_0 : int) => t0.[i_0])) input_offset;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change 24 : { final_encoded_output <- BSWAS_16u8_128.sliceset final_encoded_output 0 bytestream;}. 
               + by auto => /> &2;have  /= -> := BSWAS_16u8_128_slicesetE final_encoded_output{2} 0 bytestream{2} _;1:smt().

unroll for ^while.
unroll for ^while.
cfold 2.
cfold 622.  
wp -3.

conseq (:  List.all (fun i => 
    _a.[i] \sle W32.of_int (dpow) /\ 
    W32.of_int (1-dpow) \sle _a.[i]) 
    (iota_ 0 256) 
  /\ _a = t0  ==>
           t0_encoded = let mapped = BSWA_256u13.init (fun i => t0_encode_polynomial_lane _a.[i]) in
             BSWA_416u8.init (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 13].[(i*8+j) %% 13])));last by circuit.

+ move => &hr [<- +]; rewrite /wpoly_srng allP /= => Hrng.
  rewrite /(\sle) allP => x; rewrite mem_iota /= => Hx.
  rewrite to_sintK_small //=.
  by rewrite of_sintK /= /smod /= /#.

+ by move => &hr [<- Hrng] ? /= => ->;rewrite BitPack_liftE //=.

qed.

op t0_decode_to_polynomial_lane(c : W13.t) : W32.t = 
    ((W32.of_int dpow) + (- (BS_W32_W13_U.zeroextu32 c))).

lemma BitUnack_liftE (bytes : W8.t Array416.t) :
    BitUnpack (to_list bytes) (dpow - 1) dpow
  =
  (map (fun (w : W32.t) => incoeff (to_sint w))
     (BSWA_256u32.init
        (fun (i : int) =>
           t0_decode_to_polynomial_lane
             (W13.init (fun (j : int) => bytes.[(d * i + j) %/ 8].[(d * i + j) %% 8]))))).
proof.
move=>  @/BitUnpack /=; rewrite tP => i ib.
rewrite initiE 1:// mapiE //= initiE 1:/# /=.
pose l1 := List.map _ _.
have sl1 : size l1 = n.
+   rewrite /l1;rewrite !size_map size_iota ilog_dpow /= /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
rewrite (nth_map []) /=.
+ rewrite size_chunk ilog_dpow //=.
  rewrite /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
congr; rewrite  /t0_decode_to_polynomial_lane.
rewrite ilog_dpow /= /zeroextu32. 
rewrite nth_chunk // 1:/#.
+ rewrite /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
have  := BS2Int.bs2int_le2Xs ((take d (drop (d * i) (BytesToBits (to_list bytes))))).
+ rewrite size_take // size_drop 1:/# /max /= (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite !size_map !size_iota /max /=.
  pose ll := if _ then _ else _.
  have -> /= : ll = 13;1: by smt().
rewrite /BitsToInteger.
pose p := BS2Int.bs2int  (take d (drop (d * i) (BytesToBits (to_list bytes)))) .
move => ?.
have ? : 0 <= p by smt(BS2Int.bs2int_ge0).
have <- : p = to_uint (W13.init (fun (j : int) => bytes.[(d * i + j) %/ 8].[ (d * i + j) %% 8])); last by have /= :=  W32.to_sintK_small (dpow - p); smt().
rewrite /to_uint /p;congr.
apply (eq_from_nth false).
+ rewrite size_take // size_drop 1:/# size_w2bits /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
move => k kb.
have ? : size (take d (drop (d * i) (BytesToBits (to_list bytes)))) = d.
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


lemma t0_decode_to_polynomial _a :
   hoare [ M.t0____decode_polynomial :
       t0_encoded = _a
     ==>
       lifts_wpoly res = BitUnpack (to_list _a) (dpow-1) dpow
       /\ wpoly_srng (dpow-1) dpow res
   ].
proc => /=;inline *.

proc change ^while.1 : { bytestream <- if (0 <= input_offset*8 <= 416*8-128)
                                       then BSWAS_416u8_128.sliceget t0_encoded (input_offset*8)
                                       else get128_direct (WArray416.init8 (fun (i : int) => t0_encoded.[i])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 3200); last by auto.
                  by move => ?; rewrite -BSWAS_416u8_128_slicegetE /#.
proc change ^while.15 : {t0 <- if (0 <= output_offset*8 <= 256*32-256)
                               then BSWAS_256u32_256.sliceset t0 (output_offset*8) coefficients
                               else Array256.init (fun (i : int) =>                                                                                              get32 (set256_direct (WArray1024.init32 (fun (i0 : int) => t0.[i0])) output_offset coefficients) i);}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 7936); last by auto.
                 by move => ?; rewrite BSWAS_256u32_256_slicesetE /#.
proc change 4 : { bytestream <- BSWAS_416u8_128.sliceget t0_encoded (400*8); }.
               + auto => />.
                 by have /# := BSWAS_416u8_128_slicegetE (400) _a _.
proc change 19 : {t0 <- if (0 <= output_offset*8 <= 256*32-256)
                               then BSWAS_256u32_256.sliceset t0 (output_offset*8) coefficients
                               else Array256.init (fun (i : int) =>                                                                                              get32 (set256_direct (WArray1024.init32 (fun (i0 : int) => t0.[i0])) output_offset coefficients) i);}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 7936); last by auto.
                 by move => ?; rewrite BSWAS_256u32_256_slicesetE /#.

unroll for ^while.

cfold 1.
cfold 466.
wp -2.
conseq (_: _ ==>
    t0 = BSWA_256u32.init (fun i => t0_decode_to_polynomial_lane (W13.init (fun j =>
               _a.[(13*i+j) %/ 8].[(13*i+j) %% 8])))); last by circuit.
            
move=> &hr <- decoded Hdecoded.
split.
- rewrite /lifts_wpoly /=; apply (inj_eq Array256.to_list Array256.to_list_inj).
  by rewrite BitUnack_liftE ~-1:// !array256_mapE; do 2!congr => //.
- rewrite /wpoly_srng  allP => w Hw /=.
  rewrite Hdecoded /t0_decode_to_polynomial_lane initiE 1:/# /=.
  pose x := (W13.init (fun (j : int) => t0_encoded{hr}.[(d * w + j) %/ 8].[(d * w + j) %% 8])).
  have ? : 2^13 = 8192 by auto.
  have ? : 0 <= to_sint (BS_W32_W13_U.zeroextu32 x) < 8192.   
    +rewrite /BS_W32_W13_U.zeroextu32 of_sintK /= modz_small;1: smt(W13.to_uint_cmp).
      by rewrite /smod /=ifF; smt(W13.to_uint_cmp).
  rewrite to_sintB_small /=.
  + rewrite of_sintK /smod /= modz_small /#.
  rewrite of_sintK /smod /= ifF 1:/# modz_small /#.
qed.


import VecMat PolyLVec.

require import Array416 Array1536 Array256 Array2496.

lemma t0_decode _a  :
    hoare [ M.t0__decode :
       encoded = _a
     ==>
       lifts_wpolykvec (kvec_unflatten256 res) =
           KArray.map (fun p => BitUnpack (to_list p) (dpow-1) dpow) (kvec_unflatten416 _a)
       /\ wpolykvec_srng (kvec_unflatten256 res) (dpow-1) dpow
   ].
have Hkvec := mldsa65_kvec.
proc => /=.
while (0 <= i <= 6 /\ encoded = _a /\
       forall k, 0 <= k < i =>
       (lifts_wpolykvec (kvec_unflatten256 t0)).[k] =
       (map (fun (p : W8.t Array416.t) => BitUnpack (to_list p) (Top.dpow - 1) Top.dpow) (kvec_unflatten416 _a)).[k]
       /\ wpoly_srng (dpow-1) dpow (kvec_unflatten256 t0).[k]);
       last first.
       + auto => /> &hr *;do split;1: smt().
         move => i0 t00 ??? H; do split.
         + rewrite tP => k kb; smt().
         by smt(KArray.allP).
         
wp; ecall (t0_decode_to_polynomial (Array416.init (fun (i_0 : int) => _a.[i * (d * n %/ 8) + i_0]))).
auto => /> &hr ?? H ?; split;1:smt().
move => ? rr Hrr Hrng; do split;1,2:smt().
move => k kbl kbh.
case(0<=k<i{hr}) => *.
+ have := H k _; 1:smt().
  move => [H1 H2].
  split.
  + have -> : (lifts_wpolykvec
     (kvec_unflatten256
        (Array1536.init
           (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else t0{hr}.[i_0])))).[k] =
      (lifts_wpolykvec (kvec_unflatten256 t0{hr})).[k]; last by smt().
    rewrite !mapiE 1..2:/# initiE 1:/# /= initiE 1:/# /= tP =>  ii iib.
    rewrite mapiE 1:/# /= initiE 1:/# /= mapiE 1:/# /= initiE 1:/# /= !nth_sub 1,2:/# initiE 1:/# /= /#.
  + rewrite /kvec_unflatten256 initiE 1:/# /= /wpoly_srng allP => kk Hkk /=.
    rewrite get_of_list // nth_sub 1:/# initiE 1:/# /=.
    rewrite ifF 1:/#.
    have := H2; rewrite /wpoly_srng allP => H21.
    have /= := H21 kk _; 1:smt().
    rewrite initiE 1:/# /= get_of_list 1:/# nth_sub /#.
have -> : k = i{hr} by smt().
+ split.
  + have -> : (lifts_wpolykvec
     (kvec_unflatten256
        (Array1536.init
           (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else t0{hr}.[i_0])))).[i{hr}]  =
      (lifts_wpoly rr); last first.
    + rewrite Hrr mapiE 1:/# /=;congr;congr;rewrite initiE 1:/# /= tP => ii iib.
      by rewrite initiE 1:/# get_of_list 1:/# /= nth_sub /#.
    rewrite mapiE 1:/# /= initiE 1:/# /= tP => ii iib.
    rewrite !mapiE 1,2:/# /= initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
  + have -> : (kvec_unflatten256
      (Array1536.init
         (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else t0{hr}.[i_0]))).[i{hr}] = rr.
    + rewrite initiE 1:/# /= tP => ii iib; rewrite initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
    by exact Hrng.
qed.


lemma t0_decode_ll : islossless  M.t0__decode.
proof.
proc => /=.
inline *;while (0<=i<=6) (6-i);auto; last by smt().
conseq(_: _ ==> true);1:smt().
while (0 <= input_offset <=  d * n %/ 8 - d /\ input_offset %% d = 0) (d * n %/ 8 - d - input_offset); auto => /> /#.
qed.

lemma t0_decode_ph _a  :
    phoare [ M.t0__decode :
       encoded = _a
     ==>
       lifts_wpolykvec (kvec_unflatten256 res) =
           KArray.map (fun p => BitUnpack (to_list p) (dpow-1) dpow) (kvec_unflatten416 _a)
       /\ wpolykvec_srng (kvec_unflatten256 res) (dpow-1) dpow
    ] = 1%r by conseq t0_decode_ll (t0_decode _a).


lemma t0_encode _a  :
    hoare [ M.t0____encode : 
       t0 = _a /\
       wpolykvec_srng (kvec_unflatten256 _a) (dpow - 1) dpow 
     ==>
      kvec_unflatten416 res = 
           KArray.map (fun p => (Array416.of_list witness (BitPack p (dpow-1) dpow))) (lifts_wpolykvec (kvec_unflatten256 _a))
   ].
have Hkvec := mldsa65_kvec.
proc => /=.
while (0 <= j <= 6 /\ t0 = _a /\
       (forall k, 0 <= k < kvec =>
           wpoly_srng (dpow - 1) dpow (kvec_unflatten256 _a).[k]) /\
       (forall k, 0 <= k < j =>
        (kvec_unflatten416 encoded).[k] =
         (KArray.map (fun (p : poly) => Array416.of_list witness (BitPack p (dpow - 1) dpow))
          (lifts_wpolykvec (kvec_unflatten256 _a))).[k]));
       last first.
       + auto => /> &hr; rewrite /wpolykvec_srng allP => *;do split; 1,2: smt().
         move => i0 t00 *;rewrite tP => k kb; smt().
wp; ecall (t0_encode_polynomial (Array256.init (fun (i : int) => t0.[n * j + i]))).
auto => /> &hr ?? H H0 ?; split.
+ move : (H j{hr} _); 1:smt().
  rewrite initiE 1:/# /= /wpoly_srng !allP /= => Hbnd ii iib /=.
  rewrite initiE 1:/# /=.
  move : (Hbnd ii iib).
  by rewrite get_of_list // nth_sub //. 
move => ? rr Hrr;do split;1,2:smt().
move => k kbl kbh.
case(0<=k<j{hr}) => *.
+ have -> : 
   ((kvec_unflatten416
   (Array2496.init
      (fun (i : int) => if j{hr} * 416 <= i < j{hr} * 416 + 416 then rr.[i - j{hr} * 416] else encoded{hr}.[i]))).[k] = (kvec_unflatten416 encoded{hr}).[k]); last by smt().
  rewrite initiE 1:/# /= initiE 1:/# /= tP =>  ii iib.
  by rewrite !get_of_list // !nth_sub // initiE 1:/# /= ifF 1:/#.
have -> : k = j{hr} by smt().
+ have -> : (
   ((kvec_unflatten416
   (Array2496.init
      (fun (i : int) => if j{hr} * 416 <= i < j{hr} * 416 + 416 then rr.[i - j{hr} * 416] else encoded{hr}.[i]))).[j{hr}]  =
    rr)); last first.
  + have <-:= (Array416.to_listK witness rr).
    rewrite Hrr mapiE 1:/# /=; congr;congr;rewrite  mapiE 1:/# /= initiE 1:/# /=;congr;rewrite tP => ??;rewrite get_of_list 1:/# /= initiE 1:/# /= nth_sub /#.
    rewrite initiE 1:/# /= tP => i ib.
by rewrite get_of_list // nth_sub // initiE 1:/# /= /#. 
qed.

lemma t0_encode_ll : islossless  M.t0____encode.
proof.
proc => /=.
inline *;while (0<=j<=6) (6-j);auto; last by smt().
unroll for 28;wp.
conseq(_: _ ==> true);1:smt().
while (0 <= input_offset <=  n * 32 %/ 8 - 32 /\ input_offset %% 32 = 0) (n * 32 %/ 8 - 32 - input_offset); auto => /> /#.
qed.

lemma t0_encode_ph _a  :
    phoare [ M.t0____encode : 
       t0 = _a /\
       wpolykvec_srng (kvec_unflatten256 _a) (dpow - 1) dpow 
     ==>
      kvec_unflatten416 res = 
           KArray.map (fun p => (Array416.of_list witness (BitPack p (dpow-1) dpow))) (lifts_wpolykvec (kvec_unflatten256 _a)) ] = 1%r by conseq t0_encode_ll (t0_encode _a).
