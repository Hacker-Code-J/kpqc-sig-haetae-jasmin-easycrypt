require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import CircuitBindings Bindings JWordExtra.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.
from JazzEC require import Array256 Array128.
from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.
import BitEncoding BitChunking.

import Round ZModQ Zq.

require import ArrayExtra.
from CryptoSpecs require import JWord_extra EclibExtra JWordList.

require import XArray256 XArray128 XWord4.

lemma truncateu_32_4E (w : W32.t) : BS_W32_W4_U.truncateu4 w = W4.bits2w (take 4 (W32.w2bits w)).
proof.
rewrite /truncateu4 W4.of_intE W32.to_uintE BS2Int.bs2int_mod //;congr.
have {1}-> : 4 = size (take 4 (w2bits w)) by rewrite size_take //.
by rewrite BS2Int.bs2intK.
qed.

op b_w1 = 15. (* 2^w1_bits - 1 *)
lemma ilog_b_w1 : ilog 2 b_w1 = w1_bits - 1 by rewrite /b_w1 /=.

(* Circuit spec  *)

op commitment_encode_polynomial_lane(c : W32.t) : W4.t =
    BS_W32_W4_U.truncateu4  c.


(* Pre relaxed from `wpoly_urng b_w1 p` (< 15) to `wpoly_urng (b_w1+1) p` (< 16) to *)
(* match the tight output of polynomial__use_hints. SimpleBitPack with b=15 uses   *)
(* 4-bit int2bs, which correctly encodes all of [0..15].                           *)
lemma SimpleBitPack_liftE (p : wpoly) :
  wpoly_urng (b_w1 + 1) p =>
    SimpleBitPack (liftu_wpoly p) b_w1
  = to_list
  (BSWA_128u8.init
     (fun (i0 : int) =>
        W8.init
          (fun (j : int) =>
             (BSWA_256u4.init (fun (i1 : int) => commitment_encode_polynomial_lane p.[i1])).[(i0 * 8 + j) %/ 4].[
             (i0 * 8 + j) %% 4]))).
proof.
move=> h @/SimpleBitPack; (pose l := ilog 2 _) => /=.
have := ilog_b_w1; rewrite /= => ?.
have ? : size
   (flatten (map (fun (x : W32.t) => IntegerToBits (asint (incoeff (to_uint x))) (l + 1)) (to_list p))) = 256*4.
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
rewrite /commitment_encode_polynomial_lane .
pose v:=p.[(i * 8 + j) %/ 4].
have -> : p.[(8 * i + j) %/ (l + 1)] = v by smt().
move: h => @/wpoly_urng /array256_allP /(_ v _) //= /=.
+ rewrite /to_list /mkseq mapP; exists ((i * 8 + j) %/ 4); smt(mem_iota).
move => h.
rewrite incoeffK truncateu_32_4E get_bits2w 1:/#.
rewrite nth_take 1,2:/#.
rewrite /IntegerToBits w2bits_int2bsE /l ilog_b_w1 /= (modz_small _ q) 1:/# /BS2Int.int2bs.
by rewrite !nth_mkseq 1,2:/# /= /#.
qed.

require import WArray1024 WArray128.

(* Pre relaxed from `wpoly_urng b_w1 _a` (values < 15) to                          *)
(* `wpoly_urng (b_w1+1) _a` (values < 16). The encoding uses 4-bit truncation      *)
(* (VPMADDUBSW after truncateu4) which handles the full [0..15] range, so the      *)
(* looser pre still suffices; this matches polynomial__use_hints's tight output    *)
(* bound (4-bit-masked impl, [0..15]).                                             *)
lemma commitment_encode_polynomial _a :
   hoare [ M.commitment____encode_polynomial :
       commitment = _a /\ wpoly_urng (b_w1 + 1) _a
     ==>
       to_list res = SimpleBitPack (liftu_wpoly _a) b_w1
   ].
proc => /=;inline *.
proc change 1 : { temp <- W64.of_int 4097;}; 1: by auto.
proc change 2 : { shift <- zeroextu256 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu256E zeroextu256E.
  rewrite wordP => i ib.
  rewrite pack2E pack2E pack4E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?; 1: by rewrite ifT 1:/# initiE 1:/# /= get_of_list /#.
  case (i %/ 128 = 0) => ?; 2: by auto.
  rewrite initiE 1:/# /= get_of_list 1:/#.
  by have -> /= : (i %% 128 %/ 64) = 1 by smt().

proc change ^while.1 : { c0 <- if (0 <= input_offset*8 <= 32*256-256)
                                then BSWAS_256u32_256.sliceget commitment (input_offset*8)
                                else get256_direct (WArray1024.init32 (fun (i_0 : int) => commitment.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.3 : { c1 <- if (0 <= input_offset*8 <= 32*256-256)
                                then BSWAS_256u32_256.sliceget commitment (input_offset*8)
                                else get256_direct (WArray1024.init32 (fun (i_0 : int) => commitment.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.5 : { c2 <- if (0 <= input_offset*8 <= 32*256-256)
                                then BSWAS_256u32_256.sliceget commitment (input_offset*8)
                                else get256_direct (WArray1024.init32 (fun (i_0 : int) => commitment.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.7 : { c3 <- if (0 <= input_offset*8 <= 32*256-256)
                                then BSWAS_256u32_256.sliceget commitment (input_offset*8)
                                else get256_direct (WArray1024.init32 (fun (i_0 : int) => commitment.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.9 : { c4 <- if (0 <= input_offset*8 <= 32*256-256)
                                then BSWAS_256u32_256.sliceget commitment (input_offset*8)
                                else get256_direct (WArray1024.init32 (fun (i_0 : int) => commitment.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.11 : { c5 <- if (0 <= input_offset*8 <= 32*256-256)
                                 then BSWAS_256u32_256.sliceget commitment (input_offset*8)
                                 else get256_direct (WArray1024.init32 (fun (i_0 : int) => commitment.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.13 : { c6 <- if (0 <= input_offset*8 <= 32*256-256)
                                 then BSWAS_256u32_256.sliceget commitment (input_offset*8)
                                 else get256_direct (WArray1024.init32 (fun (i_0 : int) => commitment.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.15 : { c7 <- if (0 <= input_offset*8 <= 32*256-256)
                                 then BSWAS_256u32_256.sliceget commitment (input_offset*8)
                                 else get256_direct (WArray1024.init32 (fun (i_0 : int) => commitment.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.

proc change ^while.28 : {encoded <- if (0 <= output_offset*8 <= 8*128-256)
                                     then BSWAS_128u8_256.sliceset encoded (output_offset*8) c0
                                     else Array128.init (get8 (set256_direct (WArray128.init8 (fun (i_0 : int) => encoded.[i_0])) output_offset c0));}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 768); last by auto.
                 by move => ?; rewrite BSWAS_128u8_256_slicesetE /#.

unroll for ^while.
cfold 5.
wp -2.

conseq (:  commitment = BSWA_256u32.init (fun i => BS_W32_W4_U.zeroextu32 (BS_W32_W4_U.truncateu4 _a.[i])) ==>
    encoded  = let mapped = BSWA_256u4.init (fun i => commitment_encode_polynomial_lane _a.[i]) in
    BSWA_128u8.init (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 4].[(i*8+j) %% 4]))); last by circuit.

+ move => &hr [->+]; rewrite /wpoly_urng allP => ?.
  by rewrite tP => k kb; rewrite initiE 1:/# /= /zeroextu32 /truncateu4 /= of_uintK /= modz_small 1:/# to_uintK.
+ by move => &hr [<- Hrng] ? /= => ->;rewrite SimpleBitPack_liftE //=.

qed.

lemma commitment____encode_polynomial_ll : islossless M.commitment____encode_polynomial.
proof.
proc; wp.
while (true) ((4 * 256) %/ 8 - output_offset); last by auto => /#.
by move => *; auto => /#.
qed.

import VecMat PolyKVec.

require import Array768 Array1536.

(* Pre relaxed from `wpolykvec_urng _ b_w1` (< 15) to `_ (b_w1+1)` (< 16) to match  *)
(* the tight output bound of polynomial__use_hints (4-bit-masked impl, [0..15]).   *)
lemma commitment_encode _a :
    hoare [ M.commitment____encode :
       commitment = _a /\ wpolykvec_urng (kvec_unflatten256 _a) (b_w1 + 1)
     ==>
       kvec_unflatten128 res =
           KArray.map (fun (p : poly) => Array128.of_list witness (SimpleBitPack  p b_w1)) (liftu_wpolykvec (kvec_unflatten256 _a))
   ].
have Hkvec := mldsa65_kvec.
proc => /=.
while (0 <= i <= 6 /\ commitment = _a /\ wpolykvec_urng (kvec_unflatten256 _a) (b_w1 + 1)  /\
       forall k, 0 <= k < i =>
       (kvec_unflatten128 encoded_commitment).[k] =
       (map (fun (p : poly) => Array128.of_list witness (SimpleBitPack  p b_w1)) (liftu_wpolykvec (kvec_unflatten256 _a))).[k]);
       last first.
       + auto => /> &hr *;do split;1: smt().
         move => r0 j0 *;rewrite tP => k kb; smt().
wp; ecall (commitment_encode_polynomial (Array256.init (fun (i_0 : int) => _a.[i * 256 + i_0]))).
auto => /> &hr ?? Hrng H ?;do split.
+ move : Hrng; rewrite /wpolykvec_urng /wpoly_urng !allP /=  => Hrng ii iib.
  have := Hrng i{hr} _; 1:smt().
  rewrite allP /= initiE 1:/# /= => Hrngj.
  have := Hrngj ii _; 1:smt().
  rewrite initiE 1:/# /= initiE 1:/# /= nth_sub 1:/# /#.
move => ? rr Hrr; do split;1,2: smt().
move => k kbl kbh.
case(0<=k<i{hr}) => *.
+
   have -> : (kvec_unflatten128
   (Array768.init
      (fun (ii : int) => if i{hr} * 128 <= ii < i{hr} * 128 + 128 then rr.[ii - i{hr} * 128] else encoded_commitment{hr}.[ii]))).[k] =
    ((kvec_unflatten128 encoded_commitment{hr})).[k]; last by smt().
  rewrite !initiE 1..2:/# /= /of_list /= tP => kk kkb.
  rewrite !initiE 1,2:/# !nth_sub 1,2:/# initiE 1:/# /= /#.
have -> : k = i{hr} by smt().
+ have -> :
   (kvec_unflatten128
   (Array768.init
      (fun (ii : int) => if i{hr} * 128 <= ii < i{hr} * 128 + 128 then rr.[ii - i{hr} * 128] else encoded_commitment{hr}.[ii]))).[i{hr}]  =
    (rr); last first.
  + have <- := Array128.to_listK witness rr;rewrite Hrr mapiE 1:/# /=;congr;congr.
    rewrite /liftu_wpolykvec mapiE 1:/#;congr;rewrite initiE 1:/# /=.
    rewrite tP => kk kkb; rewrite !initiE 1,2:/# /= nth_sub /#.

rewrite initiE 1:/# /= tP => ii iib.
rewrite  initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
qed.

lemma commitment____encode_ll : islossless M.commitment____encode.
proof.
proc.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *; wp; call commitment____encode_polynomial_ll; auto => /#.
qed.

(* Phoare variant of commitment_encode, composing the hoare post with
   losslessness. Used via ecall{2} in the seq 3 3 bridge of
   ml_dsa_65_sign_correct (sign.ec). *)
phoare commitment_encode_ph _a :
 [ M.commitment____encode :
    commitment = _a /\ wpolykvec_urng (kvec_unflatten256 _a) (b_w1 + 1)
  ==>
    kvec_unflatten128 res =
      KArray.map
        (fun (p : poly) => Array128.of_list witness (SimpleBitPack p b_w1))
        (liftu_wpolykvec (kvec_unflatten256 _a))
 ] = 1%r.
proof. by conseq commitment____encode_ll (commitment_encode _a). qed.
