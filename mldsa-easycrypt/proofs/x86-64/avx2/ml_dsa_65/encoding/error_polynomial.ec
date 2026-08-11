require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import CircuitBindings Bindings JWordExtra.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.
from JazzEC require import Array256 Array128.
from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.
import BitEncoding BitChunking.

import Round ZModQ Zq.

from CryptoSpecs require import JWord_extra EclibExtra JWordList.

require import XArray256 XArray128 XWord4 ArrayExtra.

lemma truncateu_32_4E (w : W32.t) : BS_W32_W4_U.truncateu4 w = W4.bits2w (take 4 (W32.w2bits w)).
proof.
rewrite /truncateu4 W4.of_intE W32.to_uintE BS2Int.bs2int_mod //;congr.
have {1}-> : 4 = size (take 4 (w2bits w)) by rewrite size_take //.
by rewrite BS2Int.bs2intK.
qed.

lemma to_sint_uint_rng_pos_4(xx : W4.t) :
    0 <= to_sint xx  <=> 0 <= to_uint xx < 8.
 have /= Hxx := W4.to_uint_cmp xx.
 rewrite /to_sint /smod /= /#.
qed.

lemma to_sint_uint_rng_neg_4(xx : W4.t) :
    to_sint xx < 0  <=> 8 <= to_uint xx < 16.
 have /= Hxx := W4.to_uint_cmp xx.
 rewrite /to_sint /smod /= /#.
qed.

(* Circuit spec *)

lemma ilog_Eta : ilog 2 (Eta + Eta) = 3 by rewrite mldsa65_Eta /=.

op error_polynomial_encode_lane(c : W32.t) : W4.t =
    BS_W32_W4_U.truncateu4 ((W32.of_int 4) + (-c)).

op valid_eta_bytes (a : W8.t Array128.t) =
    forall i, 0 <= i < 256 =>
     to_uint (W4.init (fun j => a.[(4*i+j) %/ 8].[(4*i+j) %% 8])) <= 2*Eta.

lemma BitPack_liftE (p : wpoly) :
  wpoly_srng Eta Eta p =>
    BitPack (lifts_wpoly p) Eta Eta
  = to_list (let mapped = BSWA_256u4.init (fun i => error_polynomial_encode_lane p.[i]) in
             BSWA_128u8.init (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 4].[(i*8+j) %% 4]))).
proof.
have Eta_val := mldsa65_Eta.
move=> h @/BitPack; (pose l := ilog 2 _) => /=.
have Hlog := ilog_Eta.
have ? : size
  (flatten (map (fun (x : W32.t) => IntegerToBits (Eta - crepr (incoeff (to_sint x))) (l + 1)) (to_list p))) = 256*4.
+  rewrite  (size_flatten_ctt (l+1)).
  +  by move => x; rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite  /IntegerToBits BS2Int.size_int2bs /#.
  by rewrite size_map /= size_to_list  /l /= Hlog //=.

rewrite /BitsToBytes !array256_mapE /=.
rewrite  -map_comp &(eq_sym) -map_comp /(\o) /=.
apply (eq_from_nth witness);1: by rewrite size_to_list /= size_map size_iota /#.
move => i; rewrite size_to_list => Hi.
rewrite get_to_list (nth_map witness) /=; 1: by rewrite size_iota /#.
rewrite wordP => j jb.
rewrite !initiE //= initiE 1:/# /= get_bits2w // nth_take // 1:/# nth_drop;2: by smt().
+ rewrite nth_iota /#.
rewrite (nth_flatten false (l+1)).
+ by rewrite allP => x;rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs /#.
rewrite nth_iota 1:/#  (nth_map witness) /=; 1: by rewrite size_to_list /= /#.
rewrite /error_polynomial_encode_lane .
pose v:=p.[(i * 8 + j) %/ 4].
have -> : p.[(8 * i + j) %/ (l + 1)] = v by smt().
move: h => @/wpoly_srng /array256_allP /(_ v _) //= /=.
+ rewrite /to_list /mkseq mapP; exists ((i * 8 + j) %/ 4); smt(mem_iota).
move => h.
rewrite incoeffK_centered 1,2:/# truncateu_32_4E get_bits2w 1:/#.
rewrite nth_take 1,2:/# w2bits_int2bsE.
have  -> := BS2Int.int2bs_cat 4 32 (to_uint (W32.of_int 4 - v)) _;1:smt().
rewrite /IntegerToBits nth_cat ifT;1: by rewrite BS2Int.size_int2bs /#.
congr;2:smt().
congr;1:smt().
have := (W32.of_uintK (Eta- to_sint v)).
rewrite modz_small;1:by smt().
move => <-; rewrite -W32.of_intD';congr.
rewrite W32.of_intN;congr;1:smt().
rewrite /to_sint /smod /=.
case (2147483648 <= to_uint v) => ?;last by smt(W32.to_uintK pow2_32).
move : h; rewrite /to_sint /smod ifT //= => ?.
congr;rewrite to_uint_eq /= of_uintK /=;smt(W32.to_uint_cmp pow2_32).
qed.

require import WArray1024 WArray128.

lemma error_polynomial_encode _a :
   hoare [ M.error_polynomial__encode :
       polynomial = _a /\ wpoly_srng 4 4 _a
     ==>
       to_list res = BitPack (lifts_wpoly _a) Eta Eta
       /\ valid_eta_bytes res
   ].
have Eta_val := mldsa65_Eta.
proc;inline * => /=.
proc change 1 : { temp <- W64.of_int 4097;}; 1: by auto.
proc change 2 : { shift <- zeroextu256 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu256E zeroextu256E.
  rewrite wordP => i ib.
  rewrite pack2E pack2E pack4E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?; 1: by rewrite ifT 1:/# initiE 1:/# /= get_of_list /#.
  case (i %/ 128 = 0) => ?; 2: by auto.
  rewrite initiE 1:/# /= get_of_list 1:/#.
  by have -> /= : (i %% 128 %/ 64) = 1 by smt().
proc change 5 : { eta_0 <- zeroextu256 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu256E zeroextu256E.
  rewrite wordP => i ib.
  rewrite pack2E pack2E pack4E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?; 1: by rewrite ifT 1:/# initiE 1:/# /= get_of_list /#.
  case (i %/ 128 = 0) => ?; 2: by auto.
  rewrite initiE 1:/# /= get_of_list 1:/#.
  by have -> /= : (i %% 128 %/ 64) = 1 by smt().

proc change ^while.1 : { c0 <- if (0 <= input_offset*8 <= 32*256-256)
                                then BSWAS_256u32_256.sliceget polynomial (input_offset*8)
                                else get256_direct (WArray1024.init32 (fun (i_0 : int) => polynomial.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.4 : { c1 <- if (0 <= input_offset*8 <= 32*256-256)
                                then BSWAS_256u32_256.sliceget polynomial (input_offset*8)
                                else get256_direct (WArray1024.init32 (fun (i_0 : int) => polynomial.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.7 : { c2 <- if (0 <= input_offset*8 <= 32*256-256)
                                then BSWAS_256u32_256.sliceget polynomial (input_offset*8)
                                else get256_direct (WArray1024.init32 (fun (i_0 : int) => polynomial.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.10 : { c3 <- if (0 <= input_offset*8 <= 32*256-256)
                                 then BSWAS_256u32_256.sliceget polynomial (input_offset*8)
                                 else get256_direct (WArray1024.init32 (fun (i_0 : int) => polynomial.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.13 : { c4 <- if (0 <= input_offset*8 <= 32*256-256)
                                 then BSWAS_256u32_256.sliceget polynomial (input_offset*8)
                                 else get256_direct (WArray1024.init32 (fun (i_0 : int) => polynomial.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.16 : { c5 <- if (0 <= input_offset*8 <= 32*256-256)
                                 then BSWAS_256u32_256.sliceget polynomial (input_offset*8)
                                 else get256_direct (WArray1024.init32 (fun (i_0 : int) => polynomial.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.19 : { c6 <- if (0 <= input_offset*8 <= 32*256-256)
                                 then BSWAS_256u32_256.sliceget polynomial (input_offset*8)
                                 else get256_direct (WArray1024.init32 (fun (i_0 : int) => polynomial.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.
proc change ^while.22 : { c7 <- if (0 <= input_offset*8 <= 32*256-256)
                                 then BSWAS_256u32_256.sliceget polynomial (input_offset*8)
                                 else get256_direct (WArray1024.init32 (fun (i_0 : int) => polynomial.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.

proc change ^while.36 : {encoded <- if (0 <= output_offset*8 <= 8*128-256)
                                     then BSWAS_128u8_256.sliceset encoded (output_offset*8) c0
                                     else Array128.init (get8 (set256_direct (WArray128.init8 (fun (i_0 : int) => encoded.[i_0])) output_offset c0));}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 768); last by auto.
                 by move => ?; rewrite BSWAS_128u8_256_slicesetE /#.

unroll for ^while.
cfold 8.
wp -2.
conseq (:
  List.all (fun i =>
    W32.of_int (-4) \sle _a.[i] /\ _a.[i] \sle W32.of_int 4) (iotared 0 256)
  /\ _a = polynomial  ==>
  (List.all (fun i => (W4.init (fun j => encoded.[(4*i+j) %/ 8].[(4*i+j) %% 8])) \ule W4.of_int 8) (iotared 0 256)) /\
  encoded = let mapped = BSWA_256u4.init (fun i => error_polynomial_encode_lane _a.[i]) in
  BSWA_128u8.init (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 4].[(i*8+j) %% 4])));last by circuit. 

+ move => &hr [<- +]; rewrite iotaredE /wpoly_srng allP /= => Hrng.
  rewrite /(\sle) allP => x; rewrite mem_iota /= => Hx.
  by rewrite !of_sintK /= /smod /= /#. 

+ move => &hr [<- Hrng] encoded; rewrite iotaredE allP /= => [# H1 H2].
  split; 1: by rewrite H2 BitPack_liftE /#.
  rewrite /valid_eta_bytes => k kb.
  have := H1 k _; 1: by smt(mem_iota).
  by rewrite /(\ule) /= mldsa65_Eta /=.
qed.

op error_polynomial_decode_lane(c : W4.t) : W32.t =
    ((W32.of_int 4) + (-(BS_W32_W4_U.zeroextu32 c))).

lemma BitUnack_liftE (bytes : W8.t Array128.t) :
    BitUnpack (to_list bytes) Eta Eta
  =
  (map (fun (w : W32.t) => incoeff (to_sint w))
     (BSWA_256u32.init
        (fun (i : int) =>
           error_polynomial_decode_lane
             (W4.init (fun (j : int) => bytes.[(4 * i + j) %/ 8].[(4 * i + j) %% 8]))))).
proof.
have Eta_val := mldsa65_Eta.
move=>  @/BitUnpack /=; rewrite tP => i ib.
rewrite initiE 1:// mapiE //= initiE 1:/# /=.
pose l1 := List.map _ _.
have sl1 : size l1 = n.
+   rewrite /l1;rewrite !size_map size_iota ilog_Eta /= /BytesToBits.
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
rewrite (nth_map []) /=.
+ rewrite size_chunk ilog_Eta //=.
  rewrite /BytesToBits.
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
congr; rewrite  /error_polynomial_decode_lane.
rewrite ilog_Eta /= /zeroextu32.
rewrite nth_chunk // 1:/#.
+ rewrite /BytesToBits.
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
have  := BS2Int.bs2int_le2Xs ((take 4 (drop (4 * i) (BytesToBits (to_list bytes))))).
+ rewrite size_take // size_drop 1:/# /max /= (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite !size_map !size_iota /max /=.
  pose ll := if _ then _ else _.
  have -> /= : ll = 4;1: by smt().
rewrite /BitsToInteger .
pose p := BS2Int.bs2int  (take 4 (drop (4 * i) (BytesToBits (to_list bytes)))) .
move => ?.
have ? : 0 <= p by smt(BS2Int.bs2int_ge0).
have <- : p = to_uint (W4.init (fun (j : int) => bytes.[(4 * i + j) %/ 8].[(4 * i + j) %% 8])); last by have /= :=  W32.to_sintK_small (4 - p); smt().
rewrite /to_uint /p;congr.
apply (eq_from_nth false).
+ rewrite size_take // size_drop 1:/# size_w2bits /BytesToBits.
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
move => k kb.
have ? : size (take 4 (drop (4 * i) (BytesToBits (to_list bytes)))) = 4.
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


lemma error_polynomial_decode _a :
   hoare [ M.error_polynomial__decode :
       encoded = _a /\ valid_eta_bytes _a
     ==>
       lifts_wpoly res = BitUnpack (to_list _a) Eta Eta
       /\ wpoly_srng Eta Eta res
   ].
proc => /=.
proc change 1 : { temp <- W64.of_int 15;}; 1: by auto.
proc change 2 : { mask <- zeroextu256 temp; }.
+ auto => &1 &2 [#??->]; rewrite /VMOV_64 zeroextu256E zeroextu256E.
  rewrite wordP => i ib.
  rewrite pack2E pack2E pack4E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?; 1: by rewrite ifT 1:/# initiE 1:/# /= get_of_list /#.
  case (i %/ 128 = 0) => ?; 2: by auto.
  rewrite initiE 1:/# /= get_of_list 1:/#.
  by have -> /= : (i %% 128 %/ 64) = 1 by smt().
proc change 5 : { eta_0 <- zeroextu256 temp; }.
+ auto => &1 &2 [# ??->]; rewrite /VMOV_64 zeroextu256E zeroextu256E.
  rewrite wordP => i ib.
  rewrite pack2E pack2E pack4E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?; 1: by rewrite ifT 1:/# initiE 1:/# /= get_of_list /#.
  case (i %/ 128 = 0) => ?; 2: by auto.
  rewrite initiE 1:/# /= get_of_list 1:/#.
  by have -> /= : (i %% 128 %/ 64) = 1 by smt().
proc change ^while.1 : { bytes <- if (0 <= input_offset*8 <= 8*128-128)
                                   then BSWAS_128u8_128.sliceget encoded (input_offset*8)
                                   else get128_direct (WArray128.init8 (fun (i_0 : int) => encoded.[i_0])) input_offset ;}.
                + auto => /> &2.
                  case (0 <= input_offset{2} * 8 <= 896); last by auto.
                  by move => ?; rewrite -BSWAS_128u8_128_slicegetE /#.
proc change ^while.^while.7 : {decoded <- if (0 <= output_offset*8 <= 32*256-256)
                                            then BSWAS_256u32_256.sliceset decoded (output_offset*8) coefficients
                                            else Array256.init (get32 (set256_direct (WArray1024.init32 (fun (i_0 : int) => decoded.[i_0])) output_offset coefficients));}.
               + auto => /> &2.
                 case (0 <= output_offset{2} * 8 <= 7936); last by auto.
                 by move => ?; rewrite BSWAS_256u32_256_slicesetE /#.

swap 10 1.
unroll for ^while.
do 8!(unroll for ^while).


cfold 10.
do 8!(cfold ^byte_group<-).
wp -3.


conseq (_: encoded = _a /\
    List.all (fun i => (W4.init (fun j => encoded.[(4*i+j) %/ 8].[(4*i+j) %% 8])) \ule W4.of_int 8) (iotared 0 256)
        ==>
    List.all (fun i =>
    W32.of_int (-4) \sle decoded.[i] /\ decoded.[i] \sle W32.of_int 4) (iotared 0 256) /\
    decoded = BSWA_256u32.init (fun i => error_polynomial_decode_lane (W4.init (fun j =>
               _a.[(4*i+j) %/ 8].[(4*i+j) %% 8])))); last by simplify;circuit.

+ move => &hr; rewrite iotaredE /valid_eta_bytes mldsa65_Eta /= => [#-> H] /=.
  by rewrite allP => k; rewrite mem_iota /= /(\ule) /=  => ?; rewrite H /#. 
               
move=> &hr [# <- Hvalid decoded [H Hdecoded]]; split.

- (* Part 1: lifts_wpoly = BitUnpack *)
  rewrite /lifts_wpoly /=; apply (inj_eq Array256.to_list Array256.to_list_inj).
  by rewrite Hdecoded BitUnack_liftE ~-1:// !array256_mapE; do 2!congr => //.
- (* Part 2: wpoly_srng Eta Eta res *)
  rewrite /wpoly_srng allP mldsa65_Eta => w Hw /=.
  have := H; rewrite iotaredE allP => HH; have /= := HH w _; 1: by smt(mem_iota).
  by rewrite /(\sle) /= !of_sintK /smod /= /#.
qed.
