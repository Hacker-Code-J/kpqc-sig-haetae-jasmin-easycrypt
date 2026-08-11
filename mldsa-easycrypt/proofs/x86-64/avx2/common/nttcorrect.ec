(**
  This theory connects the extracted implementation code to the
  machine-level specification of the NTT.
*)

(* -------------------------------------------------------------------- *)
require import AllCore CoreUtils List Ring IntDiv BitEncoding.
require import StdRing StdOrder.

import BitChunking.

(* -------------------------------------------------------------------- *)
from Jasmin require import JWord JArray.

require import JArrayExtra.
require import CircuitBindings.

(* -------------------------------------------------------------------- *)
from Jasmin require import JModel_x86.
from JazzEC require import Ml_dsa_65_avx2.

(* -------------------------------------------------------------------- *)
require import WArray1024.
require import Array4 Array8 Array16 Array256.
require import XArray256.

(* -------------------------------------------------------------------- *)
type wpoly = W32.t Array256.t.

(* -------------------------------------------------------------------- *)
require import Nttzetas Nttspec Nttlogspec.

(* ==================================================================== *)
lemma truncateu32_64E (w : W64.t) : truncateu32 w = w \bits32 0.
proof.
apply: W32.ext_eq=> i rgi; rewrite bits32iE //=.
rewrite /truncateu32 of_intwE rgi /= /W32.int_bit.
rewrite modz_pow2_div ~-1://# modz_dvd.
- by rewrite -{1}[2]expr1 dvdz_exp2l /#.
- by rewrite -b2i_get /#.
qed.

hint simplify truncateu32_64E.

(* -------------------------------------------------------------------- *)
lemma truncateu32_256E (w : W256.t) : truncateu32 w = w \bits32 0.
proof.
apply: W32.ext_eq=> i rgi; rewrite bits32iE //=.
rewrite /truncateu32 of_intwE rgi /= /W32.int_bit.
rewrite modz_pow2_div ~-1://# modz_dvd.
- by rewrite -{1}[2]expr1 dvdz_exp2l /#.
- by rewrite -b2i_get /#.
qed.

hint simplify truncateu32_256E.

(* -------------------------------------------------------------------- *)
lemma truncateu128_256E (w : W256.t) : truncateu128 w = w \bits128 0.
proof.
apply: W128.ext_eq=> i rgi; rewrite bits128iE //=.
rewrite of_intwE rgi /= /W128.int_bit.
rewrite modz_pow2_div ~-1://# modz_dvd.
- by rewrite -{1}[2]expr1 dvdz_exp2l /#.
- by rewrite -b2i_get /#.
qed.

hint simplify truncateu128_256E.

(* ==================================================================== *)
lemma VMOV_32 (w : W32.t) : VMOV_32 w = pack4 [w; zero; zero; zero].
proof. done. qed.

hint simplify VMOV_32.

(* -------------------------------------------------------------------- *)
lemma zeroextu256E (w : W128.t) : zeroextu256 w = pack2 [w; zero].
proof.
rewrite zeroextu256E &(wordP) => i rgi /=.
by rewrite !pack2bE //= of_listE !initiE.
qed.

hint simplify zeroextu256E.

(* -------------------------------------------------------------------- *)
lemma VPBROADCAST_8u32E (w : W32.t) :
  VPBROADCAST_8u32 w = pack8 [w; w; w; w; w; w; w; w].
proof. by rewrite /VPBROADCAST_8u32 -iotaredE. qed.

hint simplify VPBROADCAST_8u32E.

(* -------------------------------------------------------------------- *)
lemma VPADD_8u32E (u w : W256.t) :
    VPADD_8u32 u w
  = W8u32.pack8 [
      (u \bits32 0) + (w \bits32 0); (u \bits32 1) + (w \bits32 1);
      (u \bits32 2) + (w \bits32 2); (u \bits32 3) + (w \bits32 3);
      (u \bits32 4) + (w \bits32 4); (u \bits32 5) + (w \bits32 5);
      (u \bits32 6) + (w \bits32 6); (u \bits32 7) + (w \bits32 7)
    ].
proof. by cbv delta. qed.

hint simplify VPADD_8u32E.

(* -------------------------------------------------------------------- *)
lemma VPSUB_4u64E (u w : W256.t) :
    VPSUB_4u64 u w
  = W4u64.pack4 [
      (u \bits64 0) - (w \bits64 0); (u \bits64 1) - (w \bits64 1);
      (u \bits64 2) - (w \bits64 2); (u \bits64 3) - (w \bits64 3)
    ].
proof. by cbv delta. qed.

hint simplify VPSUB_4u64E.

(* -------------------------------------------------------------------- *)
lemma VPSUB_8u32E (u w : W256.t) :
    VPSUB_8u32 u w
  = W8u32.pack8 [
      (u \bits32 0) - (w \bits32 0); (u \bits32 1) - (w \bits32 1);
      (u \bits32 2) - (w \bits32 2); (u \bits32 3) - (w \bits32 3);
      (u \bits32 4) - (w \bits32 4); (u \bits32 5) - (w \bits32 5);
      (u \bits32 6) - (w \bits32 6); (u \bits32 7) - (w \bits32 7)
    ].
proof. by cbv delta. qed.

hint simplify VPSUB_8u32E.

(* -------------------------------------------------------------------- *)
lemma VPMUL_256 (u v : W256.t) :
    VPMUL_256 u v
  = W4u64.pack4 [
      (u \bits32 0) \sx (v \bits32 0); (u \bits32 2) \sx (v \bits32 2);
      (u \bits32 4) \sx (v \bits32 4); (u \bits32 6) \sx (v \bits32 6)
    ].
proof. by cbv delta. qed.

hint simplify VPMUL_256.

(* -------------------------------------------------------------------- *)
lemma VMOVSHDUP_256E (w : W256.t) :
    VMOVSHDUP_256 w
  = W8u32.pack8 [
      w \bits32 1; w \bits32 1; w \bits32 3; w \bits32 3;
      w \bits32 5; w \bits32 5; w \bits32 7; w \bits32 7
    ].
proof. by cbv delta. qed.

hint simplify VMOVSHDUP_256E.

(* -------------------------------------------------------------------- *)
lemma VPSHUFD_256_216E (w : W256.t) :
    VPSHUFD_256 w (W8.of_int 216)
  = W8u32.pack8 [
      w \bits32 0; w \bits32 2; w \bits32 1; w \bits32 3;
      w \bits32 4; w \bits32 6; w \bits32 5; w \bits32 7
    ].
proof. by cbv delta. qed.

hint simplify VPSHUFD_256_216E.

(* -------------------------------------------------------------------- *)
lemma VPSHUFD_128_228E (w : W128.t) : VPSHUFD_128 w (W8.of_int 228) = w.
proof.
rewrite /VPSHUFD_128 -{2}(W4u32.unpack32K w) iotaredE -/(range 0 4).
rewrite -/(mkseq _ 4) -(eq_in_mkseq (fun i => w \bits32 i)) /=.
- move=> i rgi @/VPSHUFD_128_B /=; congr.
  by move/mem_range: rgi; rewrite /range -iotaredE /= => [#|] ->.
rewrite -{2}[w](unpack32K); congr; apply/W4u32.Pack.ext_eq.
by move=> i rgi; rewrite !(get_unpack32, get_of_list, nth_mkseq).
qed.

hint simplify VPSHUFD_128_228E.

(* -------------------------------------------------------------------- *)
lemma VPSHUFD_256_228E (w : W256.t) : VPSHUFD_256 w (W8.of_int 228) = w.
proof.
rewrite /VPSHUFD_256 mapE map_to_list.
rewrite (List.eq_map _ idfun) /= 1:&(VPSHUFD_128_228E) map_id.
rewrite -{2}[w](unpack128K); congr; apply/W2u128.Pack.ext_eq.
move=> i rgi; rewrite !(get_unpack128, nth_mkseq) //.
by rewrite to_listK /unpack128 initE /= ifT.
qed.

hint simplify VPSHUFD_256_228E.

(* -------------------------------------------------------------------- *)
lemma VPSHUFD_128_245E (w : W128.t) :
    VPSHUFD_128 w (W8.of_int 245)
  = W4u32.pack4 [w \bits32 1; w \bits32 1; w \bits32 3; w \bits32 3].
proof. by cbv delta. qed.

hint simplify VPSHUFD_128_245E.

(* -------------------------------------------------------------------- *)
lemma VPSHUFD_256_245E (w : W256.t) :
    VPSHUFD_256 w (W8.of_int 245)
  = W8u32.pack8 [
      w \bits32 1; w \bits32 1; w \bits32 3; w \bits32 3;
      w \bits32 5; w \bits32 5; w \bits32 7; w \bits32 7
    ].
proof. by cbv delta. qed.

hint simplify VPSHUFD_256_245E.

(* -------------------------------------------------------------------- *)
lemma VPUNPCKL_4u64E (u v : W256.t) :
    VPUNPCKL_4u64 u v
  = W4u64.pack4 [u \bits64 0; v \bits64 0; u \bits64 2; v \bits64 2].
proof. by cbv delta. qed.

hint simplify VPUNPCKL_4u64E.

(* -------------------------------------------------------------------- *)
lemma VPUNPCKH_4u64E (u v : W256.t) :
    VPUNPCKH_4u64 u v
  = W4u64.pack4 [u \bits64 1; v \bits64 1; u \bits64 3; v \bits64 3].
proof. by cbv delta. qed.

hint simplify VPUNPCKH_4u64E.

(* -------------------------------------------------------------------- *)
lemma VPBLENDD_256_170E (u v : W256.t) :
    VPBLENDD_256 u v (W8.of_int 170)
  = pack8 [
      u \bits32 0; v \bits32 1; u \bits32 2; v \bits32 3;
      u \bits32 4; v \bits32 5; u \bits32 6; v \bits32 7
    ].
proof. by cbv delta; rewrite !of_intwE; cbv delta. qed.

hint simplify VPBLENDD_256_170E.

(* -------------------------------------------------------------------- *)
lemma VPERM2I128_19E (u v : W256.t) :
    VPERM2I128 u v (W8.of_int 19)
  = pack2 [v \bits128 1; u \bits128 1].
proof. by cbv delta; rewrite !of_intwE /=; cbv delta. qed.

hint simplify VPERM2I128_19E.

(* -------------------------------------------------------------------- *)
lemma VINSERTI128_L (u : W256.t) (w : W128.t) :
  VINSERTI128 u w W8.zero = pack2 [w; u \bits128 1].
proof. done. qed.

hint simplify VINSERTI128_L.

(* -------------------------------------------------------------------- *)
lemma VINSERTI128_R (u : W256.t) (w : W128.t) :
  VINSERTI128 u w W8.one = pack2 [u \bits128 0; w].
proof. done. qed.

hint simplify VINSERTI128_R.

(* -------------------------------------------------------------------- *)
hint simplify W8u32.Pack.of_listK.
hint simplify W8u32.Pack.to_listK.

(* -------------------------------------------------------------------- *)
lemma to_list_unpack32E (w : W256.t) :
  to_list (unpack32 w) = [
    w \bits32 0; w \bits32 1; w \bits32 2; w \bits32 3;
    w \bits32 4; w \bits32 5; w \bits32 6; w \bits32 7
  ].
proof. by rewrite /to_list /mkseq -iotaredE. qed.

hint simplify to_list_unpack32E.

(* -------------------------------------------------------------------- *)
hint simplify size_map, size_nseq.
hint simplify nth_mkseq, nth_nseq.
hint simplify flatten_cons, flatten_nil.
hint simplify cat0s, cats0.

(* ==================================================================== *)
lemma pack8K (w : W256.t) : W8u32.pack8 (mkseq (W8u32.(\bits32) w) 8) = w.
proof. 
apply/W8u32.wordP=> i rgi; rewrite pack8bE //.
by rewrite of_listE initiE //= nth_mkseq .
qed.

hint simplify pack8K.

(* -------------------------------------------------------------------- *)
lemma pack8_bits32E (w : W32.t list) (i : int) : 0 <= i < 8 =>
  (W8u32.pack8 w) \bits32 i = nth W32.zero w i.
proof.
move=> rgi; apply/W32.ext_eq=> j rgj; rewrite pack8E bits32E /= initE rgj /=.
rewrite initE ifT 1:/# /= modzMDl divzMDl // !(pdiv_small, pmod_small) //=.
by rewrite get_of_list.
qed.

hint simplify pack8_bits32E.

(* -------------------------------------------------------------------- *)
lemma pack8_eq (F G : int -> W32.t) :
     (forall i, 0 <= i < 8 => F i = G i)
  =>   pack8 [F 0; F 1; F 2; F 3; F 4; F 5; F 6; F 7]
     = pack8 [G 0; G 1; G 2; G 3; G 4; G 5; G 6; G 7].
proof. by move=> eq; rewrite !eq. qed.

(* ==================================================================== *)
abbrev MODULUS = 8380417.

(* -------------------------------------------------------------------- *)
abbrev MODULUS_8u32 =
  225935595421087293402315996791205668696012104344015382954355885915737415681.

(* -------------------------------------------------------------------- *)
op MODULUS_VECTOR : W256.t =
 W8u32.pack8 (nseq 8 (W32.of_int MODULUS)).

(* -------------------------------------------------------------------- *)
lemma MODULUS_VECTOR_E : W256.of_int MODULUS_8u32 = MODULUS_VECTOR.
proof.
have eq: forall i, 0 <= i < 8 =>
  W256.of_int MODULUS_8u32 \bits32 i = W32.of_int MODULUS.
- by move=> i /mem_range @/range; rewrite -iotaredE /= => [#|] -> /=.
apply/W8u32.wordP=> i rgi; rewrite eq 1://.
by rewrite /MODULUS_VECTOR pack8_bits32E // nth_nseq.
qed.

(* -------------------------------------------------------------------- *)
abbrev INVERSE_OF_MODULUS_MOD_MONTGOMERY_R = 58728449.

(* -------------------------------------------------------------------- *)
abbrev INVERSE_OF_MODULUS_MOD_MONTGOMERY_R_8u32 = 
  1583315853253120773718772168429862829322770379248453373268938642773050925057.

(* -------------------------------------------------------------------- *)
op INVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR : W256.t =
 W8u32.pack8 (nseq 8 (W32.of_int INVERSE_OF_MODULUS_MOD_MONTGOMERY_R)).

(* -------------------------------------------------------------------- *)
lemma INVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR_E :
    W256.of_int INVERSE_OF_MODULUS_MOD_MONTGOMERY_R_8u32
  = INVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR.
proof.
have eq: forall i, 0 <= i < 8 =>
    W256.of_int INVERSE_OF_MODULUS_MOD_MONTGOMERY_R_8u32 \bits32 i
  = W32.of_int INVERSE_OF_MODULUS_MOD_MONTGOMERY_R.
- by move=> i /mem_range @/range; rewrite -iotaredE /= => [#|] -> /=.
apply/W8u32.wordP=> i rgi; rewrite eq 1://.
rewrite /INVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR.
by rewrite pack8_bits32E // nth_nseq.
qed.

(* ==================================================================== *)
section.
(* -------------------------------------------------------------------- *)
hint simplify size_mkseq.

(* -------------------------------------------------------------------- *)
lemma wpoly_get256_aligned (p : wpoly) (s : int) :
     0 <= s < 256 - 7
  =>   WArray1024.get256_direct (WArray1024.init32 ("_.[_]" p)) (4 * s)
     = W8u32.pack8 (mkseq (fun i => p.[s + i]) 8).
proof.
move=> *; apply/W8u32.wordP=> i rgi; rewrite get_pack8 1://.
rewrite nth_mkseq //= get256E &(W32.ext_eq) => j rgj.
rewrite bits32_W32u8 ifT // pack4wE //=.
rewrite of_listE 4!initE /= !ifT ~-1:/#.
rewrite 4!initE /= !ifT ~-1:/# !addrA -mulrDr.
rewrite [4*_]mulrC modzMl !modzMDl ![_%%4]pmod_small //.
rewrite !(mulzK, divzMDl) // ![_ %/ 4]pdiv_small //.
rewrite -(W4u8.Pack.init_ext ((\bits8) p.[s + i])) 1:/#.
by rewrite initE ifT 1:/# -get_bits8.
qed.

(* -------------------------------------------------------------------- *)
lemma wpoly_get256_alignedE (p : wpoly) (s : int) :
     0 <= s %/ 4 < 256 - 7
  => s %% 4 = 0
  =>   WArray1024.get256_direct (WArray1024.init32 ("_.[_]" p)) s
     = W8u32.pack8 (mkseq (fun i => p.[s %/ 4 + i]) 8).
proof. by move=> ?; have := wpoly_get256_aligned p (s %/ 4); smt(). qed.

(* -------------------------------------------------------------------- *)
lemma wpoly_set256_aligned (s : int) (p : wpoly) (w : W256.t) :
     0 <= s < 256 - 7
  =>   Array256.init
          (fun (i : int) =>
            get32
              (set256_direct (init32 ("_.[_]" p)) (4 * s) w) i)
     = Array256.fill (fun i =>  w \bits32 (i - s)) s 8 p.
proof.
move=> ?; apply: Array256.ext_eq=> j rgj; rewrite fillE !initE rgj /=.
rewrite get32E /= &(W32.ext_eq) => k rgk; rewrite pack4wE //= initE /=.
rewrite ifT 1:/# /set256_direct WArray1024.initE /= ifT 1:/#.
have /= -> := fun_if (fun (w : W8.t) => w.[k %% 8]).
have /= -> := fun_if (fun (w : W32.t) => w.[k]).
rewrite &(if_congr) 1:/#; last first.
- rewrite initE ifT 1:/# /= [4*_]mulrC divzMDl // -divz_mul //=.
  by rewrite pdiv_small 1:// /= modzMDl modz_small 1:/# -get_bits8.
- by rewrite addrAC -mulrBr -W256_bits32_bits8 1:/# -get_bits8.
qed.

(* -------------------------------------------------------------------- *)
lemma wpoly_set256_alignedE (s : int) (p : wpoly) (w : W256.t) :
     0 <= s %/ 4 < 256 - 7
  => s %% 4 = 0
  =>   Array256.init                                                           
          (fun (i : int) =>                                                     
            get32
              (set256_direct (init32 ("_.[_]" p)) s w) i)
     = Array256.fill (fun i =>  w \bits32 (i - s %/ 4)) (s %/ 4) 8 p.
proof. by move=> ?; have := wpoly_set256_aligned (s %/ 4) p w; smt(). qed.

end section.

(* ==================================================================== *)
lemma mmrP (u v : W256.t) : hoare[M.montgomery_multiply_and_reduce :
      arg = (u, v)
    ==>
      res = W8u32.pack8_t (W8u32.Pack.map2 mmr (W8u32.unpack32 u) (W8u32.unpack32 v))
  ].
proof.
proc.
auto=> &hr [#] 2!->>.
pose uw (i : int) := u \bits32 i; pose vw (i : int) := v \bits32 i.
rewrite -[u]pack8K /= -!/~(uw _) -[v]pack8K /= -!/~(vw _).
rewrite INVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR_E MODULUS_VECTOR_E.
rewrite /INVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR /=.
rewrite /MODULUS_VECTOR //=.

pose qinv := W32.of_int INVERSE_OF_MODULUS_MOD_MONTGOMERY_R.
pose q    := W32.of_int MODULUS.

pose F    := fun k =>
    (uw k \sx vw k)
  - (uw k \sx vw k \bits32 0 \sx qinv \bits32 0 \sx q) \bits32 1.

apply: (pack8_eq F (fun i => mmr (uw i) (vw i))).
move=> i rgi @/F @/mmr /=; move: (uw i) (vw i) => w1 w2.
by rewrite -shr_shrw 1://; circuit.
qed.

(* -------------------------------------------------------------------- *)
lemma mmr_ll (u v : W256.t) : phoare[M.montgomery_multiply_and_reduce :
      arg = (u, v)
    ==>
      true
  ] = 1%r.
proof. by proc; islossless. qed.

(* -------------------------------------------------------------------- *)
lemma mmrP_ll (u v : W256.t) : phoare[M.montgomery_multiply_and_reduce :
      arg = (u, v)
    ==>
      res = W8u32.pack8_t (W8u32.Pack.map2 mmr (W8u32.unpack32 u) (W8u32.unpack32 v))
  ] = 1%r.
proof. by conseq (mmr_ll u v) (mmrP u v). qed.

(* -------------------------------------------------------------------- *)
hint simplify mkseqSr_minus, mkseq0.

(* -------------------------------------------------------------------- *)
hint simplify W64.of_uintK.

(* -------------------------------------------------------------------- *)
lemma NTT_layer0_bf (p : wpoly) (start : int) (z : W256.t) :
     0 <= start < 32
  => 2 %| start
  => hoare[M.polynomial__butterfly_2 :
         arg = (p, W64.of_int start, z)
       ==>
         res = reduce_n p (8 * start) 1 (List.map ((\bits32) z) perm0L)
     ].
proof.
move=> *; proc.
cfold ^lhs_start<-; kill ^lhs_start<-; first by auto.
cfold ^rhs_start<-; kill ^rhs_start<-; first by auto.

pose uw (i : int) := p.[8 * start + i].
pose vw (i : int) := p.[8 * start + 8 + i].
pose zw (i : int) := z \bits32 i.

swap ^rhs<- -1; seq 2 : (#pre /\
     lhs = W8u32.pack8 (mkseq uw 8)
  /\ rhs = W8u32.pack8 (mkseq vw 8)).
- hoare split; auto=> &hr |> /=.
  by rewrite !pmod_small ~-1:/# !wpoly_get256_alignedE //#.

proc change 5 : {
  zeta_products <-
    W8u32.pack8_t (W8u32.Pack.map2 mmr
      (W8u32.unpack32 zeta_products)
      (W8u32.unpack32 zetas)
    );
}.
- by ecall {1} (mmrP_ll zeta_products{1} zetas{1}); auto.

pose bf (w : int -> W32.t) (i : int) (t : int) :=
  [w i + mmr (w (i + 1)) (zw t); w i - mmr (w (i + 1)) (zw t)].
move=> /= ; seq 11 : (#{/~{lhs,rhs}}pre /\
  (  lhs = pack8 (flatten [bf uw 0 0; bf uw 2 1; bf uw 4 4; bf uw 6 5])
  /\ rhs = pack8 (flatten [bf vw 0 2; bf vw 2 3; bf vw 4 6; bf vw 6 7]))).
- by hoare split; [auto=> &hr ||> | auto=> &hr ||> ->].

seq 2: (#{/~{polynomial}}pre /\ polynomial =
  let p = replace_ p (8 * start    ) (to_list lhs) in
  let p = replace_ p (8 * start + 8) (to_list rhs) in
  p
).
- hoare split; [wp; skip=> &hr [#] <<- ->> 3?| by auto].
  rewrite (replace_mkseq ((\bits32) lhs{hr}) _ _ 8) /=.
  rewrite (replace_mkseq ((\bits32) rhs{hr}) _ _ 8) /=.
  rewrite !(of_uintK, pmod_small) ~-1:/#.
  rewrite !wpoly_set256_alignedE ~-1:/#.
  by rewrite &(fill_congr) ~-1:/# &(fill_congr) ~-1:/#.

skip=> &hr [#] _ _ lE rE;
  pose l := W8u32.to_list lhs{hr};
  pose r := W8u32.to_list rhs{hr};
  move=> /=.
rewrite -replace_cat reduce_nE 1:/# => -> /=; congr.
rewrite /perm0L /= /reduce_coeff /=.
by rewrite /l lE /r rE /= !catA /bf /=.
qed.

(* -------------------------------------------------------------------- *)
lemma polynomial__ntt_at_layer_0P (p_ : wpoly) :
  hoare[M.polynomial__ntt_at_layer_0 :
    polynomial = p_ ==> res = reduce_level p_ 0].
proof.
proc; sp; while (
     0 <= i <= 16
  /\ polynomial = reduce_n p_ 0 1 (take (8 * i) (map W32.of_int (zetaL 0)))
); last first.
- auto=> &hr |>; rewrite take0 /= reduce_0 /=.
  move=> j *; have ->> /=: j = 16 by smt().
  by rewrite take_oversize.

proc rewrite 2 LAYER_0_ZETASE.
wp; do 2! (cfold 1; kill -1; first by auto).
exlim i, polynomial => i_ polynomial_.
case@[ambient]: (0 <= i_ < 16) => [rgi|]; last first.
  (* FIXME: SHOULD BE A TACTIC *)
- by move=> h; conseq (_ : false ==> _); [smt() | by exfalso].

pose z := map (nth witness (take 8 (drop (8 * i_) (zetaL 0)))) perm0L.

call (NTT_layer0_bf polynomial_ (i_ * 2) (pack8 (map W32.of_int z))); ~-1: smt().

skip=> &hr |> * /=; do! (split=> *).
- rewrite /LAYER_0_ZETAS zeta_L0_AVX2 /= initE ifT //=.
  rewrite !(nth_map witness) /= ?(size_chunk, size_iota) //=.
  by rewrite nth_iota //= -/s sE /= -map_comp /=.
- smt().
- smt().
- rewrite mulrDr /= takeD ~-1://# reduce_n_cat /=; congr.
  - by rewrite -map_take /= size_take_condle ~-1:/# /= ifT /#.
  - rewrite /perm0L /= /z /= /perm0L /=; apply/eq_sym.
    rewrite -!(map_take, map_drop) -[List.map _ _](mkseq_nth witness) /=.
    rewrite size_take_condle // size_drop 1:/# ifT 1:/#.
    pose s := take 8 (drop _ _).
    rewrite -(eq_in_mkseq (fun i => W32.of_int (nth witness s i))) /= -1://.
    move=> i ?; rewrite (nth_map witness) //.
    by rewrite /s size_take_condle //  size_drop 1:/# ifT //#.
qed.

(* -------------------------------------------------------------------- *)
lemma NTT_layer1_bf (p : wpoly) (start : int) (z1 z2 z3 z4 : W32.t) :
     0 <= start < 32
  => 2 %| start
  => hoare[M.polynomial__butterfly_4:
         arg = (p, W64.of_int start, pack4 (map (pack2 \o nseq 2) [z1; z2; z3; z4]))
       ==>
         res = reduce_n p (8 * start) 2 [z1; z3; z2; z4]
     ].
proof.
move=> *; proc.
cfold ^lhs_start<-; kill ^lhs_start<-; first by auto.
cfold ^rhs_start<-; kill ^rhs_start<-; first by auto.

pose uw (i : int) := p.[8 * start + i].
pose vw (i : int) := p.[8 * start + 8 + i].

swap ^rhs<- -1; seq 2 : (#pre /\
     lhs = W8u32.pack8 (mkseq uw 8)
  /\ rhs = W8u32.pack8 (mkseq vw 8)).
- hoare split; auto=> &hr |> /=.
  by rewrite !pmod_small ~-1:/# !wpoly_get256_alignedE //#.

swap ^rhs<- -1; proc change 3 : {
  zeta_products <-
    W8u32.pack8_t (W8u32.Pack.map2 mmr
      (W8u32.unpack32 zeta_products)
      (W8u32.unpack32 zetas)
    );
}.
- by ecall {1} (mmrP_ll zeta_products{1} zetas{1}); auto.

pose bfD (w : int -> W32.t) (z : W32.t) (d i : int) := w (d + i) + mmr (w (d + i + 2)) z.
pose bfB (w : int -> W32.t) (z : W32.t) (d i : int) := w (d + i) - mmr (w (d + i + 2)) z.

pose lhs_ := pack8 (
  mkseq (bfD uw z1 0) 2 ++ mkseq (bfB uw z1 0) 2 ++
  mkseq (bfD uw z3 4) 2 ++ mkseq (bfB uw z3 4) 2
).
pose rhs_ := pack8 (
  mkseq (bfD vw z2 0) 2 ++ mkseq (bfB vw z2 0) 2 ++
  mkseq (bfD vw z4 4) 2 ++ mkseq (bfB vw z4 4) 2
).

seq ^polynomial<- & -1: (#{/~{lhs,rhs}}pre /\ (lhs = lhs_ /\ rhs = rhs_)).
- by hoare split; auto.

seq 2: (#{/~{polynomial}}pre /\ polynomial =
  let p = replace_ p (8 * start    ) (to_list lhs) in
  let p = replace_ p (8 * start + 8) (to_list rhs) in
  p
).
- hoare split; [wp; skip=> &hr [#] <<- ->> 3?| by auto].
  rewrite (replace_mkseq ((\bits32) lhs{hr}) _ _ 8) /=.
  rewrite (replace_mkseq ((\bits32) rhs{hr}) _ _ 8) /=.
  rewrite !(of_uintK, pmod_small) ~-1:/#.
  rewrite !wpoly_set256_alignedE ~-1:/#.
  by rewrite &(fill_congr) ~-1:/# &(fill_congr) ~-1:/#.

skip=> &hr [#] lE rE;
  pose l := W8u32.to_list lhs{hr};
  pose r := W8u32.to_list rhs{hr};
  move=> /=.

rewrite -replace_cat reduce_nE 1:/# => -> /=; congr.
rewrite /reduce_coeff_flatten /= /reduce_coeff /=.
by rewrite /l lE /r rE.
qed.

(* -------------------------------------------------------------------- *)
lemma polynomial__ntt_at_layer_1P (p_ : wpoly) :
  hoare[M.polynomial__ntt_at_layer_1 :
    polynomial = p_ ==> res = reduce_level p_ 1].
proof.
proc; sp; while (
     0 <= i <= 16
  /\ polynomial = reduce_n p_ 0 2 (take (4 * i) (map W32.of_int (zetaL 1)))
); last first.
- auto=> &hr |>; rewrite take0 /= reduce_0 /=.
  move=> j *; have ->> /=: j = 16 by smt().
  by rewrite take_oversize.

proc rewrite 2 LAYER_1_ZETASE.
wp; do 2! (cfold 1; kill -1; first by auto).
exlim i, polynomial => i_ polynomial_.
case@[ambient]: (0 <= i_ < 16) => [rgi|]; last first.
  (* FIXME: SHOULD BE A TACTIC *)
- by move=> h; conseq (_ : false ==> _); [smt() | by exfalso].
pose z1 := W32.of_int (nth witness (zetaL 1) (4 * i_    )).
pose z2 := W32.of_int (nth witness (zetaL 1) (4 * i_ + 1)).
pose z3 := W32.of_int (nth witness (zetaL 1) (4 * i_ + 2)).
pose z4 := W32.of_int (nth witness (zetaL 1) (4 * i_ + 3)).

call (NTT_layer1_bf polynomial_ (i_ * 2) z1 z3 z2 z4); ~-1: smt().

skip=> &hr |> * /=.
pose s := take 4 (drop (4 * i{hr}) (zetaL 1)).
have szs: size s = 4 by rewrite /s size_take_condle // ifT // size_drop /#.
have sE: s = mkseq (fun j => nth witness (zetaL 1) (4 * i{hr} + j)) 4.
- apply/(eq_from_nth witness); first by rewrite size_mkseq.
  move=> j; rewrite szs => [# *]; rewrite nth_mkseq //=.
  by rewrite /s nth_take // nth_drop ~-1://#.
do! (split=> *).
- rewrite /LAYER_1_ZETAS zeta_L1_AVX2 initE ifT //=.
  rewrite !(nth_map witness) /= ?(size_chunk, size_iota) //=.
  rewrite nth_iota //= -/s sE /= -map_comp /=.
  by rewrite /perm1L.
- smt().
- smt().
- rewrite mulrDr /= takeD ~-1://# reduce_n_cat /=; congr.
  - by rewrite -map_take /= size_take_condle ~-1:/# /= ifT /#.
  - by rewrite -!(map_drop, map_take) -/s sE.
qed.

(* -------------------------------------------------------------------- *)
lemma NTT_layer2_bf (p : wpoly) (start : int) (z1 z2 : W32.t) :
     0 <= start < 32
  => 2 %| start
  => hoare[M.polynomial__butterfly_8:
         arg = (p, W64.of_int start, pack2 [pack4 (nseq 4 z1); pack4 (nseq 4 z2)])
       ==>
         res = reduce_n p (8 * start) 4 [z1; z2]
     ].
proof.
move=> *; proc.
cfold ^lhs_start<-; kill ^lhs_start<-; first by auto.
cfold ^rhs_start<-; kill ^rhs_start<-; first by auto.

pose uw (i : int) := p.[8 * start + i].
pose vw (i : int) := p.[8 * start + 8 + i].

swap ^lhs_truncated<- 1; seq 2 : (#pre /\
     lhs = W8u32.pack8 (mkseq uw 8)
  /\ rhs = W8u32.pack8 (mkseq vw 8)).
- hoare split; auto=> &hr |> /=.
  by rewrite !pmod_small ~-1:/# !wpoly_get256_alignedE //#.

swap ^rhs<- -1; proc change 7 : {
  zeta_products <-
    W8u32.pack8_t (W8u32.Pack.map2 mmr
      (W8u32.unpack32 zeta_products)
      (W8u32.unpack32 zetas)
    );
}.
- by ecall {1} (mmrP_ll zeta_products{1} zetas{1}); auto.

pose bfD (w : int -> W32.t) (z : W32.t) (i : int) := w i + mmr (w (i + 4)) z.
pose bfB (w : int -> W32.t) (z : W32.t) (i : int) := w i - mmr (w (i + 4)) z.

pose lhs_ := pack8 (mkseq (bfD uw z1) 4 ++ mkseq (bfB uw z1) 4).
pose rhs_ := pack8 (mkseq (bfD vw z2) 4 ++ mkseq (bfB vw z2) 4).

seq ^polynomial<- & -1: (#{/~{lhs,rhs}}pre /\
  (  lhs = lhs_
  /\ rhs = rhs_)).
- by hoare split; auto.

seq 2: (#{/~{polynomial}}pre /\ polynomial =
  let p = replace_ p (8 * start    ) (to_list lhs) in
  let p = replace_ p (8 * start + 8) (to_list rhs) in
  p
).
- hoare split; [wp; skip=> &hr [#] <<- ->> 3?| by auto].
  rewrite (replace_mkseq ((\bits32) lhs{hr}) _ _ 8) /=.
  rewrite (replace_mkseq ((\bits32) rhs{hr}) _ _ 8) /=.
  rewrite !(of_uintK, pmod_small) ~-1:/#.
  rewrite !wpoly_set256_alignedE ~-1:/#.
  by rewrite &(fill_congr) ~-1:/# &(fill_congr) ~-1:/#.

skip=> &hr [#] lE rE;
  pose l := W8u32.to_list lhs{hr};
  pose r := W8u32.to_list rhs{hr};
  move=> /=.
rewrite -replace_cat reduce_nE 1:/# => -> /=; congr.
rewrite /reduce_coeff_flatten /= /reduce_coeff /=.
by rewrite /l lE /r rE.
qed.

(* -------------------------------------------------------------------- *)
lemma polynomial__ntt_at_layer_2P (p_ : wpoly) :
  hoare[M.polynomial__ntt_at_layer_2 :
    polynomial = p_ ==> res = reduce_level p_ 2].
proof.
proc; sp; while (
     0 <= i <= 16
  /\ polynomial = reduce_n p_ 0 4 (take (2 * i) (map W32.of_int (zetaL 2)))
); last first.
- auto=> &hr |>; rewrite take0 /= reduce_0 /=.
  move=> j *; have ->> /=: j = 16 by smt().
  by rewrite take_oversize.

proc rewrite 2 LAYER_2_ZETASE.
wp; do 2! (cfold 1; kill -1; first by auto).
exlim i, polynomial => i_ polynomial_.
case@[ambient]: (0 <= i_ < 16) => [rgi|]; last first.
  (* FIXME: SHOULD BE A TACTIC *)
- by move=> h; conseq (_ : false ==> _); [smt() | by exfalso].
pose z1 := W32.of_int (nth witness (zetaL 2) (2 * i_    )).
pose z2 := W32.of_int (nth witness (zetaL 2) (2 * i_ + 1)).
call (NTT_layer2_bf polynomial_ (i_ * 2) z1 z2); ~-1: smt().

skip=> &hr |> *.
pose s := take 2 (drop (2 * i{hr}) (zetaL 2)).
have szs: size s = 2 by rewrite /s size_take_condle // ifT // size_drop /#.
have sE: s = mkseq (fun j => nth witness (zetaL 2) (2 * i{hr} + j)) 2.
- apply/(eq_from_nth witness); first by rewrite size_mkseq.
  move=> j; rewrite szs => [# *]; rewrite nth_mkseq //=.
  by rewrite /s nth_take // nth_drop ~-1://#.
do! (split=> *).
- rewrite /LAYER_2_ZETAS zeta_L2_AVX2 initE ifT /= //.
  rewrite !(nth_map witness) /= ?(size_chunk, size_iota) //=.
  by rewrite nth_iota //= -/s sE /= /topair.
- smt().
- smt().
- rewrite mulrDr /= takeD ~-1://# reduce_n_cat /=; congr.
  - by rewrite -map_take /= size_take_condle ~-1:/# /= ifT /#.
  - by rewrite -!(map_drop, map_take) -/s sE.
qed.

(* -------------------------------------------------------------------- *)
lemma ntt_roundP (p_ : wpoly) (stpby base : int) (z : W32.t) :
     0 <= base
  => 1 <= stpby < 6
  => (base + 1) * (16 * stpby) <= 256
  => hoare[M.polynomial__ntt_round :
         arg = (
           p_,
           W64.of_int (8 * stpby),
           W64.of_int stpby,
           W64.of_int base,
           pack8 (nseq 8 z)
         )
       ==>
         res = reduce p_ (16 * stpby * base) (8 * stpby) z
     ].
proof.
move=> ge0b rgstpby hlt; proc.
pose offset_ := 2 * stpby * base.
pose bound_  := offset_ + stpby.

seq ^offset<-{-1} : (#pre /\ offset = W64.of_int offset_).
- hoare split; auto=> &hr |>.
  (* FIXME: I don't want to do these proofs manually *)
  by rewrite /(`>>`) /= shrDP // pmod_small /#.
swap ^i<- @^while; seq ^bound<-{-1}: (#pre /\ bound = W64.of_int bound_).
- by auto.

sp; while (
     (W64.of_int offset_) \ule i
  /\ i \ule (W64.of_int bound_)
  /\ zetas = pack8 (nseq 8 z)
  /\ bound = W64.of_int bound_
  /\ step_by = W64.of_int stpby
  /\ polynomial = reduce_partial p_ (16 * stpby * base) (8 * stpby) (8 * (to_uint i - offset_)) z
); last first.
- skip=> &hr |>; do! split.
  - by rewrite uleE /#. (* FIXME *)
  - by rewrite pmod_small 1:/# reduce_partial0.
  - move=> j; rewrite !(uleE, ultE) /= !pmod_small ~-1:/# => *.
    have ->: (to_uint j - offset_) = stpby by smt().
    by rewrite reduce_as_partial //#.

swap ^coeffs_i<- @^coeffs_i_plus_step<-.
seq ^index_plus_step<-{-1} : (#pre /\ (
     to_uint index = 32 * to_uint i
  /\ to_uint index_plus_step = 32 * (to_uint i + stpby)
)).
- hoare split; auto=> &hr |> ilo _ ihi.
  have rg: offset_ <= to_uint i{hr} < bound_.
  - by move: ilo ihi; rewrite !(uleE, ultE) /#.
  by rewrite !(to_uintD, to_uintM) /= /#.

exlim i => wi_; pose i_ := to_uint wi_.
pose uw (j : int) := p_.[8 * (i_        ) + j].
pose vw (j : int) := p_.[8 * (i_ + stpby) + j].

case@[ambient]: (
     (W64.of_int offset_ \ule wi_)
  /\ (wi_ \ult W64.of_int bound_)
) => [[#] lei gti|]; last first.
- by move=> ?; conseq (_ : false ==> _); [move=> &hr |> /# | exfalso].

rewrite W64.uleE to_uint_small 1:/# in lei.
rewrite W64.ultE to_uint_small 1:/# in gti.

have ?: 0 <= 8 * (to_uint wi_        ) < 256 - 7 by smt().
have ?: 0 <= 8 * (to_uint wi_ + stpby) < 256 - 7 by smt().

seq 2 : (#pre /\
     coeffs_i = W8u32.pack8 (mkseq uw 8)
  /\ coeffs_i_plus_step = W8u32.pack8 (mkseq vw 8)).
- hoare split; auto=> &hr |> /= *; split.
  - rewrite wpoly_get256_alignedE ~-1:/# -(eq_in_mkseq uw) -1://.
    by move=> j rgj /=; rewrite eqexcept_reduce_partial //#.
  - rewrite wpoly_get256_alignedE ~-1:/# -(eq_in_mkseq vw) -1://.
    by move=> j rgj /=; rewrite eqexcept_reduce_partial //#.

swap ^coeffs_i<-{-1} @^polynomial<-.

seq 1: (#pre /\ (product = W8u32.pack8_t
  (W8u32.Pack.map2 mmr (W8u32.unpack32 coeffs_i_plus_step) (W8u32.unpack32 zetas)))).
- ecall (mmrP coeffs_i_plus_step (pack8 (nseq 8 z))); auto=> &hr |> /=.
  - by rewrite of_listK //= 8?nseqS_minus //= nseq0. (* FIXME *)
  - (*by move=> |> * /#.*) (* FIXME *)

seq 2: (#{/~{coeffs_i,coeffs_i_plus_step}}pre /\
     coeffs_i = pack8 (mkseq (fun i => uw i + mmr (vw i) z) 8)
  /\ coeffs_i_plus_step = pack8 (mkseq (fun i => uw i - mmr (vw i) z) 8)
).
- by auto.

exlim polynomial => q.

seq 1: (
     (  #{/~{polynomial}}pre
     /\ q = reduce_partial p_ (16 * stpby * base) (8 * stpby) (8 * (to_uint i - offset_)) z)
  /\ polynomial = replace_ q (8 * (to_uint i + stpby)) (to_list coeffs_i_plus_step)
).
- hoare split; [wp; skip=> &hr [#] -> <- 8? idxE ? hE | by auto].
  have ->: W8u32.to_list coeffs_i_plus_step{hr} =
    mkseq (fun i => coeffs_i_plus_step{hr} \bits32 i) 8 by done.
  rewrite idxE (_ : 32 * _ = 4 * (8 * (to_uint wi_ + stpby))) 1:#ring.
  by rewrite wpoly_set256_aligned -1:replace_mkseq.

seq 1: (#{/~{polynomial}}pre /\ polynomial =
  let q = replace_ q (8 * (to_uint i + stpby)) (to_list coeffs_i_plus_step) in
  let q = replace_ q (8 * (to_uint i        )) (to_list coeffs_i          ) in
  q
).
- hoare split; [wp; skip=> &hr [#] <- 6? idxE ? hE 2? -> | by auto].
  have ->: W8u32.to_list coeffs_i{hr} =
    mkseq (fun i => coeffs_i{hr} \bits32 i) 8 by done.
  move: (replace_ q _ _) => q0; (pose s := mkseq _ _) => /=.
  rewrite /s replace_mkseq idxE.
  rewrite (_ : 32 * _ = 4 * (8 * to_uint wi_)) 1:#ring.
  by rewrite wpoly_set256_aligned.

wp; skip=> &hr;
  pose c2  := W8u32.to_list _;
  pose c1  := W8u32.to_list _;
  pose bfD := mkseq _ 8;
  pose bfB := mkseq _ 8;
  move=> |> *; do! split.
- by rewrite uleE /= to_uintD /#. (* FIXME *)
- by rewrite uleE !to_uintD /#.   (* FIXME *)

rewrite replace_swap; first by suff: size c1 = 8 by smt().
rewrite to_uintD_small /= -1:[_ + 1 + _]addrAC 1:/#.
rewrite [8*(_+1)]mulrDr /= reduce_partialD ~-1://#.
(pose r := (reduce_partial p_ _ _ _ _)) => @/reduce_partial /=.
case _: (reduce_coeff _ _ _ _ _) => c'1 c'2 E /=.
suff [#] 2->: c1 = c'1 /\ c2 = c'2.
- by (congr; first congr); rewrite /offset_ #ring.
move: E; rewrite -(reduce_coeff_eqon p_).
- by move=> i * @/r; rewrite eqexcept_reduce_partial //#.
- by move=> i * @/r; rewrite eqexcept_reduce_partial //#.
rewrite mulrBr /offset_ !mulrA /= addrCA /=.
move=> ^ /(congr1 fst) /= <- /(congr1 snd) /= <-; split.
- rewrite reduce_coeffLE /c1 (_ : W8u32.to_list (pack8 _) = bfD) 1://.
  by apply: eq_mkseq => i /= @/uw @/vw; do! congr => //#.
- rewrite reduce_coeffRE /c2 (_ : W8u32.to_list (pack8 _) = bfB) 1://.
  by apply: eq_mkseq => i /= @/uw @/vw; do! congr => //#.
qed.

(* -------------------------------------------------------------------- *)
lemma polynomial__ntt_at_layer_3P (p_ : wpoly) :
  hoare[M.polynomial__ntt_at_layer_3 :
    polynomial = p_ ==> res = reduce_level p_ 3].
proof.
proc.

proc rewrite 4.2 LAYER_3_ZETASE.
proc change [1..2] : {
  step    <- W64.of_int 8;
  step_by <- W64.of_int 1;
}; first by auto=> |>; circuit.
do 2! (cfold 1; kill -1; first by auto).

sp; while (
     0 <= i <= 16
  /\ polynomial = reduce_n p_ 0 8 (take i (map W32.of_int (zetaL 3)))
); last first.
- auto=> &hr |> *; do! (split=> *).
  - by rewrite take0 reduce_0.
  - by rewrite take_oversize //#.

sp; exlim i, zetas => i_ zetas_.
case@[ambient]: (0 <= i_ < 16) => ?; last first.
- by conseq (_ : false ==> _); [smt() | exfalso].
case@[ambient]: (zetas_ = LAYER_3_ZETAS.[i_]) => zE; last first.
- by conseq (_ : false ==> _); [smt() | exfalso].

exlim polynomial => q.
pose z := W32.of_int (nth witness (zetaL 3) i_).
wp; call (ntt_roundP q 1 i_ z); ~-1: move=> //#.

auto=> &hr |> *; do! (split=> *).
- rewrite -LAYER_3_ZETASE zeta_L3_AVX2 get_of_list ~-1://.
  by rewrite (nth_map witness).
- smt().
- smt().
- rewrite (take_nth witness) 1:// reduce_rcons /=; do! congr.
  - by rewrite size_take_condle //= ifT.
  - by rewrite (nth_map witness).
qed.

(* -------------------------------------------------------------------- *)
lemma polynomial__ntt_at_layer_4P (p_ : wpoly) :
  hoare[M.polynomial__ntt_at_layer_4 :
    polynomial = p_ ==> res = reduce_level p_ 4].
proof.
proc.

proc rewrite 4.2 LAYER_4_ZETASE.
proc change [1..2] : {
  step    <- W64.of_int 16;
  step_by <- W64.of_int 2;
}; first by auto=> |>; circuit.
do 2! (cfold 1; kill -1; first by auto).

sp; while (
     0 <= i <= 8
  /\ polynomial = reduce_n p_ 0 16 (take i (map W32.of_int (zetaL 4)))
); last first.
- auto=> &hr |> *; do! (split=> *).
  - by rewrite take0 reduce_0.
  - by rewrite take_oversize //#.

sp; exlim i, zetas => i_ zetas_.
case@[ambient]: (0 <= i_ < 8) => ?; last first.
- by conseq (_ : false ==> _); [smt() | exfalso].
case@[ambient]: (zetas_ = LAYER_4_ZETAS.[i_]) => zE; last first.
- by conseq (_ : false ==> _); [smt() | exfalso].

exlim polynomial => q.
pose z := W32.of_int (nth witness (zetaL 4) i_).
wp; call (ntt_roundP q 2 i_ z); ~-1: move=> //#.

auto=> &hr |> *; do! (split=> *).
- rewrite -LAYER_4_ZETASE zeta_L4_AVX2 get_of_list ~-1://.
  by rewrite (nth_map witness).
- smt().
- smt().
- rewrite (take_nth witness) 1:// reduce_rcons /=; do! congr.
  - by rewrite size_take_condle //= ifT.
  - by rewrite (nth_map witness).
qed.

(* -------------------------------------------------------------------- *)
lemma polynomial__ntt_at_layer_5P (p_ : wpoly) :
  hoare[M.polynomial__ntt_at_layer_5 :
    polynomial = p_ ==> res = reduce_level p_ 5].
proof.
proc.

proc rewrite 4.2 LAYER_5_ZETASE.
proc change [1..2] : {
  step    <- W64.of_int 32;
  step_by <- W64.of_int 4;
}; first by auto=> |>; circuit.
do 2! (cfold 1; kill -1; first by auto).

sp; while (
     0 <= i <= 4
  /\ polynomial = reduce_n p_ 0 32 (take i (map W32.of_int (zetaL 5)))
); last first.
- auto=> &hr |> *; do! (split=> *).
  - by rewrite take0 reduce_0.
  - by rewrite take_oversize //#.

sp; exlim i, zetas => i_ zetas_.
case@[ambient]: (0 <= i_ < 4) => ?; last first.
- by conseq (_ : false ==> _); [smt() | exfalso].
case@[ambient]: (zetas_ = LAYER_5_ZETAS.[i_]) => zE; last first.
- by conseq (_ : false ==> _); [smt() | exfalso].

exlim polynomial => q.
pose z := W32.of_int (nth witness (zetaL 5) i_).
wp; call (ntt_roundP q 4 i_ z); ~-1: move=> //#.

auto=> &hr |> *; do! (split=> *).
- rewrite -LAYER_5_ZETASE zeta_L5_AVX2 get_of_list ~-1://.
  by rewrite (nth_map witness).
- smt().
- smt().
- rewrite (take_nth witness) 1:// reduce_rcons /=; do! congr.
  - by rewrite size_take_condle //= ifT.
  - by rewrite (nth_map witness).
qed.

(* -------------------------------------------------------------------- *)
lemma polynomial__multiply (p_ : wpoly) (base stpby : int) (z : W32.t) :
     0 <= base
  => 1 <= stpby
  => 8 * (base + 8 * stpby) <= 256 - 7
  => hoare[M.polynomial__multiply :
         arg = (
           p_,
           W64.of_int base,
           W64.of_int (8 * stpby),
           z
         )
       ==>
         res = reduce_partial p_ (8 * base) (64 * stpby) 8 z
     ].
proof.
move=> *; proc => /=.
swap [^index_i<- .. ^index_i<-{-1}] @^index_i_plus_step_by<-.
swap ^coeffs_i<- @^coeffs_i_plus_step_by<-.

seq ^index_i_plus_step_by<-{-1}: (#pre /\
  (  index_i = W64.of_int (32 * base)
  /\ index_i_plus_step_by = W64.of_int (32 * (base + 8 * stpby)))).
- by hoare split; [auto=> &hr |> /# | by auto].

pose uw (i : int) := p_.[8 * base + i].
pose vw (i : int) := p_.[8 * (base + 8 * stpby) + i].

seq ^coeffs_i_plus_step_by<-: (#pre /\
  (  coeffs_i = W8u32.pack8 (mkseq uw 8)
  /\ coeffs_i_plus_step_by = W8u32.pack8 (mkseq vw 8))).
- hoare split; [auto=> &hr |> /= | by auto].
  by rewrite !pmod_small ~-1:/# !wpoly_get256_alignedE /#.

swap ^coeffs_i<- @^polynomial<-.

seq ^polynomial<- & -1: (#{/~{coeffs_i,coeffs_i_plus_step_by}}pre /\
  (  coeffs_i = pack8 (mkseq (fun i => uw i + mmr (vw i) zeta_0{hr}) 8)
  /\ coeffs_i_plus_step_by = pack8 (mkseq (fun i => uw i - mmr (vw i) zeta_0{hr}) 8))
).
- auto=> &hr |> /=.
  rewrite INVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR_E.
  rewrite /INVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR.
  rewrite MODULUS_VECTOR_E /MODULUS_VECTOR /=.

  pose qinv := W32.of_int INVERSE_OF_MODULUS_MOD_MONTGOMERY_R.
  pose q    := W32.of_int MODULUS.

  split.
  - pose F := fun k => uw k + (
        ((vw k \sx zeta_0{hr}) \bits32 1)
      - ((vw k \sx zeta_0{hr} \bits32 0 \sx qinv \bits32 0 \sx q) \bits32 1)).
    rewrite (pack8_eq F (fun i => uw i + mmr (vw i) zeta_0{hr})) //.
    move=> i rgi /=; rewrite -mmr_altE /F /mmr_alt /=.
    by move: (uw i) (vw i) => 2?; rewrite -!shr_shrw //; circuit.
  - pose F := fun k => uw k - (
        ((vw k \sx zeta_0{hr}) \bits32 1)
      - ((vw k \sx zeta_0{hr} \bits32 0 \sx qinv \bits32 0 \sx q) \bits32 1)).
    rewrite (pack8_eq F (fun i => uw i - mmr (vw i) zeta_0{hr})) //.
    move=> i rgi /=; rewrite -mmr_altE /F /mmr_alt /=.
    by move: (uw i) (vw i) => 2?; rewrite -!shr_shrw //; circuit.

seq 1: (#{/~{polynomial}}pre /\ polynomial =
  replace_ p_ (8 * (base + 8 * stpby)) (to_list coeffs_i_plus_step_by)
).
- hoare split; [wp; skip=> &hr [#] -> _ _ _ _ -> _ _ | by auto].
  have ->: W8u32.to_list coeffs_i_plus_step_by{hr} =
    mkseq (fun i => coeffs_i_plus_step_by{hr} \bits32 i) 8 by done.
  rewrite of_uintK pmod_small 1:/# (_ : 32 = 4 * 8) 1:#ring -mulrA.
  by rewrite wpoly_set256_aligned 1:/# replace_mkseq.

seq 1: (#{/~{polynomial}}pre /\ polynomial =
  let p_ = replace_ p_ (8 * (base + 8 * stpby)) (to_list coeffs_i_plus_step_by) in
  let p_ = replace_ p_ (8 * base) (to_list coeffs_i) in
  p_
).
- hoare split; [wp; skip=> &hr [#] _ _ _ -> _ _ -> | by auto].
  have ->: W8u32.to_list coeffs_i{hr} =
    mkseq (fun i => coeffs_i{hr} \bits32 i) 8 by done.
  rewrite of_uintK pmod_small 1:/# (_ : 32 = 4 * 8) 1:#ring -mulrA.
  rewrite wpoly_set256_aligned 1:/#.
  move: (replace_ p_ _ _) => q0; (pose s := mkseq _ _) => /=.
  by rewrite replace_mkseq.

skip=> &hr |> /=; rewrite replace_swap 1:/#.
by rewrite /reduce_partial /reduce_coeff /#.
qed.

(* -------------------------------------------------------------------- *)
lemma polynomial__layer (p : wpoly) (base stpby z : int) :
     0 <= base
  => 1 <= stpby
  => 8 * (base + 8 * stpby) <= 256 - 31
  => hoare[M.polynomial____layer :
         arg = (p, base, 8 * stpby, z)
       ==>
         res = reduce_partial p (8 * base) (64 * stpby) 32 (W32.of_int z)
     ].
proof.
move=> *; proc=> /=; (do 2! (cfold 1; kill -1; first by auto)); sp.
while (
     #{/~{polynomial,i}}pre
  /\ 0 <= i <= 4
  /\ polynomial = reduce_partial p (8 * base) (64 * stpby) (8 * i) (W32.of_int z)
); last first.
- by auto=> &hr |> /#.

wp; cfold 1; kill -1; first by auto.
exlim i, polynomial => i_ q.
case@[ambient]: (0 <= i_ < 4) => ?; last first.
- by conseq (_ : false ==> _); [smt() | exfalso].
call (polynomial__multiply q (base + i_) stpby (W32.of_int z)); ~-1:smt().
auto=> &hr |> *; do! (split=> *).
- by rewrite of_int_bits32_div //#.
- smt().
- smt().
- by rewrite [8 * (_ + 1)]mulrDr /= reduce_partialD -1:-mulrDr //#.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] players : player list = [
  {| base =  0; stepby = 2; twdf = zeta7 ; |};
  {| base =  8; stepby = 2; twdf = zeta7 ; |};
  {| base =  0; stepby = 1; twdf = zeta6L; |};
  {| base = 16; stepby = 1; twdf = zeta6R; |};
  {| base =  4; stepby = 2; twdf = zeta7 ; |};
  {| base = 12; stepby = 2; twdf = zeta7 ; |};
  {| base =  4; stepby = 1; twdf = zeta6L; |};
  {| base = 20; stepby = 1; twdf = zeta6R; |}
].

lemma reduce7E (p : wpoly) :
  reduce_level p 7 = reduce p 0 128 (W32.of_int zeta7).
proof. by rewrite /reduce_level zeta_L7E /= reduce_seq1. qed.

lemma reduce6E (p : wpoly) :
  reduce_level p 6 =
    reduce
      (reduce p 0 64 (W32.of_int zeta6L))
      128 64 (W32.of_int zeta6R).
proof. by rewrite /reduce_level zeta_L6E /= reduce_seq2. qed.

lemma reduce_playersE (p : wpoly) :
  reduce_players p players = reduce_tree p 6.
proof.
rewrite /players.
rewrite (reduce_players_swap 4) ~-1://; cbv lswap iswap => /=.
rewrite (reduce_players_swap 3) ~-1://; cbv lswap iswap => /=.
rewrite (reduce_players_swap 5) ~-1://; cbv lswap iswap => /=.
rewrite (reduce_players_swap 4) ~-1://; cbv lswap iswap => /=.
rewrite (reduce_players_swap 2) ~-1://; cbv lswap iswap => /=.
rewrite (reduce_players_swap 6) ~-1://; cbv lswap iswap => /=.

(* Reduce layer 7 *)
rewrite -(cat_take_drop 4) reduce_players_cat /=.
have /= <- := reduce_players_merge p 4 0 2 zeta7.
pose q7 := reduce_partial _ _ _ _ _.

(* Reduce layer 6 *)
rewrite -(cat_take_drop 2) reduce_players_cat /=.
have /= <- := reduce_players_merge q7 2 0 1 zeta6L.
pose q6L := reduce_partial _ _ _ _ _.
have /= <- := reduce_players_merge q6L 2 16 1 zeta6R.
rewrite /q6L /q7 -(reduce_as_partial p 0 128) 1:// -reduce7E.
rewrite -!(reduce_as_partial _ _ 64) ~-1:// -reduce6E.

(* Reduce tree (2 levels) *)
by rewrite /reduce_tree /range -iotaredE.
qed.

lemma polynomial__ntt_at_layer_7_and_6P (p_ : wpoly) :
  hoare[M.polynomial__ntt_at_layer_7_and_6 :
    polynomial = p_ ==> res = reduce_tree p_ 6].
proof.
proc; proc change [1..5] : {
  sTEP_BY_7 <- 16;
  sTEP_BY_6 <-  8;
  zETA_7    <- zeta7;
  zETA_60   <- zeta6L;
  zETA_61   <- zeta6R;
}; first by auto=> @/(`<<`).
do 5! (cfold 1; kill -1; first by auto).

seq 1: (polynomial = reduce_players p_ (take 1 players)).
- call (polynomial__layer p_ 0 2 zeta7).
  by auto=> &hr |> @/players @/reduce_players @/reduce_player /=.
seq 1: (polynomial = reduce_players p_ (take 2 players)).
- exlim polynomial=> q.
  call (polynomial__layer q 8 2 zeta7).
  by auto=> &hr |> @/players @/reduce_players @/reduce_player /=.
seq 1: (polynomial = reduce_players p_ (take 3 players)).
- exlim polynomial=> q.
  call (polynomial__layer q 0 1 zeta6L).
  by auto=> &hr |> @/players /= @/reduce_players @/reduce_player /=.
seq 1: (polynomial = reduce_players p_ (take 4 players)).
- exlim polynomial=> q.
  call (polynomial__layer q 16 1 zeta6R).
  by auto=> &hr |> @/players /= @/reduce_players @/reduce_player /=.
seq 1: (polynomial = reduce_players p_ (take 5 players)).
- exlim polynomial=> q.
  call (polynomial__layer q 4 2 zeta7).
  by auto=> &hr |> @/players @/reduce_players @/reduce_player /=.
seq 1: (polynomial = reduce_players p_ (take 6 players)).
- exlim polynomial=> q.
  call (polynomial__layer q 12 2 zeta7).
  by auto=> &hr |> @/players @/reduce_players @/reduce_player /=.
seq 1: (polynomial = reduce_players p_ (take 7 players)).
- exlim polynomial=> q.
  call (polynomial__layer q 4 1 zeta6L).
  by auto=> &hr |> @/players /= @/reduce_players @/reduce_player /=.
seq 1: (polynomial = reduce_players p_ (take 8 players)).
- exlim polynomial=> q.
  call (polynomial__layer q 20 1 zeta6R).
  by auto=> &hr |> @/players /= @/reduce_players @/reduce_player /=.

skip=> &hr |>; rewrite take_oversize 1:/players //.
by exact: reduce_playersE.
qed.

(* -------------------------------------------------------------------- *)
lemma polynomial__nttP (p_ : wpoly) :
  hoare[M.polynomial__ntt : polynomial = p_ ==> res = reduce_tree p_ 0].
proof.
proc.
seq 1: (polynomial = reduce_tree p_ 6).
- by call (polynomial__ntt_at_layer_7_and_6P p_); auto.
exlim polynomial => q; seq 1: (polynomial = reduce_tree p_ 5).
- call (polynomial__ntt_at_layer_5P q); auto=> &hr |>.
  by rewrite (reduce_tree_step _ 5).
exlim polynomial => {q} q; seq 1: (polynomial = reduce_tree p_ 4).
- call (polynomial__ntt_at_layer_4P q); auto=> &hr |>.
  by rewrite (reduce_tree_step _ 4).
exlim polynomial => {q} q; seq 1: (polynomial = reduce_tree p_ 3).
- call (polynomial__ntt_at_layer_3P q); auto=> &hr |>.
  by rewrite (reduce_tree_step _ 3).
exlim polynomial => {q} q; seq 1: (polynomial = reduce_tree p_ 2).
- call (polynomial__ntt_at_layer_2P q); auto=> &hr |>.
  by rewrite (reduce_tree_step _ 2).
exlim polynomial => {q} q; seq 1: (polynomial = reduce_tree p_ 1).
- call (polynomial__ntt_at_layer_1P q); auto=> &hr |>.
  by rewrite (reduce_tree_step _ 1).
exlim polynomial => {q} q; seq 1: (polynomial = reduce_tree p_ 0).
- call (polynomial__ntt_at_layer_0P q); auto=> &hr |>.
  by rewrite (reduce_tree_step _ 0).
done.
qed.
