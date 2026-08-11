(* -------------------------------------------------------------------- *)
require import AllCore CoreUtils List IntDiv BitEncoding.

import BitChunking.

(* -------------------------------------------------------------------- *)
from Jasmin require import JWord JModel_x86.
from JazzEC require import Ml_dsa_65_avx2.

require import Array4 Array25 Array32 Array168 Array256 Array848 Array7680.
require import WArray256 WArray848 WArray1024.
require import XArray256 XArray7680.

(* -------------------------------------------------------------------- *)
hint simplify dvdz0.

(* -------------------------------------------------------------------- *)
op modulus : int = 8380417.

(* -------------------------------------------------------------------- *)
hint simplify b2i0, b2i1.

(* -------------------------------------------------------------------- *)
lemma allP_range (k : int) (p : int -> bool) :
  all p (range 0 k) <=> (forall i, 0 <= i < k => p i).
proof. admitted.

(* -------------------------------------------------------------------- *)
lemma allP_range' (k : int) (p : int -> bool) :
  all p (range 0 k) <=> (forall i, 0 <= i => i < k => p i).
proof. admitted.

(* -------------------------------------------------------------------- *)
lemma sub0 (a : 'a Array848.t) (base : int) :
  Array848.sub a base 0 = [].
proof. by rewrite /sub mkseq0. qed.

hint simplify sub0.

(* -------------------------------------------------------------------- *)
theory PrefixArray.
  op sizeB : int.
  op sizeS : int.

  axiom le_size : sizeB <= sizeS.

  clone import PolyArray as AB with op size <- sizeB.
  clone import PolyArray as AS with op size <- sizeS.

  op truncatea'B (a : 'a AS.t) : 'a AB.t =
    AB.init (fun i => a.[i]).

  op injecta'S (a : 'a AS.t) (b : 'a AB.t) : 'a AS.t =
    AS.init (fun i => if 0 <= i < sizeB then b.[i] else a.[i]).

  lemma truncatea'BE (a : 'a AS.t) :
    AB.init (fun i => a.[i]) = truncatea'B a.
  proof. by done. qed.

  lemma injecta'SE (a : 'a AS.t) (b : 'a AB.t) :
    AS.init (fun i => if 0 <= i < sizeB then b.[i] else a.[i])
    = injecta'S a b.
  proof. by done. qed.
end PrefixArray.

clone import PrefixArray as PA_848_168 with
      op sizeB <- 168,
      op sizeS <- 848,
  theory AB    <- Array168,
  theory AS    <- Array848

  rename "'S" as "_848"
         "'B" as "_168"

  proof le_size by done.

(* -------------------------------------------------------------------- *)
op ntho ['a] = nth<:'a>.

lemma ntho0 ['a] (x0 : 'a) (x : 'a) (s : 'a list) :
  nth x0 (x :: s) 0 = x.
proof. done. qed.

lemma nthoS ['a] (x0 : 'a) (x : 'a) (s : 'a list) (n : int):
  0 < n => nth x0 (x :: s) n = nth x0 s (n - 1).
proof. by move=> ? /=; rewrite ifF 1:/#. qed.

hint simplify ntho0, nthoS.

(* -------------------------------------------------------------------- *)
type rho   = W8.t Array32.t.
type wpoly = W32.t Array256.t.
type A     = W32.t Array7680.t.

(* -------------------------------------------------------------------- *)
op [opaque] reject (data : W8.t list) : W32.t list =
  filter (fun w => to_uint w < modulus) (map W4u8.pack4 (chunk 4 data)).

(* -------------------------------------------------------------------- *)
lemma reject_nil : reject [] = [].
proof. admitted.

hint simplify reject_nil.

(* -------------------------------------------------------------------- *)
op [opaque] agree (p : wpoly) (base : int) (coeffs : W32.t list) =
  forall i,
       0 <= i < size coeffs
    => 0 <= i + base < 256
    => p.[base + i] = nth W32.zero coeffs i.

(* -------------------------------------------------------------------- *)
lemma agree_nil (p : wpoly) (base : int) : agree p base [].
proof. admitted.

hint simplify agree_nil.

(* -------------------------------------------------------------------- *)
require Xof.

op shake128_slice : W8.t list -> int -> int -> W8.t list.

(* -------------------------------------------------------------------- *)
type sha3_state = { absorbed : W8.t list; read : int option }.

op is_valid_sha3_state (state : sha3_state) =
  match state.`read with None => true | Some i => 0 <= i end.

(* -------------------------------------------------------------------- *)
op mk_absorbing (data : W8.t list) =
  {| absorbed = data; read = None |}.

(* -------------------------------------------------------------------- *)
op mk_absorbed (data : W8.t list) =
  {| absorbed = data; read = Some 0 |}.

(* -------------------------------------------------------------------- *)
op mk_read (read : int) (data : W8.t list) =
  {| absorbed = data; read = Some read |}.

(* -------------------------------------------------------------------- *)
type sha3x4_state = sha3_state Array4.t.

op is_valid_sha3x4_state (state : sha3x4_state) =
  Array4.all is_valid_sha3_state state.

(* -------------------------------------------------------------------- *)
type sha3x4 = W256.t Array25.t.

op (\sha3for) : sha3x4 -> sha3x4_state -> bool.

lemma is_sha3x4_is_valid (rstate : sha3x4) (state : sha3x4_state) :
  rstate \sha3for state => is_valid_sha3x4_state state.
admitted.

(* -------------------------------------------------------------------- *)
lemma sha3for_eqR rstate s1 s2 :
  s1 = s2 => rstate \sha3for s1 => rstate \sha3for s2.
proof. by move=> ->. qed.

(* -------------------------------------------------------------------- *)
lemma truncateu16_256E (w : W256.t) :
  truncateu16 w = w \bits16 0.
proof. admitted.

(* -------------------------------------------------------------------- *)
lemma bits8_256_shiftE (w : W256.t) (i : int) : 0 <= i < 16 =>
  (w `<<<` 8 * i) \bits8 i = w \bits8 0.
proof. admitted.

(* -------------------------------------------------------------------- *)
lemma bits8_256_le_shiftE (w : W256.t) (i j : int) :
  0 <= i < 16 => 0 <= j < i =>
    (w `<<<` 8 * i) \bits8 j = W8.zero.
proof. admitted.

(* -------------------------------------------------------------------- *)
lemma w256_shift_wintE (w i : int) :
  0 <= i < 256 => W256.of_int (w `<<` i) = W256.of_int w `<<<` i.
proof. admitted.

(* -------------------------------------------------------------------- *)
lemma w256_ofint_bits8E (w i : int) :
  (W256.of_int w) \bits8 i = W8.of_int (w %/ 2^(8*i)).
proof. admitted.

(* -------------------------------------------------------------------- *)
(*
lemma matrix_A__shake128_absorb_34_4xP
  (rho_ : rho) (ds_ : W16.t Array4.t)
: hoare[
  M.matrix_A__shake128_absorb_34_4x :
      rho = rho_ /\ domain_separators = ds_
    ==>
      let state =
        Array4.map (fun w => mk_absorbed (to_list rho_ ++ W2u8.to_list w)) ds_
      in res \sha3for state
  ].
proof.
proc.
admitted.
*)

(* -------------------------------------------------------------------- *)
lemma matrix_A____shake128_squeeze_multiple_blocks_4xP (data : W8.t list Array4.t)
: hoare[
  M.matrix_A____shake128_squeeze_multiple_blocks_4x :
      state \sha3for Array4.map (mk_absorbed) data
    ==>
         res.`1 \sha3for Array4.map (mk_read (168 * 5)) data
      /\ (forall i, 0 <= i < 4 =>
            let b = ntho witness [res.`2; res.`3; res.`4; res.`5] i in
            Array848.sub b 0 840 = shake128_slice data.[i] 0 840)
  ].
proof.
proc.
admitted.

(* -------------------------------------------------------------------- *)
op MODULUS8u32 =
  W8u32.pack8 (nseq 8 (W32.of_int modulus)).

(* -------------------------------------------------------------------- *)
section.
hint simplify nseq0, nseqS.
hint simplify range_geq, range_ltn.

lemma MODULUS8u32E :
  W256.of_int
    0x007fe001007fe001007fe001007fe001007fe001007fe001007fe001007fe001
  = MODULUS8u32.
proof.
apply/W8u32.wordP=> i rgi; rewrite pack8bE //= get_of_list //.
rewrite nth_nseq //= of_int_bits32_div //=.
by move: i rgi; apply/allP_range.
qed.
end section.

(* -------------------------------------------------------------------- *)
lemma WArray848_get256E (a : W8.t Array848.t) (base : int)  :
    WArray848.get256_direct
      (WArray848.init8 (fun (i : int) => a.[i]))
      base
  = W32u8.pack32 (Array848.sub a base 32).
proof. admitted.

(* -------------------------------------------------------------------- *)
lemma WArray256_get128E (a : W8.t Array256.t) (base : int) :
    WArray256.get128_direct
      (WArray256.init8 (fun (i : int) => a.[i]))
      base
  = W16u8.pack16 (Array256.sub a base 16).
proof. admitted.

(* -------------------------------------------------------------------- *)
lemma W32Array256_set128E (a : W32.t Array256.t) (base : int) (w : W128.t) :
   Array256.init                                                               
      (fun (i : int) =>                                                         
         WArray1024.get32                                            
           (WArray1024.set128_direct                                 
              (WArray1024.init32 (fun (i0 : int) => a.[i0]))
              base w) i)
 = XArray256.PAE.replace_ a base (to_list (W4u32.unpack32 w)).
proof. admitted.

(* -------------------------------------------------------------------- *)
hint exact : W64.WRingA.oner_neq0.

(* -------------------------------------------------------------------- *)
lemma of_int_b2i_eq1P (b : bool) : W64.of_int (b2i b) = W64.one => b.
proof. by case: b => //; rewrite b2i0 /= eq_sym. qed.

(* -------------------------------------------------------------------- *)
lemma matrix_A__rejection_sample_multiple_blocksP (buf : W8.t Array848.t)
: hoare[
  M.matrix_A__rejection_sample_multiple_blocks :
      randombytes = buf
    ==>
         agree res.`1 0 (reject (Array848.sub buf 0 840))
      /\ to_uint res.`2 = size (reject (Array848.sub buf 0 840))
  ].
proof.
proc=> /=.
seq 2 : #pre; first by auto.
sp 4; seq 0 : (#{/~{modulus}}pre /\ modulus = MODULUS8u32).
- by auto=> &hr |>; rewrite MODULUS8u32E.
proc rewrite 1.1  WArray848_get256E.
proc rewrite 1.11 WArray256_get128E.
proc rewrite 1.13 W32Array256_set128E.
proc rewrite 1.22 WArray256_get128E.
proc rewrite 1.24 W32Array256_set128E.
seq ^while : (
     to_uint bytes_filled <= 256
  /\ (to_uint bytes_filled < 256 => to_uint input_offset = 5 * 168)
  /\ 3 %| to_uint input_offset
  /\ agree polynomial 0 (reject (Array848.sub randombytes 0 (to_uint input_offset)))
).
- while (
       to_uint bytes_filled <= 256
    /\ to_uint input_offset <= 5 * 168
    /\ 24 %| to_uint input_offset
    /\ (stop_sampling = W64.of_int (b2i (!(
            to_uint bytes_filled <= (256 - 8) * 4
         /\ to_uint input_offset < 5 * 168))))
    /\ agree polynomial 0 (reject (Array848.sub randombytes 0 (to_uint input_offset)))
  ); last first.
  - by hoare split; auto=> &hr |> * /=; smt(of_int_b2i_eq1P).
  exlim randombytes => rb.
  proc change [0..1] : { randombytes <- rb; }.

 [by auto | cfold 1; wp -1].


  seq 2 : (#pre /\ potential_coefficients =
    W8u32.pack8 (map W4u8.pack4 (chunk 3 (sub randombytes (to_uint input_offset) 24)))).
  - hoare split; [conseq (_ : true ==> _); sp | by conseq |>].
    admit.
*)  
    

admitted.

(* -------------------------------------------------------------------- *)
op Apoly (rho : rho) (rc : int * int) : wpoly.

(* -------------------------------------------------------------------- *)
op A_rc_of_index (i : int) =
  (i %/ 5, i %% 5).

(* -------------------------------------------------------------------- *)
op poly_index_in_A (rc : int * int) : int =
  (5 * rc.`1 + rc.`2) * 256.

(* -------------------------------------------------------------------- *)
op poly_of_A (A : A) (rc : int * int) =
  Array256.of_list W32.zero (Array7680.sub A (poly_index_in_A rc) 256).

(* -------------------------------------------------------------------- *)
op A_valid_up_to (rho : rho) (A : A) (i : int) =
  forall k, 0 <= k < i =>
    poly_of_A A (A_rc_of_index k) = Apoly rho (A_rc_of_index k).

(* -------------------------------------------------------------------- *)
op A_ds (rc : int * int) : W16.t =
  W2u8.pack2 [W8.of_int rc.`2; W8.of_int rc.`1].

(* -------------------------------------------------------------------- *)
hint simplify mkseqSr_minus, mkseq0.
hint simplify range_geq, range_ltn.

(* -------------------------------------------------------------------- *)
op update_poly (a : A) (base : int) (p : W32.t Array256.t) =
  replace_ a (256 * base) (to_list p).

(* -------------------------------------------------------------------- *)
op update_polys (a : A) (base : int) (ps : W32.t Array256.t list) =
  foldl (fun a (ip : _ * _) =>
    update_poly a (base + ip.`1) ip.`2
  ) a (zip (range 0 (size ps)) ps).

(* -------------------------------------------------------------------- *)
lemma update_polys_A_valid_up_to (rho : rho) (a : A) (base : int) (tp : wpoly list) :
     A_valid_up_to rho a base
  => (forall i, 0 <= i < size tp =>
        nth witness tp i = Apoly rho (A_rc_of_index (base + i)))
  => A_valid_up_to rho (update_polys a base tp) (base + size tp).
proof.

admitted.

(* -------------------------------------------------------------------- *)
lemma replace_256_7680E (a : W32.t Array7680.t) (base : int) (b : W32.t Array256.t) :
  Array7680.init                                               
    (fun (i : int) =>                                          
       if base * 256 <= i < base * 256 + 256 then
         b.[i - base * 256]
       else a.[i])
  = update_poly a base b.
proof. admitted.

(* -------------------------------------------------------------------- *)
op reject_ok (nonce : W8.t list) (sz : int) (p : wpoly) (filled : int) =
     agree p 0 (reject (shake128_slice nonce 0 sz))
  /\ filled = size (reject (shake128_slice nonce 0 sz)).

(* -------------------------------------------------------------------- *)
lemma matrix_A____sample_4_polynomialsP
  (rho_ : rho) (rcs : (int * int) option list)
: hoare[
  M.matrix_A____sample_4_polynomials :
         rho = rho_
      /\ (forall i, 0 <= i < 4 =>
           domain_separators.[i] =
             odflt domain_separators.[i] (omap A_ds (ntho None rcs i)))
    ==>
         forall i, 0 <= i < 4 =>
           let resi = ntho witness [res.`1; res.`2; res.`3; res.`4] i in
           odflt true (omap (fun rc => resi = Apoly rho_ rc) (ntho None rcs i))
].
proof.
proc=> /=.
seq ^xof_state<- : #pre; first by auto.
pose stop fs := W32.of_int (b2i (!has (fun w => w \ult W64.of_int 256) fs)).
proc change [^stop_sampling<- .. ^stop_sampling<- & +2] : {
  stop_sampling <- stop [filled0; filled1; filled2; filled3];
}; first by auto=> &hr @/stop |>. 
exlim domain_separators => ds_.
proc change [0..0] : { rho <- rho_; domain_separators <- ds_; }; first by auto.
do 2! (cfold 1); wp -2; seq 0 : #{/~{rho}}pre; first by auto.
pose Ads i := odflt ds_.[i] (omap A_ds (nth None rcs i)).
pose nonce i := to_list rho_ ++ W2u8.to_list ds_.[i].
seq 0: (forall i, 0 <= i < 4 => ds_.[i] = Ads i).
- by auto=> &hr [#] ->> /#.
case@[ambient]: (forall i, 0 <= i < 4 => ds_.[i] = Ads i) => ?; last by exfalso.

(* Initial absorption *)
seq 1 : (xof_state \sha3for Array4.init (mk_absorbed \o nonce)).
- ecall (matrix_A__shake128_absorb_34_4xP rho_ ds_) => /=.
  auto=> &hr |> rst; apply/sha3for_eqR/Array4.ext_eq=> i ?.
  by rewrite mapiE -1:initiE.

(* Squeeze first blocks *)
pose data := Array4.init nonce.
seq 1: (
     xof_state \sha3for Array4.init (mk_read (168 * 5) \o nonce)
  /\ (forall i, 0 <= i < 4 =>
        let b = ntho witness [buf0; buf1; buf2; buf3] i in
        Array848.sub b 0 840 = shake128_slice data.[i] 0 840)).
- ecall ->> (matrix_A____shake128_squeeze_multiple_blocks_4xP data) => /=.
  - move=> &hr |>; apply: sha3for_eqR.
    by apply: Array4.ext_eq; smt(Array4.mapiE Array4.initiE).
  auto=> |> &hr + ?; apply/sha3for_eqR/Array4.ext_eq.
  by move=> i rgi; rewrite mapiE // !initiE.

seq ^stop_sampling<- & -1 : (#{/~{buf0, buf1, buf2, buf3}}pre /\
  (forall i, 0 <= i < 4 =>
     let p = ntho witness [polynomial0; polynomial1; polynomial2; polynomial3] i in
     let f = ntho witness [filled0; filled1; filled2; filled3] i in
        reject_ok data.[i] 840 p (to_uint f))).
- hoare split; last by conseq |>.
  ecall ->> (matrix_A__rejection_sample_multiple_blocksP buf0) => /= [|>|buf0_]; sp.
  ecall ->> (matrix_A__rejection_sample_multiple_blocksP buf1) => /= [|>|buf1_]; sp.
  ecall ->> (matrix_A__rejection_sample_multiple_blocksP buf2) => /= [|>|buf2_]; sp.
  ecall ->> (matrix_A__rejection_sample_multiple_blocksP buf3) => /= [|>|buf3_]; sp.
  by auto=> &hr |> * /#.

  while (exists (k : int), (
       xof_state \sha3for Array4.init (mk_read (168 * k) \o nonce)
    /\ (forall i, 0 <= i < 4 =>
          let p = ntho witness [polynomial0; polynomial1; polynomial2; polynomial3] i in
          let f = ntho witness [filled0; filled1; filled2; filled3] i in
          reject_ok data.[i] (168 * k) p (to_uint f))
    /\ (stop_sampling = stop [filled0; filled1; filled2; filled3])
  )); last first.
  - auto=> &hr |> *; split.
    - by exists 5 => /=.
    - move=> f0 f1 f2 f3 p0 p1 p2 p3 xf k ? h + i *.
      move=> @/stop /eq_sym {stop}; case _: (has _ _) => /=.
      - by move=> _ /(congr1 W32.to_uint); rewrite !of_uintK.
      rewrite !negb_or !ultE /= -!lezNgt => [#] 4?.
      case _: (ntho None rcs i) => //= rc Erc.
      have [] := h i //. admit.

  elim* => k.

  proc rewrite 3 injecta_848E.
  proc rewrite 4 injecta_848E.
  proc rewrite 5 injecta_848E.
  proc rewrite 6 injecta_848E.

  proc change [^stop_sampling<- .. ^stop_sampling<- & +2] : {
    stop_sampling <- stop [filled0; filled1; filled2; filled3];
  }; first by auto=> &hr @/stop |>.

admitted.

(* -------------------------------------------------------------------- *)
lemma sample____matrix_A_P (rho_ : rho) : hoare[M.sample____matrix_A :
  rho = rho_ ==> A_valid_up_to rho_ res 30
].
proof.
proc.
seq  4 : #pre  ; first by auto.
seq -2 : # post; last  by auto.
cfold 1; kill -1; [by auto | sp].

seq ^while : (rho = rho_ /\ A_valid_up_to rho matrix_A 28).
- while (#{/~{matrix_A, chunk}}pre
    /\ 0 <= chunk <= 7
    /\ A_valid_up_to rho matrix_A (4 * chunk)
  ); last by auto=> &hr |> /#.

  cfold 1; kill -1; first by auto.
  seq 3 : (#pre
    /\ aux   = Apoly rho (A_rc_of_index (4 * chunk    ))
    /\ aux_0 = Apoly rho (A_rc_of_index (4 * chunk + 1))
    /\ aux_1 = Apoly rho (A_rc_of_index (4 * chunk + 2))
    /\ aux_2 = Apoly rho (A_rc_of_index (4 * chunk + 3))
  ); last first.
  - proc rewrite 1 replace_256_7680E.
    proc rewrite 2 replace_256_7680E.
    proc rewrite 3 replace_256_7680E.
    proc rewrite 4 replace_256_7680E.
    do 2! (hoare split; last by auto=> /#); auto=> &hr |> 4?.
    pose tp i := Apoly rho{hr} (A_rc_of_index (4 * chunk{hr} + i)).
    pose pa := update_polys matrix_A{hr} (4 * chunk{hr}) (mkseq tp 4).
    rewrite (_ : update_poly _ _ _ = pa); first done.
    rewrite mulrDr /= {2}(_ : 4 = size (mkseq tp 4)) //.
    by rewrite update_polys_A_valid_up_to //#.

  seq ^while : (#pre /\
    (forall i, 0 <= i < 4 =>
       domain_separators.[i] = A_ds (A_rc_of_index (4 * chunk + i)))
  ).
  - hoare split; last by conseq=> |>.
    while (
         0 <= chunk <= 7
      /\ 0 <= lane <= 4
      /\ (forall i, 0 <= i < lane =>
            domain_separators.[i] = A_ds (A_rc_of_index (4 * chunk + i)))
    ); last by auto=> &hr |> /#.
    hoare split; last by auto=> |> /#.
    hoare split; last by auto=> |> /#.
    auto=> &hr |> 4? ih ? i * /=; pose ds := W16u16.truncateu16 _.
    have -> {ds}: ds = A_ds (A_rc_of_index (4 * chunk{hr} + lane{hr})).
    - rewrite /A_ds /A_rc_of_index /=; apply: W2u8.wordP.
      move=> k ?; have [#|] ->> /=: k = 0 \/ k = 1 by smt().
      - rewrite /ds truncateu16_256E /= w256_shift_wintE //.
        rewrite (bits8_256_le_shiftE _ 1 0) //=.
        by rewrite w256_ofint_bits8E.
      - rewrite /ds truncateu16_256E /= w256_shift_wintE //.
        rewrite (bits8_256_shiftE _ 1) //=.
        by rewrite !w256_ofint_bits8E /= [_ %/ 256]pdiv_small 1:/#.
    by case: (i < lane{hr}) => ?; rewrite get_set_if //#.

  exlim chunk => chunk_.
  call (matrix_A____sample_4_polynomialsP rho_
    (mkseq (fun i => Some (A_rc_of_index (4 * chunk_ + i))) 4)
  ).
  - auto=> &hr |> 4? dsE; split.
    - by apply/allP_range' => @/ntho /= /#.
    - by move=> _ r /allP_range @/ntho /=.

cfold 1; kill -1; first by auto.
seq ^while : (#pre /\
  (forall i, 0 <= i < 2 =>
     domain_separators.[i] = A_ds (A_rc_of_index (28 + i)))
).
- hoare split; last by conseq |>.
  while (
       0 <= lane <= 2
    /\ (forall i, 0 <= i < lane =>
            domain_separators.[i] = A_ds (A_rc_of_index (28 + i)))
  ); last by auto=> &hr |> /#.
  - hoare split; last by auto=> |> /#.  
    auto=> &hr |> 2? ih ? i *; pose ds := W16u16.truncateu16 _.
    have -> {ds}: ds = A_ds (A_rc_of_index (28 + lane{hr})).
    - rewrite /A_ds /A_rc_of_index /=; apply: W2u8.wordP.
      move=> k ?; have [#|] ->> /=: k = 0 \/ k = 1 by smt().
      - rewrite /ds truncateu16_256E /= w256_shift_wintE //.
        rewrite (bits8_256_le_shiftE _ 1 0) //=.
        by rewrite w256_ofint_bits8E.
      - rewrite /ds truncateu16_256E /= w256_shift_wintE //.
        rewrite (bits8_256_shiftE _ 1) //=.
        by rewrite !w256_ofint_bits8E /= [_ %/ 256]pdiv_small 1:/#.
    by case: (i < lane{hr}) => ?; rewrite get_set_if //#.

seq 1: (#pre
  /\ aux   = Apoly rho (A_rc_of_index 28)
  /\ aux_0 = Apoly rho (A_rc_of_index 29)); last first.
- proc rewrite 1 (replace_256_7680E _ 28).
  proc rewrite 2 (replace_256_7680E _ 29).
  auto=> &hr |> 2?.
  pose tp i := Apoly rho{hr} (A_rc_of_index (28 + i)).
  pose pa := update_polys matrix_A{hr} 28 (mkseq tp 2).
  rewrite (_ : update_poly _ _ _ = pa); first by done.
  by rewrite (update_polys_A_valid_up_to _ _ 28) //#.

call (matrix_A____sample_4_polynomialsP rho_
  [Some (A_rc_of_index 28); Some (A_rc_of_index 29)]
).
auto=> &hr |> ? h; split.
- by apply/allP_range' => @/ntho /= /#.
- by move=> _ r /allP_range @/ntho.
qed.
