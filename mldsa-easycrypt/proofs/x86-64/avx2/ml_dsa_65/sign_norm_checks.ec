require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Signature
                           Common_modular Common_invert_ntt Common_rounding.

from Spec require import GFq Rq Parameters VecMat MLDSA_W32_Rep.
import PolyLVec PolyKVec.
import Round ZModQ Zq.
import StdBigop.Bigint BIA.

require import Array256 Array1280 Array1536.

require import Polynomial Row_vector.

lemma lifts_wpolykvec_slice (v : W32.t Array1536.t) (base : int) :
  base %% 256 = 0 => 0 <= base %/ 256 < kvec =>
  lifts_wpoly (Array256.init (fun i => v.[base + i])) =
  (lifts_wpolykvec (kvec_unflatten256 v)).[base %/ 256].
proof.
move => Hmod Hk.
rewrite /lifts_wpolykvec mapiE 1:/# /=.
by rewrite -kvec_slice_eq.
qed.

lemma lifts_wpolylvec_slice (v : W32.t Array1280.t) (base : int) :
  base %% 256 = 0 => 0 <= base %/ 256 < lvec =>
  lifts_wpoly (Array256.init (fun i => v.[base + i])) =
  (lifts_wpolylvec (lvec_unflatten256 v)).[base %/ 256].
proof.
move => Hmod Hk.
rewrite /lifts_wpolylvec mapiE 1:/# /=.
by rewrite -lvec_slice_eq.
qed.

lemma __apply_cs2_and_check_norm_ll : islossless M.__apply_cs2_and_check_norm.
proof.
proc.
wp; while (0 <= base <= 6 * n /\ base %% n = 0) (6*n - base); last by auto => /#.
move => ?.
wp; call polynomial____check_infinity_norm_ll.
wp; call polynomial__reduce32_ll.
wp; call polynomial__subtract_ll.
wp; call polynomial__invert_ntt_montgomery_ll.
wp; call polynomial__pointwise_montgomery_multiply_and_reduce_ll.
by auto => /#.
qed.

(* ================================================================== *)
(* __compute_signer_response_element                                    *)
(* Computes one column of z = mask + c*s1:                             *)
(*   cs1 = invntt(basemul(s1_element, verifier_challenge))            *)
(*   result = reduce32(mask_element + cs1)                             *)
(* ================================================================== *)

lemma __compute_signer_response_element_ll : islossless M.__compute_signer_response_element.
proof.
proc.
wp; call polynomial__reduce32_ll.
wp; call polynomial__add_ll.
wp; call polynomial__invert_ntt_montgomery_ll.
wp; call polynomial__pointwise_montgomery_multiply_and_reduce_ll.
by auto.
qed.

lemma __compute_signer_response_element_correct
      (_s1e : W32.t Array256.t) (_c : W32.t Array256.t)
      (_mask_e : W32.t Array256.t) (_sre : W32.t Array256.t) :
    hoare [ M.__compute_signer_response_element :
        s1_element = _s1e /\ verifier_challenge = _c /\
        mask_element = _mask_e /\ signer_response_element = _sre /\
        wpoly_ntt_orng _s1e /\ wpoly_ntt_orng _c /\
        wpoly_srng gamma1 gamma1 _mask_e
        ==>
        (* z = mask + invntt(c * s1) coefficient-wise *)
        lifts_wpoly res =
          lifts_wpoly _mask_e &+ invntt (basemul (lifts_wpoly _s1e) (lifts_wpoly _c)) /\
        (* output is reduced to centered representatives *)
        wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2) res
    ].
proof.
proc.
ecall (polynomial__reduce32_correct signer_response_element).
ecall (polynomial__add_correct signer_response_element cs1 mask_element (q-1) gamma1).
ecall (polynomial__invert_ntt_montgomery_correct cs1).
ecall (polynomial__pointwise_montgomery_multiply_and_reduce_correct cs1 s1_element verifier_challenge).
auto => |> [#] Hs1e Hc Hmask.
do split => /=.
- by exact (wpoly_ntt_orng_bmul_irng _s1e).
- by exact (wpoly_ntt_orng_bmul_irng _c).
move => Hbmul_s1 Hbmul_c result [# Hbmul_eq Hbmul_rng].
split; 1: by  exact (wpoly_bmul_orng_intt_irng result Hbmul_rng).
move => ?result0 [# Hintt_eq Hintt_rng].
have Hintt_rng_wide : wpoly_srng (q-1) (q-1) result0.
+ by apply (wpoly_srng_widen result0 invntt_obound invntt_obound (q-1) (q-1) _ _ Hintt_rng);
    smt(invntt_obound_fits_for_caddq mldsa65_Eta).
split; 1: by smt(mldsa65_gamma1).
move => _ _ result1 Hadd_eq _ result2 Hred_eq _.
rewrite Hred_eq Hadd_eq Hintt_eq Hbmul_eq.
by rewrite Rq_addC.
qed.

lemma __compute_signer_response_element_ph
      (_s1e : W32.t Array256.t) (_c : W32.t Array256.t)
      (_mask_e : W32.t Array256.t) (_sre : W32.t Array256.t) :
    phoare [ M.__compute_signer_response_element :
        s1_element = _s1e /\ verifier_challenge = _c /\
        mask_element = _mask_e /\ signer_response_element = _sre /\
        wpoly_ntt_orng _s1e /\ wpoly_ntt_orng _c /\
        wpoly_srng gamma1 gamma1 _mask_e
        ==>
        lifts_wpoly res =
          lifts_wpoly _mask_e &+ invntt (basemul (lifts_wpoly _s1e) (lifts_wpoly _c)) /\
        wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2) res
    ] = 1%r
  by conseq __compute_signer_response_element_ll
            (__compute_signer_response_element_correct _s1e _c _mask_e _sre).

lemma __apply_cs2_and_check_norm_correct
      (_w0mc : W32.t Array1536.t) (_w0 : W32.t Array1536.t)
      (_s2 : W32.t Array1536.t) (_c : W32.t Array256.t)
      (_incr : W64.t)
      :
    hoare [ M.__apply_cs2_and_check_norm :
        w0_minus_cs2 = _w0mc /\ w0 = _w0 /\ s2 = _s2 /\
        verifier_challenge = _c /\ infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolykvec_ntt_orng (kvec_unflatten256 _s2) /\
        (* w0 = LowBits(Ay), coefficients in (-gamma2, gamma2] = (-261888, 261888] *)
        wpolykvec_srng (kvec_unflatten256 _w0) (gamma2 - 1) gamma2
        ==>
        (res.`2 = W64.zero \/ res.`2 = W64.one) /\
        (* Biconditional: failure bit is zero iff no prior failure AND
           the abstract cs2-norm check holds. *)
        (res.`2 = W64.zero <=>
           _incr = W64.zero /\
           PolyKVec.infnorm_lt
             (lifts_wpolykvec (kvec_unflatten256 _w0) -
              PolyKVec.invnttv (PolyKVec.ntt_smul
                (lifts_wpoly _c)
                (lifts_wpolykvec (kvec_unflatten256 _s2))))
             (gamma2 - Beta)) /\
        (res.`2 = W64.zero =>
           (* ||w0 - cs2||_inf < gamma2 - Beta = 261692 *)
           wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 res.`1) /\
           lifts_wpolykvec (kvec_unflatten256 res.`1) =
             (lifts_wpolykvec (kvec_unflatten256 _w0)) -
             (PolyKVec.invnttv (PolyKVec.ntt_smul
               (lifts_wpoly _c)
               (lifts_wpolykvec (kvec_unflatten256 _s2)))))
    ].
proof.
have kvec_val := mldsa65_kvec.
have gamma2_val := mldsa65_gamma2.
have tau_val := mldsa65_tau.
have eta_val := mldsa65_Eta.
proc => /=.
case (infinity_norm_check_result <> zero).
+ rcondt ^if;1: by auto.
  rcondf ^while;1: by auto.
  by auto => /#.
  
conseq (: _ ==>
  (infinity_norm_check_result = zero \/ infinity_norm_check_result = one) /\
  (infinity_norm_check_result = zero <=>
   PolyKVec.infnorm_lt
     (lifts_wpolykvec (kvec_unflatten256 _w0) -
      invnttv (ntt_smul (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _s2))))
     (gamma2 - Beta)) /\
  (infinity_norm_check_result = zero =>
   (wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 w0_minus_cs2) /\
   lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2) =
   lifts_wpolykvec (kvec_unflatten256 _w0) -
   invnttv (ntt_smul (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _s2))))));
 1: by move => |> &hr ?? infncr rr *; rewrite H_incr /=;
       smt(W64.to_uint_eq pow2_64 W64.to_uintK W64.of_uintK).

rcondf ^if; 1: by auto.
while (#{/~_incr}{~infinity_norm_check_result}{~w0_minus_cs2}pre /\
       _incr = W64.zero /\
       (infinity_norm_check_result = zero \/ infinity_norm_check_result = one) /\
       0 <= base <= 6*n /\ base %% n = 0 /\
       (infinity_norm_check_result <> zero => base = 6*n) /\
       (infinity_norm_check_result <> zero =>
         ! PolyKVec.infnorm_lt
             (lifts_wpolykvec (kvec_unflatten256 _w0) -
              invnttv (ntt_smul (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _s2))))
             (gamma2 - Beta)) /\
      (
       infinity_norm_check_result = zero =>
       ((forall k, 0 <= k < base %/ n =>
           wpoly_srng (gamma2 - Beta - 1) (gamma2 - Beta - 1) ((kvec_unflatten256 w0_minus_cs2)).[k]) /\
       (forall k, 0 <= k < base %/ n =>
         (lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2)).[k] =
         (lifts_wpolykvec (kvec_unflatten256 _w0) -
         invnttv (ntt_smul (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _s2)))).[k]))
      )
      ); last first.

+ auto => /> H_incr' H01 *; do split; 1,2: smt().
  move =>  ?? bs ?????? H_fail H_srng ; do split; 2: by smt().
  +   move => Hzero.
      have [Hsrng Hlifts] := H_srng Hzero.
      have Hwpkv : wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 bs)
        by rewrite /wpolykvec_infnorm_lt /wpolykvec_srng allP => *; smt(mldsa65_kvec).
      have Hleq : lifts_wpolykvec (kvec_unflatten256 bs) =
          lifts_wpolykvec (kvec_unflatten256 _w0) -
          invnttv (ntt_smul (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _s2)))
        by apply KArray.tP => *; smt(mldsa65_kvec).
      rewrite -Hleq.
      by apply (wpolykvec_infnorm_liftE (gamma2 - Beta)); smt(mldsa65_gamma2).

  +   move => Hzero.
      have [Hsrng Hlifts] := H_srng Hzero.
      have Hwpkv : wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 bs)
        by rewrite /wpolykvec_infnorm_lt /wpolykvec_srng allP => *; smt(mldsa65_kvec).
      have Hleq : lifts_wpolykvec (kvec_unflatten256 bs) =
          lifts_wpolykvec (kvec_unflatten256 _w0) -
          invnttv (ntt_smul (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _s2)))
        by apply KArray.tP => *; smt(mldsa65_kvec).
      rewrite -Hleq.
      by smt().

(* ── Loop body: one row at index i = base %/ n ──────────────────────── *)

seq 6 : (#pre /\
    lifts_wpoly (Array256.init (fun i => w0_minus_cs2.[base + i])) =
      (lifts_wpolykvec (kvec_unflatten256 _w0) -
       PolyKVec.invnttv (PolyKVec.ntt_smul
         (lifts_wpoly _c)
         (lifts_wpolykvec (kvec_unflatten256 _s2)))).[base %/ n] /\
    (* coefficients are centered representatives: to_sint = crepr *)
    wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2)
               (Array256.init (fun i => w0_minus_cs2.[base + i]))).
+ (* Loop body: basemul → invNTT → subtract → writeback → reduce32 → writeback.
     Process backwards (ecall/wp work right-to-left). *)
  wp. (* instruction 6: writeback w0_minus_cs2 <- Array1536.init ... *)
  ecall (polynomial__reduce32_correct
           (Array256.init (fun i => w0_minus_cs2.[base + i]))).
  wp. (* instruction 4: writeback w0_minus_cs2 <- Array1536.init ... *)
  ecall (polynomial__subtract_correct
           (Array256.init (fun i => w0_minus_cs2.[base + i]))
           (Array256.init (fun i => w0.[base + i]))
           cs2 gamma2 (2^31 - gamma1)).
  ecall (polynomial__invert_ntt_montgomery_correct cs2).
  ecall (polynomial__pointwise_montgomery_multiply_and_reduce_correct
           cs2
           (Array256.init (fun i => s2.[base + i]))
           verifier_challenge).
  auto => |> &hr ? Hs2_ntt Hw0_srng ?????? HH*.
  (* Strategy: same ecall-chain pattern as __compute_signer_response_element_correct,
     but the lhs is a w0 slice (not mask) and the algebraic goal uses kvec components.
     Key lemmas: polykvec_sub_iE, invnttv_ntt_smul_k (both in VecMat.ec).
     The flat-array/kvec connection is proved inline via mapiE+tP+initiE+get_of_list+nth_sub. *)
  do split => /=.
  (* ── bmul pre: s2 slice — kvec_slice_eq replaces 8-line inline proof ── *)
  - have Hs2_bmul := wpolykvec_ntt_orng_bmul_irng _ Hs2_ntt.
    have Heq_s2 : (kvec_unflatten256 _s2).[base{hr} %/ n] = Array256.init (fun i => _s2.[base{hr} + i]).
    + by apply kvec_slice_eq; smt(mldsa65_kvec).
    rewrite -Heq_s2.
    move: Hs2_bmul; rewrite /wpolykvec_bmul_irng allP => H; apply H; smt(mldsa65_kvec).
  (* ── bmul pre: verifier challenge ── *)
  - by smt(wpoly_ntt_orng_bmul_irng).
  move => Hbmul_s2 Hbmul_c result [# Hbmul_eq Hbmul_rng].
  split; 1: by exact (wpoly_bmul_orng_intt_irng result Hbmul_rng).
  move => ?result0 [# Hintt_eq Hintt_rng].
  (* ── subtract pre: w0 slice range — kvec_slice_eq replaces Heq_w0 + allP chain ── *)
  have Heq_w0 : (kvec_unflatten256 _w0).[base{hr} %/ n] = Array256.init (fun i => _w0.[base{hr} + i]).
  + by apply kvec_slice_eq; smt(mldsa65_kvec).
  have Hw0_slice : wpoly_srng gamma2 gamma2 (Array256.init (fun i => _w0.[base{hr} + i])).
  + rewrite -Heq_w0; move: Hw0_srng; rewrite /wpolykvec_srng allP => H.
    move: (H (base{hr} %/ n) _); 1: smt(mldsa65_kvec).
    rewrite /wpoly_srng !allP => H2 j Hj; have := H2 j Hj; smt(mldsa65_gamma2).
  have /= Hresult0_rng' : wpoly_srng (2^31 - gamma1) (2^31 - gamma1) result0.
  + move: Hintt_rng; rewrite/= /wpoly_srng !allP => H j Hj; have := H j Hj;
      smt(mldsa65_gamma1 invntt_obound_fits_for_caddq mldsa65_Eta).
  do split;1..3:by smt(mldsa65_gamma1 mldsa65_gamma2).
  move => ??? result1 Hr1s Hr1v result2 Hr2s Hr2v.
  (* outer = Array1536.init (fun i => if base <= i < base+n then result2.[i-base] else inner.[i])
     inner = Array1536.init (fun i => if base <= i < base+n then result1.[i-base] else w0_minus_cs2{hr}.[i]) *)
  do split.
  - (* Preserve loop invariant for k < base/n:
       kvec_unflatten256_writeback_iE applied twice eliminates the low-level ifF chain *)
    move => Hinfz.
    have [HH1 HH2] := HH _;1:smt().
    have Hslice_eq : forall k, 0 <= k < base{hr} %/ n =>
        (kvec_unflatten256 (Array1536.init (fun (i : int) =>
          if base{hr} <= i < base{hr} + n then result2.[i - base{hr}]
          else (Array1536.init (fun (i0 : int) =>
            if base{hr} <= i0 < base{hr} + n then result1.[i0 - base{hr}]
            else w0_minus_cs2{hr}.[i0])).[i]))).[k] =
        (kvec_unflatten256 w0_minus_cs2{hr}).[k].
    + move => k [hk0 hk1].
      have Hwb2 : (kvec_unflatten256 (Array1536.init (fun i =>
            if base{hr} <= i < base{hr} + n then result2.[i - base{hr}]
            else (Array1536.init (fun i0 =>
              if base{hr} <= i0 < base{hr} + n then result1.[i0 - base{hr}]
              else w0_minus_cs2{hr}.[i0])).[i]))).[k] =
          if k = base{hr} %/ 256 then result2
          else (kvec_unflatten256 (Array1536.init (fun i0 =>
            if base{hr} <= i0 < base{hr} + n then result1.[i0 - base{hr}]
            else w0_minus_cs2{hr}.[i0]))).[k].
      + by apply kvec_unflatten256_writeback_iE; smt(mldsa65_kvec).
      rewrite Hwb2 ifF; 1: smt().
      have Hwb1 : (kvec_unflatten256 (Array1536.init (fun i0 =>
            if base{hr} <= i0 < base{hr} + n then result1.[i0 - base{hr}]
            else w0_minus_cs2{hr}.[i0]))).[k] =
          if k = base{hr} %/ 256 then result1 else (kvec_unflatten256 w0_minus_cs2{hr}).[k].
      + by apply kvec_unflatten256_writeback_iE; smt(mldsa65_kvec).
      by rewrite Hwb1 ifF; smt().
    split; move => k hk1 hk2.
    + have Hk_eq := Hslice_eq k _;1:smt().
      have HH1k := HH1 k _;1:smt().
      by rewrite Hk_eq; exact HH1k.
    + have Hk_eq := Hslice_eq k _;1:smt().
      have HH2k := HH2 k _;1:smt().
      rewrite /lifts_wpolykvec !mapiE 1:/# /= Hk_eq.
      by rewrite -(HH2k) /lifts_wpolykvec !mapiE 1:/# /=; smt(mldsa65_kvec).
  - (* lifts_wpoly of result2 slice = spec[base/n]:
       init_writeback_slice_eq + lifts_wpolykvec_slice replace Hres*_eq and slice_kvec *)
    have Hout2 : Array256.init (fun i => (Array1536.init (fun (i0 : int) =>
        if base{hr} <= i0 < base{hr} + n then result2.[i0 - base{hr}]
        else (Array1536.init (fun (i1 : int) =>
          if base{hr} <= i1 < base{hr} + n then result1.[i1 - base{hr}]
          else w0_minus_cs2{hr}.[i1])).[i0])).[base{hr} + i]) = result2.
    + by apply init_writeback_slice_eq; smt().
    have Hout1 : Array256.init (fun i => (Array1536.init (fun (i0 : int) =>
        if base{hr} <= i0 < base{hr} + n then result1.[i0 - base{hr}]
        else w0_minus_cs2{hr}.[i0])).[base{hr} + i]) = result1.
    + by apply init_writeback_slice_eq; smt().
    rewrite Hout2 Hr2s Hout1 Hr1s Hintt_eq Hbmul_eq.
    rewrite polykvec_sub_iE 1:/#.
    rewrite invnttv_ntt_smul_k 1:/#.
    have Hw0_kvec : lifts_wpoly (Array256.init (fun i => _w0.[base{hr} + i])) =
        (lifts_wpolykvec (kvec_unflatten256 _w0)).[base{hr} %/ 256].
    + by apply lifts_wpolykvec_slice; smt(mldsa65_kvec).
    have Hs2_kvec : lifts_wpoly (Array256.init (fun i => _s2.[base{hr} + i])) =
        (lifts_wpolykvec (kvec_unflatten256 _s2)).[base{hr} %/ 256].
    + by apply lifts_wpolykvec_slice; smt(mldsa65_kvec).
    rewrite -Hw0_kvec -Hs2_kvec.
    by done.
  - (* wpoly_srng: init_writeback_slice_eq gives result2 directly *)
    have Hout2' : Array256.init (fun i => (Array1536.init (fun (i0 : int) =>
        if base{hr} <= i0 < base{hr} + n then result2.[i0 - base{hr}]
        else (Array1536.init (fun (i1 : int) =>
          if base{hr} <= i1 < base{hr} + n then result1.[i1 - base{hr}]
          else w0_minus_cs2{hr}.[i1])).[i0])).[base{hr} + i]) = result2.
    + by apply init_writeback_slice_eq; smt().
    by rewrite Hout2'; exact Hr2v.
wp.
ecall (polynomial____check_infinity_norm_correct
        (Array256.init (fun i => w0_minus_cs2.[base + i]))
        (gamma2 - Beta)).

auto => |> &hr  ??????? ?H H0 H1 H2 H3; split;1:smt().
move => ?? rr Ht Hf.
case (rr = W64.zero) => Hrr /=.
+ (* norm passed: rr = zero, new_incr = zero, update invariant *)
  do split; 1..3: smt().
  + move => k ??; case (k < base{hr} %/ n) => ?;1: by smt(). 
    have : wpoly_infnorm_lt (gamma2 - Beta) (init (fun (i : int) => w0_minus_cs2{hr}.[base{hr} + i])) by smt(W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
    rewrite /wpoly_infnorm_lt  /wpoly_srng !allP /= /kvec_unflatten256 => Hr kk kkb.
    rewrite initiE 1:/# /= get_of_list 1:/# /= nth_sub 1:/# /=.
    have := Hr kk _;1:smt().
    by rewrite initiE 1:/# /= /#.
 + move => k kb ?; case (k < base{hr} %/ n) => ?;1: by smt().
   have -> : k = base{hr} %/ n by smt().
   rewrite -H2 /lifts_wpolykvec mapiE 1:/#;congr;rewrite initiE 1:/# /= tP => j jb.
   rewrite get_of_list 1:/# nth_sub 1:/# initiE 1:/# /= /#.
     split; 1: smt(W64.to_uint_eq pow2_64 W64.to_uintK W64.of_uintK).
   
have Hnwpoly : !wpoly_infnorm_lt (gamma2 - Beta)
    (init (fun (i : int) => w0_minus_cs2{hr}.[base{hr} + i]))
  by apply /negP => Hwpoly; smt(). 
have Hninfnorm : !infnorm_lt
    (lifts_wpoly (init (fun (i : int) => w0_minus_cs2{hr}.[base{hr} + i])))
    (gamma2 - Beta).
+ apply /negP => Hcontra; apply Hnwpoly.
  apply (wpoly_infnorm_unliftE (gamma2 - Beta) ((q-1)%/2) ((q-1)%/2)
           (Array256.init (fun (i : int) => w0_minus_cs2{hr}.[base{hr} + i]))).
  + smt(mldsa65_gamma2).
  + smt().
  + smt().
  + exact H3.
  + exact Hcontra.
apply /negP => Hkvec; apply Hninfnorm; rewrite H2.
move: Hkvec; rewrite /infnorm_lt allP => Hk.
apply (Hk (base{hr} %/ n)).
by rewrite mem_iota /=; smt(mldsa65_kvec).
qed.

lemma __apply_cs2_and_check_norm_ph
      (_w0mc : W32.t Array1536.t) (_w0 : W32.t Array1536.t)
      (_s2 : W32.t Array1536.t) (_c : W32.t Array256.t)
      (_incr : W64.t)
      :
    phoare [ M.__apply_cs2_and_check_norm :
        w0_minus_cs2 = _w0mc /\ w0 = _w0 /\ s2 = _s2 /\
        verifier_challenge = _c /\ infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolykvec_ntt_orng (kvec_unflatten256 _s2) /\
        (* w0 = LowBits(Ay), coefficients in (-gamma2, gamma2] = (-261888, 261888] *)
        wpolykvec_srng (kvec_unflatten256 _w0) (gamma2 - 1) gamma2
        ==>
        (res.`2 = W64.zero \/ res.`2 = W64.one) /\
        (* Biconditional: failure bit is zero iff no prior failure AND
           the abstract cs2-norm check holds. *)
        (res.`2 = W64.zero <=>
           _incr = W64.zero /\
           PolyKVec.infnorm_lt
             (lifts_wpolykvec (kvec_unflatten256 _w0) -
              PolyKVec.invnttv (PolyKVec.ntt_smul
                (lifts_wpoly _c)
                (lifts_wpolykvec (kvec_unflatten256 _s2))))
             (gamma2 - Beta)) /\
        (res.`2 = W64.zero =>
           (* ||w0 - cs2||_inf < gamma2 - Beta = 261692 *)
           wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 res.`1) /\
           lifts_wpolykvec (kvec_unflatten256 res.`1) =
             (lifts_wpolykvec (kvec_unflatten256 _w0)) -
             (PolyKVec.invnttv (PolyKVec.ntt_smul
               (lifts_wpoly _c)
               (lifts_wpolykvec (kvec_unflatten256 _s2)))))
    ] = 1%r.
proof.
by conseq __apply_cs2_and_check_norm_ll
          (__apply_cs2_and_check_norm_correct _w0mc _w0 _s2 _c _incr).
qed.

(* ================================================================== *)
(* __apply_ct0_and_check_norm                                          *)
(* Called second; incr = result of cs2 check (0 or 1).               *)
(* Computes ct0 per row (K=6); checks infnorm < gamma2.              *)
(* If check passes: conditionally adds ct0 to w0_minus_cs2.           *)
(* Spec: ct0 = invnttv (ntt_smul ch t0h); output = w0mc + ct0        *)
(* Threshold: gamma2 = (q-1)/32 = 261888                              *)
(* ================================================================== *)

lemma __apply_ct0_and_check_norm_ll : islossless M.__apply_ct0_and_check_norm.
proof.
proc.
wp; while (0 <= base <= 6 * n /\ base %% n = 0) (6*n - base); last by auto => /#.
move => ?.
wp; conseq (: true==>true); 1: by smt().
seq 5 : true.
+ by auto.
+ wp; call polynomial____check_infinity_norm_ll.
  wp; call polynomial__reduce32_ll.
  wp; call polynomial__invert_ntt_montgomery_ll.
  wp; call polynomial__pointwise_montgomery_multiply_and_reduce_ll.
  by auto.
+ if; last by auto.
  wp; call polynomial__add_ll.
  by auto.

+ hoare; by auto.
+ by auto.
qed.

lemma __apply_ct0_and_check_norm_correct
      (_r : W32.t Array1536.t) (_w0mc : W32.t Array1536.t)
      (_t0 : W32.t Array1536.t) (_c : W32.t Array256.t)
      (_incr : W64.t)
      :
    hoare [ M.__apply_ct0_and_check_norm :
        w0_minus_cs2_plus_ct0 = _r /\ w0_minus_cs2 = _w0mc /\
        t0 = _t0 /\ verifier_challenge = _c /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolykvec_ntt_orng (kvec_unflatten256 _t0) /\
        (* only needed when _incr = 0 (loop runs): w0mc passed cs2 norm check *)
        (_incr = W64.zero =>
          wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 _w0mc))
        ==>
        (res.`2 = W64.zero \/ res.`2 = W64.one) /\
        (res.`2 = W64.zero <=>
           _incr = W64.zero /\
           PolyKVec.infnorm_lt
             (PolyKVec.invnttv (PolyKVec.ntt_smul
                (lifts_wpoly _c)
                (lifts_wpolykvec (kvec_unflatten256 _t0))))
             gamma2) /\
        (res.`2 = W64.zero =>
           let ct0 = PolyKVec.invnttv (PolyKVec.ntt_smul
                       (lifts_wpoly _c)
                       (lifts_wpolykvec (kvec_unflatten256 _t0))) in
           wpolykvec_srng (kvec_unflatten256 res.`1) (2*gamma2 - Beta - 2) (2*gamma2 - Beta - 2) /\
           lifts_wpolykvec (kvec_unflatten256 res.`1) =
             (lifts_wpolykvec (kvec_unflatten256 _w0mc)) + ct0)
    ].
proof.
have kvec_val := mldsa65_kvec.
have gamma2_val := mldsa65_gamma2.
have tau_val  := mldsa65_tau.
have eta_val  := mldsa65_Eta.
proc => /=.
case (infinity_norm_check_result <> zero).
+ rcondt ^if; 1: by auto.
  rcondf ^while; 1: by auto.
  by auto => /#.
conseq (: _ ==>
  (infinity_norm_check_result = zero \/ infinity_norm_check_result = one) /\
  (infinity_norm_check_result = zero <=>
   PolyKVec.infnorm_lt
     (PolyKVec.invnttv (PolyKVec.ntt_smul
        (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _t0))))
     gamma2) /\
  (infinity_norm_check_result = zero =>
   wpolykvec_srng (kvec_unflatten256 w0_minus_cs2_plus_ct0) (2*gamma2 - Beta - 2) (2*gamma2 - Beta - 2) /\
   lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0) =
     lifts_wpolykvec (kvec_unflatten256 _w0mc) +
     PolyKVec.invnttv (PolyKVec.ntt_smul
       (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _t0)))));
 1: by move => |> &hr ?? infncr rr *; rewrite H_incr /=;
       smt(W64.to_uint_eq pow2_64 W64.to_uintK W64.of_uintK).
rcondf ^if; 1: by auto.
while (#{/~_incr}{~infinity_norm_check_result}{~w0_minus_cs2_plus_ct0}pre /\
       _incr = W64.zero /\
       (infinity_norm_check_result = zero \/ infinity_norm_check_result = one) /\
       0 <= base <= 6*n /\ base %% n = 0 /\
       (infinity_norm_check_result <> zero => base = 6*n) /\
       wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 _w0mc) /\
       (infinity_norm_check_result <> zero =>
          ! PolyKVec.infnorm_lt
              (PolyKVec.invnttv (PolyKVec.ntt_smul
                 (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _t0))))
              gamma2) /\
       (infinity_norm_check_result = zero =>
         let ct0 = PolyKVec.invnttv (PolyKVec.ntt_smul
                     (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _t0))) in
         (forall k, 0 <= k < base %/ n =>
           wpoly_srng (gamma2 - Beta - 1 + gamma2 - 1)
                      (gamma2 - Beta - 1 + gamma2 - 1)
                      (kvec_unflatten256 w0_minus_cs2_plus_ct0).[k]) /\
         (forall k, 0 <= k < base %/ n =>
           infnorm_lt ct0.[k] gamma2) /\
         (forall k, 0 <= k < base %/ n =>
           (lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0)).[k] =
           (lifts_wpolykvec (kvec_unflatten256 _w0mc)).[k] &+ ct0.[k]))
      ); last first.
+ auto => /> ???; split; 1: smt().
  move => bs r ????????? H_cond; do split.
  (* biconditional ⇒: r = zero => infnorm_lt ct0_spec gamma2 *)
  + move => Hzero.
    have [# H1 H2 H3] := H_cond Hzero.
    rewrite /infnorm_lt allP => k Hk.
    have := H2 k _; 1: smt(mem_iota mldsa65_kvec).
    by rewrite /infnorm_lt.
  (* biconditional ⇐: infnorm_lt ... gamma2 => r = zero *)
  + by smt().
  (* r = zero => wpolykvec_srng ... /\ lifts = ... *)
  + move => Hinflt.
    have [# H1 H2 H3] := H_cond Hinflt.
    split.
    + rewrite /wpolykvec_srng allP => k kb.
      have := H1 k _; 1: smt(mldsa65_kvec).
      by smt(mldsa65_gamma2).
    + apply KArray.tP => ii iib.
      have -> := H3 ii _; 1: smt().
      by rewrite polykvec_add_iE 1:/#.
    
(* ── Loop body: one column at index base %/ n ──────────────────────── *)
(* Jasmin: basemul(t0_slice,c) → invNTT → reduce32 → check_infnorm(ct0,gamma2)
           → if(pass){ add(w0mc_slice, w0mc_slice, ct0); writeback }
           → base += 256 → if(fail){ base = 6*n }                           *)

(* ══ Phase 1: compute ct0 via ecall chain ══ *)
seq 3 : (#pre /\
    lifts_wpoly ct0 =
      (PolyKVec.invnttv (PolyKVec.ntt_smul
         (lifts_wpoly _c)
         (lifts_wpolykvec (kvec_unflatten256 _t0)))).[base %/ n] /\
    wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2) ct0).
+ ecall (polynomial__reduce32_correct ct0).
  ecall (polynomial__invert_ntt_montgomery_correct ct0).
  ecall (polynomial__pointwise_montgomery_multiply_and_reduce_correct
           ct0
           (Array256.init (fun i => t0.[base + i]))
           verifier_challenge).
  auto => |> &hr *.
  do split => /=.
  - (* t0 slice bmul_irng — kvec_slice_eq replaces inline Array256.tP proof *)
    have Ht0_ntt : wpolykvec_ntt_orng (kvec_unflatten256 _t0) by smt().
    have Heq_t0 : (kvec_unflatten256 _t0).[base{hr} %/ n] = Array256.init (fun i => _t0.[base{hr} + i]).
    + by apply kvec_slice_eq; smt(mldsa65_kvec).
    rewrite -Heq_t0.
    move: (wpolykvec_ntt_orng_bmul_irng _ Ht0_ntt); rewrite /wpolykvec_bmul_irng allP => H; apply H; smt(mldsa65_kvec).
  - by smt(wpoly_ntt_orng_bmul_irng).
  move => Hbmul_t0 Hbmul_c result [# Hbmul_eq Hbmul_rng].
  split; 1: by exact (wpoly_bmul_orng_intt_irng result Hbmul_rng).
  move => ?result0 [# Hintt_eq Hintt_rng].
  move => result1 [# Hred_eq Hred_rng].
  rewrite Hred_eq Hintt_eq Hbmul_eq.
  rewrite invnttv_ntt_smul_k 1:/#.
  by rewrite (lifts_wpolykvec_slice _t0 base{hr}) 1:/# 1:/#.

(* ══ Phase 2+3: check_infnorm + conditional add + base update ══ *)
(* wp absorbs: base += n; if(infnorm!=0) base = 6*n *)
wp.
(* Remaining: (1) check_infnorm(ct0, gamma2)
              (2) infnorm_result <- infnorm_result  [no-op]
              (3) if (infnorm_result = 0) { add(w0mc_slice, ct0); writeback }
   if. fails here because (1) is a call, not an if.
   seq 2 splits off (1)+(2), leaving (3) alone so if. can work. *)
seq 2 : (
  _incr = zero /\
  (w0_minus_cs2 = _w0mc /\
   t0 = _t0 /\
   verifier_challenge = _c /\
   wpoly_ntt_orng _c /\
   wpolykvec_ntt_orng (kvec_unflatten256 _t0)) /\
  0 <= base /\ base < 6 * n /\
  base %% n = 0 /\
  lifts_wpoly ct0 =
    (PolyKVec.invnttv (PolyKVec.ntt_smul
      (lifts_wpoly _c)
      (lifts_wpolykvec (kvec_unflatten256 _t0)))).[base %/ n] /\
  wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2) ct0 /\
  (* check_infnorm result: zero iff infnorm_lt holds *)
  (wpoly_infnorm_lt gamma2 ct0 => infinity_norm_check_result = W64.zero) /\
  (!wpoly_infnorm_lt gamma2 ct0 => infinity_norm_check_result = W64.one) /\
  (* w0mc range: needed for add precondition in then-branch *)
  wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 _w0mc) /\
  (* previous columns: infnorm_lt and algebraic equality hold for k < base/n *)
  (let ct0_spec = PolyKVec.invnttv (PolyKVec.ntt_smul
                    (lifts_wpoly _c)
                    (lifts_wpolykvec (kvec_unflatten256 _t0))) in
   (forall k, 0 <= k < base %/ n =>
     wpoly_srng (gamma2 - Beta - 1 + gamma2 - 1)
                (gamma2 - Beta - 1 + gamma2 - 1)
                (kvec_unflatten256 w0_minus_cs2_plus_ct0).[k]) /\
   (forall k, 0 <= k < base %/ n => infnorm_lt ct0_spec.[k] gamma2) /\
   (forall k, 0 <= k < base %/ n =>
     (lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0)).[k] =
     (lifts_wpolykvec (kvec_unflatten256 _w0mc)).[k] &+ ct0_spec.[k]))
).
- (* ── Goal 1: { pre } check_infnorm(ct0, gamma2); no-op { intermediate_cond } ── *)
  wp. (* absorb no-op backward *)
  ecall (polynomial____check_infinity_norm_correct ct0 gamma2).
  auto => |> &hr *; split;1: by smt(mldsa65_gamma2).
  move => ??rr  Hpass Hfail.
  (* wpolykvec_infnorm_lt is now a direct invariant conjunct, absorbed by |> into context.
     do split produces 3 forall goals (wpoly_srng, infnorm_lt, algebra for k < base/n).
     All closed by smt() from the unnamed (infnorm=zero => ...) invariant hypothesis:
     infnorm=zero follows from base < 1536 + (infnorm≠zero => base=1536). *)
  do split; 1..3: smt().

- (* ── Goal 2: { intermediate_cond } if(infnorm=0){ add; writeback } { post_wp } ── *)
  (* if. now works: first instruction is the if-block *)
  if.
  + (* Then-branch: infnorm_result = zero → add + writeback *)
    wp. (* absorb writeback: w0mc_plus_ct0 <- Array1536.init(...) *)
    ecall (polynomial__add_correct
             (Array256.init (fun i => w0_minus_cs2_plus_ct0.[base + i]))
             (Array256.init (fun i => w0_minus_cs2.[base + i]))
             ct0
             (gamma2 - Beta - 1) (gamma2 - 1)).
    auto => |> &hr *.
    (* From intermediate_cond + infnorm_result = zero:
       derive wpoly_infnorm_lt gamma2 ct0 via contrapositive of Hfail *)
    have Hct0_infnorm : wpoly_infnorm_lt gamma2 ct0{hr} by smt(W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
    have Hct0_eq : lifts_wpoly ct0{hr} =
        (PolyKVec.invnttv (PolyKVec.ntt_smul
          (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _t0)))).[base{hr} %/ n] by smt().
    do split.
    - (* add lhs range: wpoly_srng (gamma2-Beta-1) ... w0mc_slice *)
      have Hw0mc_inflt : wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 _w0mc) by smt().
      have Heq_slice : (kvec_unflatten256 _w0mc).[base{hr} %/ n] =
          Array256.init (fun i => _w0mc.[base{hr} + i]).
      + by apply kvec_slice_eq; smt(mldsa65_kvec).
      rewrite /wpoly_srng allP => j jb.
      move: Hw0mc_inflt; rewrite /wpolykvec_infnorm_lt /wpolykvec_srng allP => H.
      move: (H (base{hr} %/ n) _); 1: smt(mldsa65_kvec).
      rewrite Heq_slice /wpoly_srng allP => Hk.
      have := Hk j _; 1: smt().
      by rewrite initiE 1:/# /=; smt().
    - (* add rhs range: wpoly_srng (gamma2-1) ... ct0 from infnorm_lt *)
      rewrite /wpoly_srng allP => j jb.
      move: Hct0_infnorm; rewrite /wpoly_infnorm_lt /wpoly_srng allP => H.
      by have := H j _; 1: smt(); smt().
    - by smt(mldsa65_gamma2).  (* overflow: (gamma2-Beta-1) + (gamma2-1) < 2^31 *)
    move => _ _ _ add_result Hadd_eq Hadd_rng.
    do split; 1..3: by smt().
    + (* range of w0mc_plus_ct0 for all k < (base+n)/n *)
      move => k kb ?.
      case (k < base{hr} %/ n) => Hlt.
      - (* k < base/n: writeback does not touch column k, use old invariant *)
        have Hmod : base{hr} %% 256 = 0 by smt().
        have Hkvec : 0 <= k < kvec by smt(mldsa65_kvec).
        have Hwb := kvec_unflatten256_writeback_iE w0_minus_cs2_plus_ct0{hr} add_result base{hr} k Hmod Hkvec.
        by rewrite Hwb ifF; smt().
      - (* k = base/n: range comes from Hadd_rng + writeback_iE *)
        have -> : k = base{hr} %/ n by smt().
        rewrite /n.
        have Hmod2 : base{hr} %% 256 = 0 by smt().
        have Hkvec2 : 0 <= base{hr} %/ 256 < kvec by smt(mldsa65_kvec).
        have Hwb := kvec_unflatten256_writeback_iE w0_minus_cs2_plus_ct0{hr} add_result base{hr} (base{hr} %/ 256) Hmod2 Hkvec2.
        by rewrite Hwb /=; smt().
    + (* infnorm_lt for new column k = base/n *)
      move => k ??.
      case (k < base{hr} %/ n) => ?; 1: by smt().
      have -> : k = base{hr} %/ n by smt().
      rewrite -Hct0_eq.
      apply (wpoly_infnorm_liftE gamma2 ct0{hr} _ Hct0_infnorm).
      smt(mldsa65_gamma2).
    + (* algebra for all k < (base+n)/n *)
      move => k kb ?.
      case (k < base{hr} %/ n) => Hlt.
      - (* k < base/n: writeback does not touch column k *)
        have Hmod : base{hr} %% 256 = 0 by smt().
        have Hkvec : 0 <= k < kvec by smt(mldsa65_kvec).
        have Hwb := kvec_unflatten256_writeback_iE w0_minus_cs2_plus_ct0{hr} add_result base{hr} k Hmod Hkvec.
        have Hk_eq : (kvec_unflatten256 (Array1536.init (fun i =>
              if base{hr} <= i < base{hr} + n then add_result.[i - base{hr}]
              else w0_minus_cs2_plus_ct0{hr}.[i]))).[k] =
            (kvec_unflatten256 w0_minus_cs2_plus_ct0{hr}).[k]
          by rewrite Hwb ifF; smt().
        have /= HH2k : (lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0{hr})).[k] =
            (lifts_wpolykvec (kvec_unflatten256 _w0mc)).[k] &+
            (PolyKVec.invnttv (PolyKVec.ntt_smul (lifts_wpoly _c)
              (lifts_wpolykvec (kvec_unflatten256 _t0)))).[k]
          by smt().
        by rewrite -HH2k /lifts_wpolykvec mapiE 1:/# mapiE 1:/# /= Hk_eq.
         
      - (* k = base/n: writeback_iE + Hadd_eq + lifts_wpolykvec_slice + Hct0_eq *)
        have -> : k = base{hr} %/ n by smt().
        rewrite /lifts_wpolykvec mapiE 1:/# /=.
        rewrite (kvec_unflatten256_writeback_iE _ add_result base{hr} (base{hr} %/ 256)) 1:/#;
                1:smt(mldsa65_kvec).
        rewrite Hadd_eq (lifts_wpolykvec_slice _w0mc base{hr}) 1:/#; 1:smt(mldsa65_kvec).
        by rewrite Hct0_eq.
  + (* Else-branch: infnorm_result != zero → no add, base becomes 6*n in post *)
    auto => |> &hr  Hbin0 Hbin1 Hbase0 Hbase1 Hbasemod Hct0_eq Hct0_rng Hpass Hfail
            Hw0mc_inflt Hprev_srng Hprev_inf Hprev_eq Hne0.
    do split; 1: smt(W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
    have Hnwpoly : !wpoly_infnorm_lt gamma2 ct0{hr}
      by apply /negP => Hwpoly; smt().
    have Hninfnorm : !infnorm_lt (lifts_wpoly ct0{hr}) gamma2.
    + apply /negP => Hcontra; apply Hnwpoly.
      apply (wpoly_infnorm_unliftE gamma2 ((q-1)%/2) ((q-1)%/2) ct0{hr}).
      + smt(mldsa65_gamma2).
      + smt().
      + smt().
      + smt().
      + exact Hcontra.
    apply /negP => Hkvec; apply Hninfnorm; rewrite Hct0_eq.
    move: Hkvec; rewrite /infnorm_lt allP => Hk.
    apply (Hk (base{hr} %/ n)).
    by rewrite mem_iota /=; smt(mldsa65_kvec).
qed.

lemma __apply_ct0_and_check_norm_ph
      (_r : W32.t Array1536.t) (_w0mc : W32.t Array1536.t)
      (_t0 : W32.t Array1536.t) (_c : W32.t Array256.t)
      (_incr : W64.t)
      :
    phoare [ M.__apply_ct0_and_check_norm :
        w0_minus_cs2_plus_ct0 = _r /\ w0_minus_cs2 = _w0mc /\
        t0 = _t0 /\ verifier_challenge = _c /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolykvec_ntt_orng (kvec_unflatten256 _t0) /\
        (_incr = W64.zero =>
          wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 _w0mc))
        ==>
        (res.`2 = W64.zero \/ res.`2 = W64.one) /\
        (* Biconditional: failure bit is zero iff no prior failure AND
           the abstract ct0-norm check holds. *)
        (res.`2 = W64.zero <=>
           _incr = W64.zero /\
           PolyKVec.infnorm_lt
             (PolyKVec.invnttv (PolyKVec.ntt_smul
                (lifts_wpoly _c)
                (lifts_wpolykvec (kvec_unflatten256 _t0))))
             gamma2) /\
        (res.`2 = W64.zero =>
           let ct0 = PolyKVec.invnttv (PolyKVec.ntt_smul
                       (lifts_wpoly _c)
                       (lifts_wpolykvec (kvec_unflatten256 _t0))) in
           (* Tightest word-level range from add: wpolykvec_infnorm_lt (gamma2-Beta)
              on w0mc plus wpoly_infnorm_lt gamma2 on ct0. *)
           wpolykvec_srng (kvec_unflatten256 res.`1) (2*gamma2 - Beta - 2) (2*gamma2 - Beta - 2) /\
           lifts_wpolykvec (kvec_unflatten256 res.`1) =
             (lifts_wpolykvec (kvec_unflatten256 _w0mc)) + ct0)
    ] = 1%r.
proof.
by conseq __apply_ct0_and_check_norm_ll (__apply_ct0_and_check_norm_correct _r _w0mc _t0 _c _incr).
qed.


lemma __compute_z_and_check_norm_ll : islossless M.__compute_z_and_check_norm.
proof.
proc.
wp; while (0 <= base <= 5 * n /\ base %% n = 0) (5*n - base); last by auto => /#.
move => ?.
wp; call polynomial____check_infinity_norm_ll.
wp; call __compute_signer_response_element_ll.
by auto => /#.
qed.

lemma __compute_z_and_check_norm_correct
      (_s1 : W32.t Array1280.t) (_c : W32.t Array256.t)
      (_mask : W32.t Array1280.t) (_z0 : W32.t Array1280.t)
      (_incr : W64.t)
      :
    hoare [ M.__compute_z_and_check_norm :
        s1 = _s1 /\ verifier_challenge = _c /\
        mask = _mask /\ signer_response = _z0 /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolylvec_ntt_orng (lvec_unflatten256 _s1) /\
        (* only needed when _incr = 0 (loop runs): mask from ExpandMask *)
        (_incr = W64.zero =>
          wpolylvec_srng (lvec_unflatten256 _mask) (gamma1 - 1) gamma1)
        ==>
        (res.`2 = W64.zero \/ res.`2 = W64.one) /\
        (* Biconditional: failure bit is zero iff no prior failure AND
           the abstract z-norm check holds. *)
        (res.`2 = W64.zero <=>
           _incr = W64.zero /\
           PolyLVec.infnorm_lt
             ((lifts_wpolylvec (lvec_unflatten256 _mask)) +
              (PolyLVec.invnttv (PolyLVec.ntt_smul
                (lifts_wpoly _c)
                (lifts_wpolylvec (lvec_unflatten256 _s1)))))
             (gamma1 - Beta)) /\
        (_incr = W64.zero =>
           res.`2 = W64.zero =>
           (* ||z||_inf < gamma1 - Beta = 524092 *)
           wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 res.`1) /\
           lifts_wpolylvec (lvec_unflatten256 res.`1) =
             (lifts_wpolylvec (lvec_unflatten256 _mask)) +
             (PolyLVec.invnttv (PolyLVec.ntt_smul
               (lifts_wpoly _c)
               (lifts_wpolylvec (lvec_unflatten256 _s1)))) /\
           wpolylvec_srng (lvec_unflatten256 res.`1) (gamma1 - 1) gamma1)
    ].
proof.
have lvec_val  := mldsa65_lvec.
have gamma1_val := mldsa65_gamma1.
have tau_val   := mldsa65_tau.
have eta_val   := mldsa65_Eta.
proc => /=.
case (infinity_norm_check_result <> zero).
+ rcondt ^if; 1: by auto.
  rcondf ^while; 1: by auto.
  by auto => /#.

conseq (: _ ==>
  (infinity_norm_check_result = zero \/ infinity_norm_check_result = one) /\
  (infinity_norm_check_result = zero <=>
   PolyLVec.infnorm_lt
     (lifts_wpolylvec (lvec_unflatten256 _mask) +
      PolyLVec.invnttv (PolyLVec.ntt_smul
        (lifts_wpoly _c) (lifts_wpolylvec (lvec_unflatten256 _s1))))
     (gamma1 - Beta)) /\
  (infinity_norm_check_result = zero =>
  (wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 signer_response) /\
   lifts_wpolylvec (lvec_unflatten256 signer_response) =
     lifts_wpolylvec (lvec_unflatten256 _mask) +
     PolyLVec.invnttv (PolyLVec.ntt_smul
       (lifts_wpoly _c) (lifts_wpolylvec (lvec_unflatten256 _s1))) /\
   wpolylvec_srng (lvec_unflatten256 signer_response) (gamma1 - 1) gamma1)));
 1: by move => |> &hr ?? infncr rr *; smt(W64.to_uint_eq pow2_64 W64.to_uintK W64.of_uintK).
rcondf ^if; 1: by auto.
while (#{/~_incr}{~infinity_norm_check_result}{~signer_response}pre /\
       (infinity_norm_check_result = zero \/ infinity_norm_check_result = one) /\
       0 <= base <= 5*n /\ base %% n = 0 /\
       (infinity_norm_check_result <> zero => base = 5*n) /\
       wpolylvec_srng (lvec_unflatten256 _mask) (gamma1 - 1) gamma1 /\
       (infinity_norm_check_result <> zero =>
          ! PolyLVec.infnorm_lt
              (lifts_wpolylvec (lvec_unflatten256 _mask) +
               PolyLVec.invnttv (PolyLVec.ntt_smul
                 (lifts_wpoly _c) (lifts_wpolylvec (lvec_unflatten256 _s1))))
              (gamma1 - Beta)) /\
       (infinity_norm_check_result = zero =>
         (forall k, 0 <= k < base %/ n =>
           wpoly_srng (gamma1 - Beta - 1) (gamma1 - Beta - 1)
                      (lvec_unflatten256 signer_response).[k]) /\
         (forall k, 0 <= k < base %/ n =>
           (lifts_wpolylvec (lvec_unflatten256 signer_response)).[k] =
           (lifts_wpolylvec (lvec_unflatten256 _mask) +
            PolyLVec.invnttv (PolyLVec.ntt_smul
              (lifts_wpoly _c) (lifts_wpolylvec (lvec_unflatten256 _s1)))).[k]))
      ); last first.
(* ── Loop exit ────────────────────────────────────────────────── *)
+ auto => /> ???; split; 1: smt().
  move => bs inr srs ??????? H_fail H_srng; do split; 2: smt().
  (* biconditional ⇒: srs = zero => infnorm_lt *)
  + move => Hzero.
    have [# H1 H2] := H_srng Hzero.
    have Hwplv : wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 srs)
      by rewrite /wpolylvec_infnorm_lt /wpolylvec_srng LArray.allP => *; smt(mldsa65_lvec).
    have Hleq : lifts_wpolylvec (lvec_unflatten256 srs) =
        lifts_wpolylvec (lvec_unflatten256 _mask) +
        PolyLVec.invnttv (PolyLVec.ntt_smul
          (lifts_wpoly _c) (lifts_wpolylvec (lvec_unflatten256 _s1)))
      by apply LArray.tP => *; smt(mldsa65_lvec).
    rewrite -Hleq.
    by apply (wpolylvec_infnorm_liftE (gamma1 - Beta)); smt(mldsa65_gamma1).
  (* conditional: srs = zero => triple *)
  + move => Hzero.
    have [# H1 H2] := H_srng Hzero.
    do split.
    + rewrite /wpolylvec_infnorm_lt /wpolylvec_srng LArray.allP => i ib.
      by have := H1 i _; smt(mldsa65_lvec).
    + apply LArray.tP => ii iib.
      have -> := H2 ii _;1:smt(mldsa65_lvec).
      by rewrite polylvec_add_iE 1:/#.
    + rewrite /wpolylvec_srng LArray.allP => ii iib.
      have := H1 ii _;1:smt(mldsa65_lvec).
      rewrite /wpoly_srng !allP => Hrng j jb.
      by have := Hrng j _; smt().

(* ── Loop body: one column at index base %/ n ──────────────────── *)
(* Jasmin: compute_signer_response_element(signer_response_element, s1_slice, c, mask_slice)
           → writeback signer_response[base..base+n] = result
           → check_infinity_norm(result, gamma1-Beta)
           → base += n; if(fail){ base = 5*n }                    *)

(* ══ Phase 1: compute z via ecall + writeback ══ *)
seq 2 : (#pre /\
    lifts_wpoly (Array256.init (fun i => signer_response.[base + i])) =
      (lifts_wpolylvec (lvec_unflatten256 _mask) +
       PolyLVec.invnttv (PolyLVec.ntt_smul
         (lifts_wpoly _c)
         (lifts_wpolylvec (lvec_unflatten256 _s1)))).[base %/ n] /\
    wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2)
               (Array256.init (fun i => signer_response.[base + i]))).
+ wp.
  ecall (__compute_signer_response_element_correct
           (Array256.init (fun i => s1.[base + i]))
           verifier_challenge
           (Array256.init (fun i => mask.[base + i]))
           (Array256.init (fun i => signer_response.[base + i]))).
  auto => |> &hr *.
  do split => /=.
  - (* s1 slice ntt_orng — convert slice to component, then extract from vector predicate *)
    have Hs1_ntt : wpolylvec_ntt_orng (lvec_unflatten256 _s1) by smt().
    have Heq_s1 : (lvec_unflatten256 _s1).[base{hr} %/ n] = Array256.init (fun i => _s1.[base{hr} + i]).
    + by apply lvec_slice_eq; smt(mldsa65_lvec).
    rewrite -Heq_s1.
    by move: Hs1_ntt; rewrite /wpolylvec_ntt_orng LArray.allP => H; apply H; smt(mldsa65_lvec).
  - (* mask slice range: wpoly_srng gamma1 gamma1 from wpolylvec_srng (gamma1-1) gamma1 *)
    have Hmask_rng : wpolylvec_srng (lvec_unflatten256 _mask) (gamma1 - 1) gamma1 by smt().
    have Heq_mask : (lvec_unflatten256 _mask).[base{hr} %/ n] = Array256.init (fun i => _mask.[base{hr} + i]).
    + by apply lvec_slice_eq; smt(mldsa65_lvec).
    rewrite -Heq_mask.
    move: Hmask_rng; rewrite /wpolylvec_srng LArray.allP => H.
    have := H (base{hr} %/ n) _; 1: smt(mldsa65_lvec).
    rewrite /wpoly_srng !allP => Hk j jb.
    by have := Hk j _; smt().
  move => _ _ result Hres_eq Hres_rng.
  (* The writeback slice (init (fun i => (init ...).[base+i])) simplifies to result *)
  have Hwb_slice : (Array256.init (fun i =>
      (Array1280.init (fun i0 =>
        if base{hr} <= i0 < base{hr} + n then result.[i0 - base{hr}]
        else signer_response{hr}.[i0])).[base{hr} + i])) = result.
  + apply Array256.tP => j jb.
    rewrite Array256.initiE 1:/# /= Array1280.initiE; by smt().
  do split.
  - (* invariant: old columns preserved for k < base/n *)
    move => ?; split.
    + move => k kb Hlt.
      have Hmod : base{hr} %% 256 = 0 by smt().
      have Hlvec : 0 <= k < lvec by smt(mldsa65_lvec).
      have /= Hwb := lvec_unflatten256_writeback_iE signer_response{hr} result base{hr} k Hmod Hlvec.
      by rewrite Hwb ifF; smt().
    + move => k kb Hlt.
      have Hmod : base{hr} %% 256 = 0 by smt().
      have Hlvec : 0 <= k < lvec by smt(mldsa65_lvec).
      have /= Hwb := lvec_unflatten256_writeback_iE signer_response{hr} result base{hr} k Hmod Hlvec.
      have Hk_eq : (lvec_unflatten256 (Array1280.init (fun i =>
            if base{hr} <= i < base{hr} + n then result.[i - base{hr}]
            else signer_response{hr}.[i]))).[k] =
          (lvec_unflatten256 signer_response{hr}).[k]
        by rewrite Hwb ifF; smt().
      have /= HH2k : (lifts_wpolylvec (lvec_unflatten256 signer_response{hr})).[k] =
          (lifts_wpolylvec (lvec_unflatten256 _mask) +
           invnttv (ntt_smul (lifts_wpoly _c) (lifts_wpolylvec (lvec_unflatten256 _s1)))).[k]
        by smt().
      by rewrite -HH2k /lifts_wpolylvec mapiE 1:/# mapiE 1:/# /= Hk_eq.
  - (* new column: lifts = spec *)
    rewrite Hwb_slice Hres_eq.
    rewrite (lifts_wpolylvec_slice _mask base{hr}) 1:/#; 1: smt(mldsa65_lvec).
    rewrite (lifts_wpolylvec_slice _s1 base{hr}) 1:/#; 1: smt(mldsa65_lvec).
    by rewrite polylvec_add_iE 1:/# -PolyLVec.invnttv_ntt_smul_k 1:/#.
  - (* new column: range *)
    by rewrite Hwb_slice.

(* ══ Phase 2: check_infnorm + base update ══ *)
wp.
ecall (polynomial____check_infinity_norm_correct
        (Array256.init (fun i => signer_response.[base + i]))
        (gamma1 - Beta)).
auto => |> &hr *; do split.
+ rewrite /(`<<`) mldsa65_gamma1 /= /#.
+ rewrite /(`<<`) mldsa65_gamma1 /= /#.
move => ?? rr Hpass Hfail.
case (rr = W64.zero) => Hrr /=.
+ (* norm passed: rr = zero, update invariant *)
  do split; 1..3: by smt().
  + move => k kbl kbh.
    case (k < base{hr} %/ n) => ?; 1: by smt().
    have -> : k = base{hr} %/ n by smt().
    have Hinfnorm : wpoly_infnorm_lt (gamma1 - Beta)
      (Array256.init (fun i => signer_response{hr}.[base{hr} + i]))
      by smt(W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
    move: Hinfnorm; rewrite /wpoly_infnorm_lt /wpoly_srng !allP => Hr j jb.
    have /= := Hr j _; 1: smt().
    by rewrite /lvec_unflatten256 initiE 1:/# /= initiE 1:/# /= get_of_list 1:/# /= nth_sub 1:/# /= ; smt().
  + move => k kb ?; case (k < base{hr} %/ n) => ?; 1: by smt().
    have -> : k = base{hr} %/ n by smt().
    rewrite -(lifts_wpolylvec_slice signer_response{hr} base{hr}) 1:/#; 1: smt(mldsa65_lvec).
    by smt().
(* norm failed: rr = one, propagate (!infnorm_lt) *)
have Hnwpoly : !wpoly_infnorm_lt (gamma1 - Beta)
    (Array256.init (fun i => signer_response{hr}.[base{hr} + i]))
  by apply /negP => Hwpoly; smt().
have Hninfnorm : !infnorm_lt
    (lifts_wpoly (Array256.init (fun i => signer_response{hr}.[base{hr} + i])))
    (gamma1 - Beta).
+ apply /negP => Hcontra; apply Hnwpoly.
  apply (wpoly_infnorm_unliftE (gamma1 - Beta) ((q-1)%/2) ((q-1)%/2)
           (Array256.init (fun i => signer_response{hr}.[base{hr} + i]))).
  + smt(mldsa65_gamma1).
  + smt().
  + smt().
  + by smt().
  + exact Hcontra.

split; 1: smt().
apply /negP => Hkvec; apply Hninfnorm.
move: Hkvec; rewrite /PolyLVec.infnorm_lt allP => Hk.
have /= Hk_at := Hk (base{hr} %/ n) _; 1: by rewrite mem_iota /=; smt(mldsa65_lvec).
have Heq : lifts_wpoly (init (fun (i : int) => signer_response{hr}.[base{hr} + i])) =
    (lifts_wpolylvec (lvec_unflatten256 _mask) +
     invnttv (ntt_smul (lifts_wpoly _c) (lifts_wpolylvec (lvec_unflatten256 _s1)))).[base{hr} %/ n]
  by smt().
by rewrite /infnorm_lt Heq; exact Hk_at.
qed.

lemma __compute_z_and_check_norm_ph
      (_s1 : W32.t Array1280.t) (_c : W32.t Array256.t)
      (_mask : W32.t Array1280.t) (_z0 : W32.t Array1280.t)
      (_incr : W64.t)
      :
    phoare [ M.__compute_z_and_check_norm :
        s1 = _s1 /\ verifier_challenge = _c /\
        mask = _mask /\ signer_response = _z0 /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolylvec_ntt_orng (lvec_unflatten256 _s1) /\
        (_incr = W64.zero =>
          wpolylvec_srng (lvec_unflatten256 _mask) (gamma1 - 1) gamma1)
        ==>
        (res.`2 = W64.zero \/ res.`2 = W64.one) /\
        (* Biconditional: failure bit is zero iff no prior failure AND
           the abstract z-norm check holds. *)
        (res.`2 = W64.zero <=>
           _incr = W64.zero /\
           PolyLVec.infnorm_lt
             ((lifts_wpolylvec (lvec_unflatten256 _mask)) +
              (PolyLVec.invnttv (PolyLVec.ntt_smul
                (lifts_wpoly _c)
                (lifts_wpolylvec (lvec_unflatten256 _s1)))))
             (gamma1 - Beta)) /\
        (res.`2 = W64.zero =>
           wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 res.`1) /\
           lifts_wpolylvec (lvec_unflatten256 res.`1) =
             (lifts_wpolylvec (lvec_unflatten256 _mask)) +
             (PolyLVec.invnttv (PolyLVec.ntt_smul
               (lifts_wpoly _c)
               (lifts_wpolylvec (lvec_unflatten256 _s1)))) /\
           wpolylvec_srng (lvec_unflatten256 res.`1) (gamma1 - 1) gamma1)
    ] = 1%r.
proof.
by conseq __compute_z_and_check_norm_ll
          (__compute_z_and_check_norm_correct _s1 _c _mask _z0 _incr) => /#.
qed.

(* ================================================================== *)
(* __make_hint_vector                                                  *)
(* Called fourth; incr = combined result of all three norm checks.    *)
(* Computes h = MakeHintImpl(-ct0, w-cs2+ct0) per row (K=6).            *)
(* Checks total hint count <= omega = 55.                             *)
(* Note: ct0 at spec level is passed as parameter by the caller.      *)
(* ================================================================== *)

lemma __make_hint_vector_ll : islossless M.__make_hint_vector.
proof.
proc.
wp. (* post-loop: SETcc + OR *)
while (0 <= base <= 6 * n /\ base %% n = 0) (6*n - base); last by auto => /#.
move => ?.
wp. (* total_ones_in_hint += ones_in_hint *)
wp. (* hint_0 writeback *)
call polynomial____make_hint_ll.
wp. (* hint_element <- Array256.init *)
by auto => /#.
qed.

(* When all coefficients of the hint vector are 0 or 1 (wpolykvec_urng v 2),
   hammw and count_nonzero_coeffs_kvec measure the same thing:
   c <> Zq.zero <=> c = Zq.one for 0/1-valued coefficients. *)
lemma hammw_count_nonzero (v : wpolykvec) (bound : int) :
  wpolykvec_urng v 2 =>
  hammw (liftu_wpolykvec v) bound =>
  count_nonzero_coeffs_kvec (liftu_wpolykvec v) <= bound.
proof.
rewrite /wpolykvec_urng allP => Hrng.
rewrite /hammw /count_nonzero_coeffs /count_nonzero_coeffs_kvec /count_nonzero_coeffs /=.
rewrite /to_list /mkseq StdBigop.Bigint.BIA.big_map /(\o) /=.
suff: StdBigop.Bigint.BIA.big predT<:int>
  (fun (ii : int) => count (fun (jj : int) => (liftu_wpolykvec v).[ii].[jj] <> Zq.zero) (iota_ 0 n)) (
  iota_ 0 kvec) =
 StdBigop.Bigint.BIA.big (fun (x : int) => predT (liftu_wpolykvec v).[x])
  (fun (x : int) => count (fun (c : coeff) => c = Zq.one) (map ("_.[_]" (liftu_wpolykvec v).[x]) (iota_ 0 n)))
  (iota_ 0 kvec) by smt().
apply StdBigop.Bigint.BIA.eq_big_seq => x; rewrite mem_iota => /= *.
rewrite count_map;apply eq_in_count => k; rewrite mem_iota => /= *.
rewrite /preim /=.
have := Hrng x _; 1:smt().
rewrite /wpoly_urng allP => /= Hrngx.
have := Hrngx k _;1:smt().
move => H.
rewrite /liftu_wpolykvec !mapiE 1,2:/# /=.
smt(@Zq).
qed.


lemma __make_hint_vector_correct
      (_r : W32.t Array1536.t) (_w1 : W32.t Array1536.t)
      (_h : W32.t Array1536.t) (_incr : W64.t)
      :
    hoare [ M.__make_hint_vector :
        w0_minus_cs2_plus_ct0 = _r /\ w1 = _w1 /\ hint_0 = _h /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        (_incr = W64.zero =>
          wpolykvec_srng (kvec_unflatten256 _r) (2*gamma2 - Beta - 2) (2*gamma2 - Beta - 2)) /\
        wpolykvec_urng (kvec_unflatten256 _w1) ((q - 1) %/ (2 * gamma2))
        ==>
        (res.`2 = W64.zero \/ res.`2 = W64.one) /\
        (* Biconditional: failure bit is zero iff no prior failure AND
           the abstract hint-weight check holds. Hints are always 0/1 by
           construction — the spec-level condition is just hammw. *)
        (res.`2 = W64.zero =>
             liftu_wpolykvec (kvec_unflatten256 res.`1) =
               MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1))
                             (lifts_wpolykvec (kvec_unflatten256 _r))) /\
        (res.`2 = W64.zero <=>
           _incr = W64.zero /\
           PolyKVec.hammw
             (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1))
                          (lifts_wpolykvec (kvec_unflatten256 _r))) w_hint) /\
        (res.`2 = W64.zero =>
           (* Hint coefficients are 0 or 1, so the kvec is unsigned-range 2. *)
           wpolykvec_urng (kvec_unflatten256 res.`1) 2)
    ].
proof.
have kvec_val  := mldsa65_kvec.
have w_hint_val := mldsa65_w_hint.
proc => /=.
case (infinity_norm_check_result <> zero).
+ rcondt ^if; 1: by auto.
  rcondf ^while; 1: by auto.
  auto => /> *; do split; smt().

rcondf ^if; 1: by auto.
wp.  (* absorb post-loop: SETcc + zeroextu64 + OR *)
while (#{/~_incr}{~infinity_norm_check_result}{~hint_0}{~total_ones_in_hint}pre /\
       (infinity_norm_check_result = zero \/ infinity_norm_check_result = one) /\
       0 <= base <= 6*n /\ base %% n = 0 /\
       (infinity_norm_check_result <> zero => base = 6*n) /\
       wpolykvec_srng (kvec_unflatten256 _r) (2*gamma2 - Beta - 2) (2*gamma2 - Beta - 2) /\
       wpolykvec_urng (kvec_unflatten256 _w1) ((q - 1) %/ (2 * gamma2)) /\
       0 <= total_ones_in_hint /\
       (infinity_norm_check_result = zero =>
         (forall k, 0 <= k < base %/ n =>
           liftu_wpoly (kvec_unflatten256 hint_0).[k] =
             poly_MakeHintImpl (lifts_wpoly (kvec_unflatten256 _w1).[k])
                           (lifts_wpoly (kvec_unflatten256 _r).[k]))) /\
       (infinity_norm_check_result = zero =>
         (forall k, 0 <= k < base %/ n =>
           wpoly_urng 2 ((kvec_unflatten256 hint_0).[k]))) /\
       (infinity_norm_check_result = zero <=>
         _incr = zero /\
         big predT (fun ii =>
             count (fun jj => (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1))
                             (lifts_wpolykvec (kvec_unflatten256 _r))).[ii].[jj] <> Zq.zero)
                   (iota_ 0 256)) (iota_ 0 (base %/ n)) <= w_hint
         ) /\
        (infinity_norm_check_result = zero =>
         total_ones_in_hint =
           big predT (fun ii =>
             count (fun jj => (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1))
                             (lifts_wpolykvec (kvec_unflatten256 _r))).[ii].[jj] <> Zq.zero)
                   (iota_ 0 256)) (iota_ 0 (base %/ n)))
      ); last first.
(* ── Loop exit (combined with initialization) ─────────────────── *)
+ auto => /> ??.
  do split; 1,2:smt(). 
  + by rewrite (iota0 0 0) //= big_nil /#.
  + by rewrite (iota0 0 0) //= big_nil /#.
  (* exit condition: INV /\ !guard => post *)
  move => bs h0 inf0 toi0 ? Hbin ? ?? Hexit ? Hcond Hmhp Hmhp0 Hmhp1 Hmhp2.
  do split.
  + move => Hi.
    have HH := Hmhp Hi.
    rewrite tP => k kb.
    rewrite mapiE 1:/# HH 1:/# /MakeHintImpl map2iE 1:/# mapiE 1:/#; smt(KArray.mapiE).
  + move => Hi; rewrite /hammw.
    have -> : kvec = bs %/ n by smt().
    by have := Hmhp1; rewrite Hi /= => ->.
  + move => Hh.
    move: Hh; rewrite /hammw => Hh.
    have Hk : kvec = bs %/ n by smt().
    have := Hmhp1; by rewrite -Hk Hh.
  + move => Hi; rewrite /wpolykvec_urng allP; smt().
    
    
(* ── Loop body ────────────────────────────────────────────────── *)
(* Statements: 6.1 read slice, 6.2 ecall make_hint, 6.3 writeback,
               6.4 accumulate count, 6.5 base+=n,
               6.6 declassify (no-op), 6.7 if(fail){base=6n} *)
seq 3 : (#pre /\
    liftu_wpoly (Array256.init (fun i => hint_0.[base + i])) =
      poly_MakeHintImpl (lifts_wpoly (kvec_unflatten256 _w1).[base %/ n])
                    (lifts_wpoly (kvec_unflatten256 _r).[base %/ n]) /\
      wpoly_urng 2 (Array256.init (fun i => hint_0.[base + i]))  /\
    ones_in_hint =
      count (fun i => (liftu_wpoly (Array256.init (fun j => hint_0.[base + j]))).[i] <> Zq.zero)
            (iota_ 0 256)).
+ wp.
  ecall (polynomial____make_hint_correct
           (Array256.init (fun i => hint_0.[base + i]))
           (Array256.init (fun i => w0_minus_cs2_plus_ct0.[base + i]))
           (Array256.init (fun i => w1.[base + i]))).
  auto => |> &hr *.
  do split => /=.
  - (* r slice range: wpoly_srng (2*gamma2-Beta-2) from wpolykvec_srng *)
    have Hr : wpolykvec_srng (kvec_unflatten256 _r) (2*gamma2 - Beta - 2) (2*gamma2 - Beta - 2) by smt().
    have /= Heq : (kvec_unflatten256 _r).[base{hr} %/ n] = Array256.init (fun i => _r.[base{hr} + i])
      by apply kvec_slice_eq; smt(mldsa65_kvec).
    rewrite -Heq.
    by move: Hr; rewrite /wpolykvec_srng KArray.allP => H; apply H; smt(mldsa65_kvec).
  - (* w1 slice range: wpoly_urng from wpolykvec_urng *)
    have Hw : wpolykvec_urng (kvec_unflatten256 _w1) ((q - 1) %/ (2 * gamma2)) by smt().
    have /= Heq : (kvec_unflatten256 _w1).[base{hr} %/ n] = Array256.init (fun i => _w1.[base{hr} + i])
      by apply kvec_slice_eq; smt(mldsa65_kvec).
    rewrite -Heq.
    by move: Hw; rewrite /wpolykvec_urng KArray.allP => H; apply H; smt(mldsa65_kvec).
  move => ? ? result Hres_eq Hres_cnt.
  (* writeback slice reads back as result.`1 *)
  have Hwb_slice : (Array256.init (fun i =>
      (Array1536.init (fun i0 =>
        if base{hr} <= i0 < base{hr} + n then result.`1.[i0 - base{hr}]
        else hint_0{hr}.[i0])).[base{hr} + i])) = result.`1.
  + apply Array256.tP => j jb.
    rewrite Array256.initiE 1:/# /= Array1536.initiE; first by smt().
    by rewrite /= ifT 1:/# /= /#.
  have /= Hr_eq := kvec_slice_eq _r base{hr} _ _; 1,2: smt(mldsa65_kvec).
  have /= Hw1_eq := kvec_slice_eq _w1 base{hr} _ _; 1,2: smt(mldsa65_kvec).
  rewrite Hwb_slice Hres_eq Hr_eq Hw1_eq /=.
  move => Rv.

(* ── Phase 2: accumulate + base++ + declassify + conditional exit ── *)
do split;3..:smt().
move => Hinf.
have Hfork : forall k, 0 <= k < base{hr} %/ n =>
      liftu_wpoly (kvec_unflatten256 hint_0{hr}).[k] =
      poly_MakeHintImpl (lifts_wpoly (kvec_unflatten256 _w1).[k]) (lifts_wpoly (kvec_unflatten256 _r).[k])
  by move => k [Hk0 Hkn]; smt().
+ (* forall k < base/n: writeback preserves old columns *)
  move => k kb Hlt.
  have /= Hmod : base{hr} %% 256 = 0 by smt().
  have Hkvec : 0 <= k < kvec by smt(mldsa65_kvec).
  have /= Hwb := kvec_unflatten256_writeback_iE hint_0{hr} result.`1 base{hr} k Hmod Hkvec.
  by rewrite Hwb ifF; smt().
+ move => Hzero k Hk0 Hklt.
  have /= Hmod : base{hr} %% 256 = 0 by smt().
  have Hkvec : 0 <= k < kvec by smt(mldsa65_kvec).
  have /= Hwb := kvec_unflatten256_writeback_iE hint_0{hr} result.`1 base{hr} k Hmod Hkvec.
  by rewrite Hwb ifF;smt().

auto => /> &hr ???????????Hcount H??; split. 
+ rewrite /SETcc.
  pose p := 55 <
      total_ones_in_hint{hr} +
      count (fun (i : int) => (liftu_wpoly (init (fun (j : int) => hint_0{hr}.[base{hr} + j]))).[i] <> Zq.zero)
        (iota_ 0 n).
  move => Hf;do split;2:smt(count_ge0).
  + case p => Hp; case (infinity_norm_check_result{hr} = zero) => H0; 2,4:smt(W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64 or64_ne0); rewrite H0 /= to_uint_eq  to_uint_zeroextu64 //=;  by have := Hf;rewrite Hp H0 /= to_uint_eq /= to_uint_zeroextu64 //=.
  + case (_incr = zero); last by smt().
    move => Hi0 /=.
    case (infinity_norm_check_result{hr} = zero) => Hin0; last by smt().
    move : Hf; rewrite Hin0 /= to_uint_eq /= to_uint_zeroextu64 => ?.
    have  : p by smt(W8.to_uint_eq W8.of_uintK W8.to_uintK pow2_8).
    rewrite /p Hcount // => Hpp.
    have -> : 6 = base{hr} %/n + 1 + (6 - base{hr} %/n  - 1) by ring.
    rewrite iota_add;1,2:smt(mldsa65_kvec).
    rewrite iota_add;1,2:smt(mldsa65_kvec).
    simplify.
    rewrite iota1 !big_cat big_cons /= big_nil /= /(predT (base{hr} %/ n)) /=.
    (* Goal: !(big(0..base/n) + (MakeHintImpl w1 r)[base/n]-count + big(base/n+1..5) <= w_hint)
       Strategy: rewrite the middle count via Heq, then arithmetic from Hpp+Htail *)
    have Heq : (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1))
                   (lifts_wpolykvec (kvec_unflatten256 _r))).[base{hr} %/ n] =
               liftu_wpoly (init (fun (i : int) => hint_0{hr}.[base{hr} + i]))
      by rewrite /PolyKVec.MakeHintImpl map2iE 1:/# /lifts_wpolykvec mapiE 1:/# mapiE 1:/#; smt().
    rewrite Heq.
    have Htail : 0 <= big predT
        (fun (ii : int) => count (fun (jj : int) =>
           (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1))
              (lifts_wpolykvec (kvec_unflatten256 _r))).[ii].[jj] <> Zq.zero) (iota_ 0 n))
        (iota_ (base{hr} %/ n + 1) (5 - base{hr} %/ n))
      by apply sumr_ge0_seq => ??; smt( count_ge0).
    have Hcnt : count (fun (jj : int) =>
          (liftu_wpoly (init (fun (i : int) => hint_0{hr}.[base{hr} + i]))).[jj] <> Zq.zero)
        (iota_ 0 n) =
        count (fun (i : int) =>
          (liftu_wpoly (init (fun (j : int) => hint_0{hr}.[base{hr} + j]))).[i] <> Zq.zero)
        (iota_ 0 n) by done.
    move: Hpp.
    pose a := big predT<:int>
    (fun (ii : int) =>
       count
         (fun (jj : int) =>
            (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1)) (lifts_wpolykvec (kvec_unflatten256 _r))).[ii].[jj] <>
            Zq.zero) (iota_ 0 n)) (iota_ 0 (base{hr} %/ n)).
    pose b :=  count (fun (jj : int) => (liftu_wpoly (init (fun (i : int) => hint_0{hr}.[base{hr} + i]))).[jj] <> Zq.zero) (iota_ 0 n).
    pose F := (fun (ii : int) =>
       count
         (fun (jj : int) =>
            (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1)) (lifts_wpolykvec (kvec_unflatten256 _r))).[ii].[jj] <>
            Zq.zero) (iota_ 0 n)).
     by smt (sumr_ge0 count_ge0).

  move => Hn; do split;1..5: smt(count_ge0).
  + (* MakeHintImpl forall: extend from k < base/n to k < (base+n)/n *)
    move => _ k Hk0 Hklt.
    have Hinf0 : infinity_norm_check_result{hr} = zero
      by smt(or64_ne0 W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
    have /= Hslice := kvec_slice_eq hint_0{hr} base{hr} _ _; 1,2: smt(mldsa65_kvec).
    have Hkdec : k < base{hr} %/ n \/ k = base{hr} %/ n by smt().
    elim Hkdec => [Hklt2|->].
    + by smt().
    + by rewrite Hslice; smt().
  + (* wpoly_urng forall: extend from k < base/n to k < (base+n)/n *)
    move => _ k Hk0 Hklt.
    have Hinf0 : infinity_norm_check_result{hr} = zero
      by smt(or64_ne0 W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
    have /= Hslice := kvec_slice_eq hint_0{hr} base{hr} _ _; 1,2: smt(mldsa65_kvec).
    have Hkdec : k < base{hr} %/ n \/ k = base{hr} %/ n by smt().
    elim Hkdec => [Hklt2|->].
    + by smt().
    + by rewrite Hslice; smt().
  + (* Biconditional: inf_new = zero <=> _incr = zero /\ big(0..(base+n)/n) <= w_hint *)
    move => ?.
    have Hinf0 : infinity_norm_check_result{hr} = zero
      by smt(or64_ne0 W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
    pose p := 55 <
      total_ones_in_hint{hr} +
      count (fun (i : int) => (liftu_wpoly (init (fun (j : int) => hint_0{hr}.[base{hr} + j]))).[i] <> Zq.zero)
        (iota_ 0 n).
    have Hnp : !p
      by smt(W8.to_uint_eq W8.of_uintK W8.to_uintK pow2_8
             W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64 or64_ne0).
    split; 1: smt().
    have -> : (base{hr} + n) %/ n = base{hr} %/ n + 1 by smt().
    rewrite iota_add; 1,2: smt().
    rewrite iota1 big_cat big_cons /= big_nil /=.
    have Heq2 : (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1))
                   (lifts_wpolykvec (kvec_unflatten256 _r))).[base{hr} %/ n] =
                 liftu_wpoly (init (fun (i : int) => hint_0{hr}.[base{hr} + i]))
      by rewrite /PolyKVec.MakeHintImpl map2iE 1:/# /lifts_wpolykvec mapiE 1:/# mapiE 1:/#; smt().
    rewrite Heq2.
    have Hcnt : count (fun (jj : int) => (liftu_wpoly (init (fun (i : int) => hint_0{hr}.[base{hr} + i]))).[jj] <> Zq.zero) (iota_ 0 n) =
                count (fun (i : int) => (liftu_wpoly (init (fun (j : int) => hint_0{hr}.[base{hr} + j]))).[i] <> Zq.zero) (iota_ 0 n)
      by done.
    rewrite Hcnt -(Hcount Hinf0); smt().
  + (* count equality: inf_new = zero => total_new = big(0..(base+n)/n) *)
    move => _.
    have Hinf0 : infinity_norm_check_result{hr} = zero
      by smt(or64_ne0 W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
    have -> : (base{hr} + n) %/ n = base{hr} %/ n + 1 by smt().
    rewrite iota_add; 1,2: smt().
    rewrite iota1 big_cat big_cons /= big_nil /=.
    have Heq2 : (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1))
                   (lifts_wpolykvec (kvec_unflatten256 _r))).[base{hr} %/ n] =
                 liftu_wpoly (init (fun (i : int) => hint_0{hr}.[base{hr} + i]))
      by rewrite /PolyKVec.MakeHintImpl map2iE 1:/# /lifts_wpolykvec mapiE 1:/# mapiE 1:/#; smt().
    rewrite Heq2.
    have Hcnt : count (fun (jj : int) => (liftu_wpoly (init (fun (i : int) => hint_0{hr}.[base{hr} + i]))).[jj] <> Zq.zero) (iota_ 0 n) =
                count (fun (i : int) => (liftu_wpoly (init (fun (j : int) => hint_0{hr}.[base{hr} + j]))).[i] <> Zq.zero) (iota_ 0 n)
      by done.
    rewrite Hcnt -(Hcount Hinf0).
    ring.
qed.

lemma __make_hint_vector_ph
      (_r : W32.t Array1536.t) (_w1 : W32.t Array1536.t)
      (_h : W32.t Array1536.t) (_incr : W64.t)
      :
    phoare [ M.__make_hint_vector :
        w0_minus_cs2_plus_ct0 = _r /\ w1 = _w1 /\ hint_0 = _h /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        (_incr = W64.zero =>
          wpolykvec_srng (kvec_unflatten256 _r) (2*gamma2 - Beta - 2) (2*gamma2 - Beta - 2)) /\
        wpolykvec_urng (kvec_unflatten256 _w1) ((q - 1) %/ (2 * gamma2))
        ==>
        (res.`2 = W64.zero \/ res.`2 = W64.one) /\
        (* Biconditional: failure bit is zero iff no prior failure AND
           the abstract hint-weight check holds. Hints are always 0/1 by
           construction — the spec-level condition is just hammw. *)
        (res.`2 = W64.zero =>
             liftu_wpolykvec (kvec_unflatten256 res.`1) =
               MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1))
                             (lifts_wpolykvec (kvec_unflatten256 _r))) /\
        (res.`2 = W64.zero <=>
           _incr = W64.zero /\
           PolyKVec.hammw
             (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 _w1))
                          (lifts_wpolykvec (kvec_unflatten256 _r))) w_hint) /\
        (res.`2 = W64.zero =>
           (* Hint coefficients are 0 or 1, so the kvec is unsigned-range 2. *)
           wpolykvec_urng (kvec_unflatten256 res.`1) 2)
    ] = 1%r.
proof. by conseq __make_hint_vector_ll (__make_hint_vector_correct _r _w1 _h _incr). 
qed.
