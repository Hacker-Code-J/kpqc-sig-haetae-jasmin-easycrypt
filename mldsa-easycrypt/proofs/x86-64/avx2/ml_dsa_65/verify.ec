require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Hashing
                           Signature Challenge Row_vector Polynomial Commitment T1
                           Common_ntt Common_modular Common_invert_ntt Rounding.

require import CircuitBindings Bindings XArray48.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq.

require import Array2 Array32 Array48 Array64 Array256 Array768 Array1280 Array1536
               Array1920 Array1952 Array3309 Array7680.
               require import WArray48.

require import BitEncoding.
from CryptoSpecs require import JWordList.
import BitChunking.

lemma compare_commitment_hashes_ll : islossless M.__compare_commitment_hashes.
proof.
proc.
wp;while (0 <=  offset <= 48 /\ offset %% 16 = 0) (48 -  offset); last by auto => />; smt().
auto => /> ; smt().
qed.

lemma compare_commitment_hashes_correct (_lhs _rhs : W8.t Array48.t) :
    phoare [ M.__compare_commitment_hashes :
        arg.`1 = _lhs /\ arg.`2 = _rhs
        ==>
        res = (if _lhs = _rhs then W64.of_int 0 else -W64.one)
    ] = 1%r.
proof.
have hh : hoare [ M.__compare_commitment_hashes :
    arg.`1 = _lhs /\ arg.`2 = _rhs
    ==>
    res = (if _lhs = _rhs then W64.of_int 0 else -W64.one) ].
+ proc => /=.
  proc change 2 : { lhs_bytes <- if (0 <=  offset * 8 <= 48*8-128)
                                  then BSWAS_48u8_128.sliceget lhs (offset * 8)
                                  else get128_direct (WArray48.init8 (fun i => lhs.[i])) (offset); }.
  + auto => /> &2.
    case (0 <= offset{2} * 8 <= 256); last  by auto.
    by move => ?; rewrite -BSWAS_48u8_128_slicegetE /#.
  proc change 3 : { rhs_bytes <- if (0 <=  offset * 8 <= 48*8-128)
                                  then BSWAS_48u8_128.sliceget rhs ( offset * 8)
                                  else get128_direct (WArray48.init8 (fun i => rhs.[i])) (offset); }.
  + auto => /> &2.
    case (0 <= offset{2} * 8 <= 256); last by auto.
    by move => ?; rewrite -BSWAS_48u8_128_slicegetE /#.
  proc change ^while.1 : { lhs_bytes <- if (0 <= offset * 8 <= 48*8-128)
                                         then BSWAS_48u8_128.sliceget lhs (offset * 8)
                                         else get128_direct (WArray48.init8 (fun i => lhs.[i])) (offset); }.
  + auto => /> &2.
    case (0 <= offset{2} * 8 <= 256); last by auto.
    by move => ?; rewrite -BSWAS_48u8_128_slicegetE /#.
  proc change ^while.2 : { rhs_bytes <- if (0 <= offset * 8 <= 48*8-128)
                                         then BSWAS_48u8_128.sliceget rhs (offset * 8)
                                         else get128_direct (WArray48.init8 (fun i => rhs.[i])) (offset); }.
  + auto => /> &2.
    case (0 <= offset{2} * 8 <= 256); last by auto.
    by move => ?; rewrite -BSWAS_48u8_128_slicegetE /#.
  cfold 1;unroll for ^while.
  cfold 12.
  wp 12.
  conseq (: _ ==> _lhs = _rhs <=> result = W64.of_int 65535).
  + move => &hr [<- <-] rr [Hl Hr].
    case (rr <> W64.of_int 65535); last first.
    + move => HH; rewrite Hr //=.
      move => ?; rewrite ifF 1:/# /=.
      case (lhs{hr} = rhs{hr}) => ?; 1: by
       rewrite to_uint_eq /=; smt(W64.to_uint_cmp pow2_64).
      by rewrite to_uint_eq /= to_uintN /=. 
  by circuit.
conseq compare_commitment_hashes_ll hh;smt().
qed.


(* ================================================================== *)
(* reconstruct_signer_commitment                                       *)
(* Reconstructs w1' = UseHint(h, A*z - c*t1*2^d) for each of 6 rows. *)
(* Per-component loop body:                                            *)
(*   t1_decode → shift_left → NTT → pmmar(c,t1) →                    *)
(*   subtract(az, ct1) → reduce32 → invNTT → cond_add_mod →          *)
(*   use_hints → write back                                            *)
(* Then commitment_encode on the result.                               *)
(* Spec: w1Encode(UseHint(h, Az - c*NTT^{-1}(NTT(t1*2^d)*chat)))    *)
(* ================================================================== *)

lemma reconstruct_signer_commitment_ll :
    islossless M.reconstruct_signer_commitment.
proof.
proc.
wp; call commitment____encode_ll.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *; wp.
call polynomial__use_hints_ll; wp.
call polynomial__conditionally_add_modulus_ll.
call polynomial__invert_ntt_montgomery_ll.
call polynomial__reduce32_ll.
call polynomial__subtract_ll; wp.
call polynomial__pointwise_montgomery_multiply_and_reduce_ll.
call polynomial__ntt_ll.
call polynomial____shift_coefficients_left_ll.
call t1__decode_polynomial_ll.
by auto => /#.
qed.

(* Spec-level t1 polykvec obtained from the t1_encoded bytes (6 chunks of 320 bytes, *)
(* each decoded via SimpleBitUnpack with range 2^(q_bits-d)-1 = 1023 = b_t1).        *)
op t1_from_t1enc (_t1enc : W8.t Array1920.t) : polykvec =
   KArray.init (fun i =>
      SimpleBitUnpack
        (take ((n * (q_bits - d)) %/ 8)
              (drop (((n * (q_bits - d)) %/ 8) * i) (to_list _t1enc)))
        (2^(q_bits - d) - 1)).

(* The reconstructed signer commitment at the spec level: the wapprox that the proc *)
(* computes internally, reused by the verify proof after algebra bridging.           *)
op signer_commitment_spec
     (_t1enc : W8.t Array1920.t) (_ch : W32.t Array256.t) (_az : W32.t Array1536.t)
   : polykvec =
   invnttv (lifts_wpolykvec (kvec_unflatten256 _az)
             - ntt_smul (lifts_wpoly _ch)
                        (nttv (smul (t1_from_t1enc _t1enc) (incoeff (2^d))))).

lemma reconstruct_signer_commitment_correct
      (_t1enc : W8.t Array1920.t) (_ch : W32.t Array256.t)
      (_az : W32.t Array1536.t) (_hints : W32.t Array1536.t) :
    hoare [ M.reconstruct_signer_commitment :
        t1_encoded = _t1enc /\ challenge_as_ntt = _ch /\
        a_times_signer_response = _az /\ hints = _hints /\
        wpoly_ntt_orng _ch /\
        wpolykvec_urng (kvec_unflatten256 _hints) 2 /\
        (* _az is the output of row_vector____multiply_with_matrix_A: sum of lvec *)
        (* basemul results, each wpoly_srng (q-1) (q-1). Bound: lvec*(q-1).        *)
        wpolykvec_srng (kvec_unflatten256 _az) (lvec * (q-1)) (lvec * (q-1))
        ==>
        BytesW1.of_list (to_list res) =
          w1Encode (UseHint (liftu_wpolykvec (kvec_unflatten256 _hints))
                            (signer_commitment_spec _t1enc _ch _az))
    ].
proof.
have kvec_val := mldsa65_kvec.
have gamma2_val := mldsa65_gamma2.
proc => /=.
(* Post-loop: commitment____encode produces res from commitment.                       *)
(* commitment_encode's pre requires wpolykvec_urng _ b_w1 (values in [0..b_w1-1]).     *)
wp; ecall (commitment_encode commitment).
(* Outer 6-iteration loop. Invariant tracks, for each processed component k < i:       *)
(*  (a) liftu (commitment.[k]) = poly_UseHint (liftu (_hints.[k])) (spec_commit.[k]);  *)
(*  (b) wpoly_urng ((q-1)/(2*gamma2)) commitment.[k]  (tight use_hints post = [0..15]) *)
while (0 <= i <= 6 /\ t1_encoded = _t1enc /\ challenge_as_ntt = _ch /\
       a_times_signer_response = _az /\ hints = _hints /\
       wpoly_ntt_orng _ch /\
       wpolykvec_urng (kvec_unflatten256 _hints) 2 /\
       wpolykvec_srng (kvec_unflatten256 _az) (lvec * (q-1)) (lvec * (q-1)) /\
       (forall k, 0 <= k < i =>
          liftu_wpoly (kvec_unflatten256 commitment).[k] =
            poly_UseHint
              (liftu_wpoly (kvec_unflatten256 _hints).[k])
              (signer_commitment_spec _t1enc _ch _az).[k] /\
          wpoly_urng ((q - 1) %/ (2 * gamma2)) (kvec_unflatten256 commitment).[k])
      ); last first.
+ (* Exit: aggregate per-component invariant to kvec level and bridge to w1Encode.    *)
  auto => |> Hch_rng Hhints_rng Haz_rng; split; 1: smt().
  move => cm_exit i_exit Hng Hi1 Hi2 Hdone.
  (* Step 1: establish kvec-level equality for liftu cm_exit = UseHint _ spec.         *)
  have Hlifts_cm :
      liftu_wpolykvec (kvec_unflatten256 cm_exit) =
      UseHint (liftu_wpolykvec (kvec_unflatten256 _hints))
              (signer_commitment_spec _t1enc _ch _az).
  + rewrite /UseHint; apply KArray.tP => k kb.
    rewrite KArray.map2iE 1:/# /= /liftu_wpolykvec KArray.mapiE 1:/# /=.
    rewrite KArray.mapiE 1:/# /=.
    by have /= [-> _] := Hdone k _; smt(mldsa65_kvec).
  (* Step 2: derive wpolykvec_urng (b_w1+1) bound needed by commitment_encode's pre.    *)
  (* The invariant gives wpoly_urng ((q-1)/(2*gamma2)) = wpoly_urng 16 = wpoly_urng     *)
  (* (b_w1+1) per component (tight; the 4-bit-masked impl always stays in [0..15]).    *)
  have Hurng_b_w1 : wpolykvec_urng (kvec_unflatten256 cm_exit) (b_w1 + 1).
  + rewrite /wpolykvec_urng KArray.allP => k kbl.
    have /= [_ Hrng] := Hdone k _; 1: smt(mldsa65_kvec).
    by move: Hrng; rewrite /b_w1 /=; smt(mldsa65_gamma2).
  split; first exact Hurng_b_w1.
  (* Step 3: relate commitment_encode post (kvec_unflatten128 res = map SimpleBitPack)  *)
  (* to w1Encode definition (BytesW1.of_list (flatten (map SimpleBitPack (mkseq ...)))).*)
  move => _ encres Hunflat.
  rewrite Hlifts_cm in Hunflat.
  rewrite /w1Encode.
  have Hb_w1 : (q - 1) %/ (2 * gamma2) - 1 = b_w1
    by rewrite /b_w1 /=; smt(mldsa65_gamma2).
  rewrite Hb_w1; apply BytesW1.tP => k kb.
  rewrite !BytesW1.get_of_list 1,2:/# get_to_list (kvec_unflatten128iE encres k) 1:/# Hunflat.
  rewrite KArray.mapiE; 1: smt(mldsa65_kvec).
  rewrite /= Array128.Array128.get_of_list 1:/# (BitChunking.nth_flatten witness 128).
  + rewrite allP => s /mapP [wi [_ ->]] /=.
    by rewrite size_SimpleBitPack' /b_w1 /= /#.
  rewrite (nth_map witness); 1: by rewrite size_mkseq; smt(mldsa65_kvec).
  by rewrite nth_mkseq; 1: smt(mldsa65_kvec).
(* Loop body: 9-call chain (t1_decode → shift → ntt → pmmar → subtract → reduce32 →    *)
(*   invert_ntt → caddq → use_hints) + writeback. The ecall chain is structurally      *)
(* threaded below.                              *)
wp.
ecall (polynomial__use_hints_correct commitment_element hints_element).
wp.
ecall (polynomial__conditionally_add_modulus_correct commitment_element).
ecall (polynomial__invert_ntt_montgomery_correct commitment_element).
ecall (polynomial__reduce32_correct commitment_element).
ecall (polynomial__subtract_correct commitment_element az_element c_times_t1
         (lvec * (q-1)) (q-1)).
wp.
ecall (polynomial__pointwise_montgomery_multiply_and_reduce_correct
         c_times_t1 challenge_as_ntt t1_element).
ecall (polynomial__ntt_correct t1_element).
ecall (polynomial____shift_coefficients_left_correct t1_element).
ecall (t1_decode_polynomial
         (Array320.Array320.init
            (fun j => t1_encoded.[(q_bits - d) * n %/ 8 * i + j]))).
auto => /> &hr Hi1 Hi2 Hch_rng Hhints_rng Haz_rng Hdone Hguard.
move => result Hliftu_t1 Hurng_t1 Hurng_t1_1024 result0 Hto_sint_shift Hsrng_shift.
(* ntt's pre: wpoly_ntt_irng result0 via bridge from wpoly_srng (q-1) (q-1) *)
split; first by apply wpoly_srng_ntt_irng.
move => _ result1 Hlifts_ntt Horng_ntt.
(* pmmar's pre: wpoly_bmul_irng on _ch and result1 via wpoly_ntt_orng_bmul_irng *)
split; first split; [exact (wpoly_ntt_orng_bmul_irng _ Hch_rng)
                    | exact (wpoly_ntt_orng_bmul_irng _ Horng_ntt)].
move => _ _ result2 Hlifts_pmmar Hsrng_pmmar.
(* subtract's pre: wpoly_srng on az slice + arithmetic bound *)
split.
+ split; last by smt(mldsa65_lvec).
  have /= Hslice := kvec_slice_eq _az (i{hr} * n) _ _; 1,2: smt().
  have Hdiv : i{hr} * n %/ n = i{hr} by smt().
  move: Hslice; rewrite Hdiv => Hslice.
  rewrite -Hslice.
  by move: Haz_rng; rewrite /wpolykvec_srng KArray.allP => H; apply H; smt(mldsa65_kvec).
move => _ _ result3 Hlifts_sub Hsrng_sub result4 Hlifts_red Hsrng_red.
(* invert_ntt's pre: wpoly_intt_irng via widening + bridge *)
split; first by apply wpoly_bmul_orng_intt_irng;
  apply (wpoly_srng_widen _ ((q-1) %/ 2) ((q-1) %/ 2) (q-1) (q-1)); smt().
move => _ result5 Hlifts_invntt Hsrng_invntt.
(* caddq's pre: wpoly_srng (q-1) (q-1) via widening *)
split; first by apply (wpoly_srng_widen _ invntt_obound invntt_obound (q-1) (q-1));
  first 2 smt(invntt_obound_fits_for_caddq mldsa65_Eta);
  exact Hsrng_invntt.
move => _ result6 Hlifts_caddq Hurng_caddq.
(* use_hints' pre: wpoly_urng 2 hints slice *)
split.
+ have /= Hslice_h := kvec_slice_eq _hints (i{hr} * n) _ _; 1,2: smt().
  have Hdiv_h : i{hr} * n %/ n = i{hr} by smt().
  move: Hslice_h; rewrite Hdiv_h => Hslice_h.
  rewrite -Hslice_h.
  by move: Hhints_rng; rewrite /wpolykvec_urng KArray.allP => H; apply H; smt(mldsa65_kvec).
move => _ result7 Hliftu_useh Hurng_useh.
(* Final goal: invariant at i+1 *)
split; 1: smt().
move => k Hk_lo Hk_hi.
have /= Hwb :=
  kvec_unflatten256_writeback_iE commitment{hr} result7 (i{hr} * n) k _ _;
  1,2: smt(mldsa65_kvec).
rewrite Hwb.
case (k = i{hr}) => Hki.
+ (* New component k = i *)
  subst k; have Hnnd : i{hr} * n %/ n = i{hr} by smt().
  rewrite Hnnd ifT //; split; last exact Hurng_useh.
  rewrite Hliftu_useh.
  (* Match poly_UseHint's two args *)
  have H_hints_slice : liftu_wpoly (init (fun (i_0 : int) => _hints.[i{hr} * n + i_0])) =
                       (liftu_wpoly (kvec_unflatten256 _hints).[i{hr}]).
  + have /= Hslice_h2 := kvec_slice_eq _hints (i{hr} * n) _ _; 1,2: smt().
    move: Hslice_h2; rewrite Hnnd => Hslice_h2.
    by rewrite Hslice_h2.
  rewrite H_hints_slice; congr.
  (* Algebraic chain: liftu result6 = (signer_commitment_spec ...).[i] *)
  have Hliftu_eq : liftu_wpoly result6 = lifts_wpoly result6
    by rewrite -wpoly_urng_lifts_eq_liftu.
  rewrite Hliftu_eq Hlifts_caddq Hlifts_invntt Hlifts_red Hlifts_sub
          Hlifts_pmmar Hlifts_ntt.
  (* Unfold signer_commitment_spec + decompose the kvec ops *)
  rewrite /signer_commitment_spec /invnttv KArray.mapiE; 1: smt(mldsa65_kvec).
  rewrite polykvec_sub_iE; 1: smt(mldsa65_kvec).
  congr; congr.
  + (* lifts_wpoly az_slice = (lifts_wpolykvec ...).[i] *)
    rewrite /lifts_wpolykvec mapiE; 1: smt(mldsa65_kvec).
    congr; by rewrite -kvec_slice_eq; smt().
  (* Remaining: basemul _ch (ntt (lifts result0))
       = (&-) ((ntt_smul _ch (nttv (smul t1_spec (incoeff 2^d)))).[i])  *)
  (* Wait — need to match against the FULL (&-) term *)
  congr.
  rewrite /ntt_smul KArray.mapiE; 1: smt(mldsa65_kvec).
  rewrite /= /nttv KArray.mapiE; 1: smt(mldsa65_kvec).
  rewrite /smul KArray.mapiE; 1: smt(mldsa65_kvec).
  rewrite /=.
  (* Bridge: lifts_wpoly (shift result) = smul t1_spec (incoeff 2^d) at index i.      *)
  (* Per-coeff: Hto_sint_shift gives to_sint = to_uint * 2^d. After incoeffM and      *)
  (* Zq commutativity the remaining obligation reduces to the byte-list equality      *)
  (*   Array320.to_list (init (fun k => _t1enc.[320*i + k])) =                         *)
  (*   take 320 (drop (320*i) (to_list _t1enc))                                        *)
  (* which we close via eq_from_nth + size_take/size_drop + get_to_list/initiE.        *)
  have Hlifts_shift_eq :
      lifts_wpoly result0 = map ((( * ) (incoeff (2^d))))
                                (t1_from_t1enc _t1enc).[i{hr}].
  + apply Array256.tP => j jb.
    rewrite /lifts_wpoly mapiE 1:/# /= (Hto_sint_shift j jb).
    rewrite mapiE 1:/# /=.
    rewrite /t1_from_t1enc KArray.initiE; 1: smt(mldsa65_kvec).
    rewrite /=.
    rewrite incoeffM Zq.ComRing.mulrC; congr.
    have <- : liftu_wpoly result = SimpleBitUnpack
                (take 320 (drop (320 * i{hr}) (to_list _t1enc))) 1023.
    + rewrite Hliftu_t1 /b_t1 /=; congr.
      apply (eq_from_nth witness).
      + rewrite Array320.Array320.size_to_list size_take 1:/# size_drop 1:/#
                size_to_list /= /#.
      move => i0 Hi0.
      move: Hi0; rewrite Array320.Array320.size_to_list => Hi0.
      rewrite Array320.Array320.get_to_list Array320.Array320.initiE 1:/# /=.
      rewrite nth_take 1:/# 1:/# nth_drop 1:/# 1:/#.
      by rewrite get_to_list.
    by rewrite /liftu_wpoly mapiE 1:/#.
  rewrite Hlifts_shift_eq.
  (* basemul (lifts _ch) X = basemul X (lifts _ch) — use tP + init.                   *)
  (* W13_eq normalizes XWord13.W13.modulus (= 8192 = 2^d) on LHS to match RHS's 8192. *)
  apply Array256.tP => j jb.
  have W13_eq : XWord13.W13.modulus = 8192 by smt(XWord13.W13.ge2_modulus).
  rewrite W13_eq.
  rewrite /basemul !initiE 1,2:/# /=; first smt(mldsa65_kvec).
  by rewrite Zq.ComRing.mulrC.
+ (* Old component k < i: via Hdone *)
  have -> : (k = i{hr} * n %/ n) = false by smt().
  rewrite /=.
  by have /= := Hdone k _; first smt().
qed.

lemma reconstruct_signer_commitment_ph
      (_t1enc : W8.t Array1920.t) (_ch : W32.t Array256.t)
      (_az : W32.t Array1536.t) (_hints : W32.t Array1536.t) :
    phoare [ M.reconstruct_signer_commitment :
        t1_encoded = _t1enc /\ challenge_as_ntt = _ch /\
        a_times_signer_response = _az /\ hints = _hints /\
        wpoly_ntt_orng _ch /\
        wpolykvec_urng (kvec_unflatten256 _hints) 2 /\
        wpolykvec_srng (kvec_unflatten256 _az) (lvec * (q-1)) (lvec * (q-1))
        ==>
        BytesW1.of_list (to_list res) =
          w1Encode (UseHint (liftu_wpolykvec (kvec_unflatten256 _hints))
                            (signer_commitment_spec _t1enc _ch _az))
    ] = 1%r
  by conseq reconstruct_signer_commitment_ll
            (reconstruct_signer_commitment_correct _t1enc _ch _az _hints).

lemma ml_dsa_65_verify_correct _m :
    equiv [ MLDSA(MLDSA_XOFA, MLDSA_XOFS, MLDSA_XOF_SIB, SIB_RO).verify ~ M.ml_dsa_65_verify :
       Glob.mem{2} = _m /\
       arg{1}.`1 = BytesPK.of_list (to_list arg{2}.`1)
    /\ arg{1}.`2 = BytesSig.init (fun i => arg{2}.`5.[i])
    /\ W64.to_uint arg{2}.`2.[1] <= 255
    /\ 0 <= arg{2}.`4
    /\ to_uint context{2}.[0] + to_uint context{2}.[1] < 18446744073709551616
    /\ message_pointer{2} + message_size{2} < 18446744073709551616
    /\ arg{1}.`3 = [W8.zero; truncateu8 arg{2}.`2.[1]]
                   ++ memread _m (W64.to_uint arg{2}.`2.[0]) (W64.to_uint arg{2}.`2.[1])
                   ++ memread _m arg{2}.`3 arg{2}.`4
       ==>
       Glob.mem{2} = _m /\
       res{1} = (res{2} = W64.of_int 0)
   ].
proof.
have Hlvec := mldsa65_lvec.
have Hkvec := mldsa65_kvec.
have HLambda := mldsa65_lambda.
have HEta := mldsa65_Eta.
have Htau := mldsa65_tau.
have Hgamma1 := mldsa65_gamma1.

proc => /=; conseq |>.

sp 0 2.
rcondt {2} ^if; 1: by auto => /> /#.
inline {2} M.__verify_internal.
sp 0 6.
seq 1 9 : #pre; 1: by auto.
sp 1 0.
seq 1 0 : (#pre /\
    rho{1} = Bytes32.of_list (take 32 (BytesPK.to_list pk{1})) /\
    t1{1}  = KArray.init (fun i =>
        SimpleBitUnpack
          (take ((n * (q_bits-d)) %/ 8)
                (drop (((n * (q_bits-d)) %/ 8) * i + 32) (BytesPK.to_list pk{1})))
          (2^(q_bits - d) - 1))).
+ ecall{1} (pkDecode_corr pk{1}).
  by auto.

seq 1 1 : (#pre /\
    ct{1} = BytesCT.init (fun i => signature{2}.[i]) /\
    lifts_wpolylvec (lvec_unflatten256 signer_response{2}) = z{1} /\
    wpolylvec_srng (lvec_unflatten256 signer_response{2}) (gamma1 - 1) gamma1 /\
    (h{1} = None => result1{2} = -W64.one) /\
    (h{1} <> None =>
        result1{2} = W64.zero /\
        liftu_wpolykvec (kvec_unflatten256 hints{2}) = oget h{1} /\
        wpolykvec_urng (kvec_unflatten256 hints{2}) 2)).
+ ecall (signature_decode signature{2}).
  by auto.
seq 0 1 : (#pre /\
    (!wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 signer_response{2}) => result2{2} <> W64.of_int 0) /\
    (wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 signer_response{2})  => result2{2} = W64.zero)).
+ ecall {2} (row_vector____check_infinity_norm_correct signer_response{2} ((1 `<<` gamma1m1_bits) - 49 * w1_bits)).
  auto => /> &1 &2 ?????? rr0.
  have -> : (1 `<<` gamma1m1_bits) - 49 * w1_bits = gamma1 - Beta
    by rewrite /(`<<`) /= /Beta /=; smt(mldsa65_gamma1 mldsa65_tau mldsa65_Eta).
  have Hbnd : 0 < gamma1 - Beta <= q %/ 2
    by rewrite /Beta /=; smt(mldsa65_gamma1 mldsa65_tau mldsa65_Eta). 
  by smt(). 
  
if {1}; last first.
+ sp 0 1; rcondf {2} 1.
  + auto => |> &hr ?????-> ??. 
    have ? : (- W64.one <> W64.zero); last by smt(or64_ne0).
    by rewrite to_uint_eq to_uintN  /=.
  auto => /> &2 ?????  -> ??.
    have ? : (- W64.one <> W64.zero); last by smt(or64_ne0).
    by rewrite to_uint_eq to_uintN  /=.
  
sp;if {2}; last first.
+ wp; call {1} (: true ==> true); 1: by proc*; exlim  rho => _rho;  call (SampleInBall_correct _rho).
  wp; call {1} (: true ==> true); 1: by proc*; exlim  rho => _rho;  call (ExpandA_correct _rho).
  auto => /> &1 &2 ?????????? rr0 rr1.
  have ? : (!wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 signer_response{2})) by smt(or64_ne0).
  have Hrng : wpolylvec_srng (lvec_unflatten256 signer_response{2}) (gamma1-1) gamma1 by smt().
  have Hb : 0 < gamma1 - Beta <= q %/ 2 by rewrite /Beta /=; smt(mldsa65_gamma1 mldsa65_tau mldsa65_Eta).
  have Hq1 : (gamma1-1) + 1 <= q %/ 2 by smt(mldsa65_gamma1).
  have Hq2 : gamma1 <= q %/ 2 by smt(mldsa65_gamma1).
  have ? := wpolylvec_infnorm_unliftE (gamma1-Beta) (gamma1-1) gamma1
              (lvec_unflatten256 signer_response{2}) Hb Hq1 Hq2 Hrng.
  by smt().
  
(* expand A *)
seq 1 1 : (#pre /\
      liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
      wpolymat_urng (mat_unflatten256 matrix_A{2}) q).
  + ecall{1} (ExpandA_correct rho{1}).
    ecall{2} (matrix_A_correct (Array32.init (fun i => verification_key{2}.[i]))).
    auto => |> &1 &2 ??????????? rr0 -> ?;congr.
    apply Bytes32.tP => k kb.
    do 2!(rewrite Bytes32.get_of_list //).
    rewrite get_to_list initiE 1:/# /=.
    rewrite nth_take 1,2:/# BytesPK.get_to_list /=.
    by rewrite BytesPK.get_of_list 1:/# get_to_list.

(* anticipate hashing *)
swap {2} [6..7] -5.

(* verification key hash. *)
sp 1 0.
seq 0 1 : (#pre /\
      verification_key_hash{2} =
        Array64.of_list witness (Bytes64.to_list (H_tr pk{1}))).
  + ecall{2} (hash_verification_key_correct verification_key{2}).
    by auto.

(* message representative *)    
sp 1 0.
seq 0 1 : (#pre /\
      message_representative{2} =
        Array64.of_list witness (Bytes64.to_list mu{1})).
  + ecall{2} (derive_message_representative_ph
                 verification_key_hash{2}
                 (memread _m context_pointer{2} context_size{2})
                 (memread _m message_pointer{2} message_size{2})).
    wp; skip => /> &1 &2 *; do split.
    + by rewrite !size_memread /=; smt(W64.to_uint_cmp).
    + by rewrite !size_memread /=; smt(W64.to_uint_cmp).
    + by rewrite !size_memread /=; smt(W64.to_uint_cmp).
    + by rewrite !size_memread /=;  smt(W64.to_uint_cmp).
    move => ????;do congr.
    + rewrite Bytes64.tP => k kb.
      by rewrite Bytes64.get_of_list // get_to_list get_of_list //.
    + by rewrite size_memread; smt(W64.to_uint_cmp).
   
(* anticipate sib *)
swap {2} [3..4] -2.
  seq 1 1 : (#pre /\ lifts_wpoly challenge{2} = c{1} /\ wpoly_srng 1 1 challenge{2}).
  + call sample_challenge_correct.
    wp; skip => /> &1 &2 *.
    rewrite BytesCT.tP => i ib.
    rewrite BytesCT.initiE 1:/# BytesCT.get_of_list 1:/#.
    by rewrite get_to_list initiE /#.

(* Ghost-bind pre-NTT signer_response and challenge — the seq 2 4 below NTTs   *)
(* them in place, so the infnorm/range/lifts facts we established earlier      *)
(* (which reference the memory vars signer_response{2} / challenge{2}) would   *)
(* become false post-seq if left as literal memory references.                 *)
exlim signer_response{2} => _sr_pre.
exlim challenge{2} => _ch_pre.

(* jump over algebra *)
seq 2 4 :
  (#{/~signer_response{2}}{/~challenge{2}}pre /\
    lifts_wpolylvec (lvec_unflatten256 _sr_pre) = z{1} /\
    wpolylvec_srng (lvec_unflatten256 _sr_pre) (gamma1 - 1) gamma1 /\
    (!wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 _sr_pre) => result2{2} <> W64.of_int 0) /\
    (wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 _sr_pre) => result2{2} = W64.zero) /\
    lifts_wpoly _ch_pre = c{1} /\
    wpoly_srng 1 1 _ch_pre /\
    BytesW1.of_list (to_list reconstructed_signer_commitment{2}) = w1Encode w1{1}); last first.

(* recompute hash *)
sp 1 0.
seq 0 1 : (#pre /\
      expected_commitment_hash{2} =
        Array48.of_list witness (BytesCT.to_list (H_ct mu{1} (w1Encode w1{1})))).
  + ecall{2} (derive_commitment_hash_ph message_representative{2}
                 reconstructed_signer_commitment{2}).
    wp; skip => /> &1 &2 *; do congr.
    rewrite Bytes64.tP => k kb.
    + by rewrite Bytes64.get_of_list // get_to_list get_of_list //.

 wp; ecall{2} (compare_commitment_hashes_correct expected_commitment_hash{2} (Array48.init (fun (i : int) => signature_encoded{2}.[0 + i]))).
 
 wp;skip => /> &1 &2 *.
 pose xx := H_ct
   (H_mu (H_tr (BytesPK.of_list (to_list verification_key{2})))
      (W8.zero :: truncateu8 context{2}.[1] :: (memread _m (to_uint context{2}.[0]) (to_uint context{2}.[1]) ++  memread _m message_pointer{2} message_size{2}))) (
   w1Encode w1{1}).
have ? : wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 _sr_pre) by smt(or64_ne0).
have -> /=: infnorm_lt (lifts_wpolylvec (lvec_unflatten256 _sr_pre)) (gamma1 - Beta).
+ have /# := wpolylvec_infnorm_liftE (gamma1-Beta)
              (lvec_unflatten256 _sr_pre) _ _; by smt().
suff: ((BytesCT.init ("_.[_]" signature{2}) = xx) <=>  (Array48.of_list witness (BytesCT.to_list xx) = Array48.init ("_.[_]" signature{2}))); last first.
+ by rewrite tP BytesCT.tP /=;split => H i ib; have := H i _;[ by smt() | rewrite get_of_list 1:/# BytesCT.get_to_list BytesCT.initiE 1:/# /= initiE /#  | by smt() | rewrite get_of_list 1:/# BytesCT.get_to_list BytesCT.initiE 1:/# /= initiE /# ].

move => -> ; pose bb := Array48.of_list witness (BytesCT.to_list xx) = Array48.init ("_.[_]" signature{2}).
by case (bb) => //=; rewrite to_uint_eq to_uintN /=.

(* algebra: the forward head of `seq 2 4` — chain the four Jasmin ecalls        *)
(* (polynomial__ntt on challenge, row_vector__ntt on signer_response,           *)
(*  row_vector____multiply_with_matrix_A, reconstruct_signer_commitment) then   *)
(* substitute the spec's wapprox via the known lifted equalities (nttv, ntt,    *)
(* matrix multiply) and the pkDecode ↔ t1_from_t1enc slice identity.             *)
sp 2 0.
wp; ecall{2} (reconstruct_signer_commitment_ph
                (Array1920.init (fun i => verification_key0{2}.[32 + i]))
                challenge{2} a_times_signer_response{2} hints{2}).
wp; ecall{2} (row_vector____multiply_with_matrix_A_ph matrix_A{2} signer_response{2}).
wp; ecall{2} (row_vector__ntt_ph signer_response{2}).
wp; ecall{2} (polynomial__ntt_ph challenge{2}).
auto => />.
move => &1 &2 Hctx Hmsg Hov1 Hov2 Hz_srng Hh_none Hh_some_case Hr2_nz Hr2_z Hh_some Hor HA Hc_srng.
split; first by apply wpoly_srng_ntt_irng; apply (wpoly_srng_widen _ 1 1 (q-1) (q-1)); smt().
move => _ result0 Hlift_chal Horng_chal.
split; first by apply wpolylvec_srng_ntt_irng;
  apply (wpolylvec_srng_widen _ (gamma1-1) gamma1 (q-1) (q-1)); smt(mldsa65_gamma1).
move => _ result3 Hlift_s_ntt Horng_s.
split; first exact (wpolylvec_ntt_orng_bmul_irng _ Horng_s).
move => _ result4 Hlift_amulz Hsrng_amulz.
have [Hr1z [Hh_lift Hh_urng]] := Hh_some_case Hh_some.
split; first exact Hh_urng.
move => _ result5 Hreconstruct.
rewrite Hreconstruct Hh_lift.
congr; congr.
rewrite /signer_commitment_spec Hlift_amulz Hlift_s_ntt Hlift_chal.
congr; congr; congr; congr; congr.
+ (* t1_from_t1enc (init (fun i => verification_key0.[32+i])) = pkDecode t1 form *)
  rewrite /t1_from_t1enc.
  apply KArray.tP => k kb.
  rewrite !KArray.initiE; 1,2: smt(mldsa65_kvec).
  rewrite /= BytesPK.of_listK; 1: by rewrite size_to_list /#.
  congr; congr.
  have -> : to_list (Array1920.init (fun i => verification_key{2}.[32 + i])) =
            drop 32 (to_list verification_key{2}).
  + apply (eq_from_nth witness); 1: by rewrite size_to_list size_drop 1:/# size_to_list /#.
    move => i Hi.
    rewrite get_to_list Array1920.initiE /=;
      1: by move: Hi; rewrite size_to_list.
    by rewrite nth_drop 1:/# 1:/# get_to_list /#.
  by rewrite drop_drop 1,2:/#.
+ (* incoeff XWord13.W13.modulus = incoeff 8192 *)
  have W13_eq : XWord13.W13.modulus = 8192 by smt(XWord13.W13.ge2_modulus).
  by rewrite W13_eq.
qed.
