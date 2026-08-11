require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Hashing
                           Signature Challenge Row_vector S1 S2 T0 Mask
                           Sign_norm_checks Common_ntt Commitment Polynomial.

require import Column_vector.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq.

require import Array2 Array32 Array48 Array64 Array128 Array256
               Array416 Array640 Array768 Array1280 Array1536 Array2496
               Array3309 Array4032 Array7680 WArray5120.
require import XArray5120 XWord4.

require import BitEncoding.
from CryptoSpecs require import JWordList.
import BitChunking.

(* -------------------------------------------------------------------- *)
(* Loop-body machine-arithmetic helper.                                 *)
(*                                                                      *)
(* At the bottom of the rejection-sampling loop, the Jasmin code        *)
(* increments `domain_separator_for_mask` (a W16 counter advancing by   *)
(* lvec per iteration) and tests whether the loop has run kappa_max     *)
(* times via the xor+TEST_32+SETcc chain:                               *)
(*                                                                      *)
(*   kappa_diff        := zeroextu32 dsep `^` of_int ((2^16-1 - lvec) %/ lvec * lvec) *)
(*   kappa_bit         := SETcc (TEST_32 kappa_diff kappa_diff).`5      *)
(*   kappa_exceeded_R  := kappa_exceeded `|` zeroextu64 kappa_bit       *)
(*                                                                      *)
(* This packages the key invariant the smt() at the end of the loop    *)
(* body needs: that `kappa_exceeded_R` tracks `kappa_max <= kappa+1`    *)
(* exactly, assuming the prior iteration's `kappa_exceeded` tracked    *)
(* `kappa_max <= kappa`, and the counter has advanced by `lvec`.        *)
(* -------------------------------------------------------------------- *)

lemma kappa_bit_update (kappa : int) (kappa_e : W64.t) (dsep : W16.t) :
  0 <= kappa =>
  kappa_max = (65535 - lvec) %/ lvec =>
  W16.to_uint dsep = (kappa + 1) * lvec =>
  (kappa_e = W64.one) = (kappa_max <= kappa) =>
  (kappa_e <> W64.one => kappa_e = W64.zero) =>
  let kappa_diff    = zeroextu32 dsep `^` W32.of_int ((65535 - lvec) %/ lvec * lvec) in
  let kappa_bit     = SETcc (TEST_32 kappa_diff kappa_diff).`5 in
  let kappa_exc_R   = kappa_e `|` zeroextu64 kappa_bit in
  (kappa_exc_R = W64.one) = (kappa_max <= kappa + 1) /\
  (kappa_exc_R <> W64.one => kappa_exc_R = W64.zero).
proof.
move => ?; rewrite mldsa65_lvec /=  => ->.
move => Hd Hke ? /=.
case (13106 <= kappa) => ? /=.
+ rewrite (: 13106 <= kappa + 1) 1:/# /SETcc /TEST_32 /rflags_of_bwop /ZF_of /=.
  have -> : kappa_e = one by smt().
  have ->/= : zeroextu32 dsep `^` of_int 65530 <> zero 
   by rewrite W32.WRing.addr_eq0 /= to_uint_eq to_uint_zeroextu32 /oppw /=; smt(W32.to_uint_eq W32.of_uintK W32.to_uintK pow2_32).
   by rewrite eqT /zeroextu64/=.

   case (kappa < 13105) => ? /=.
rewrite (: !13106 <= kappa + 1) 1:/# /SETcc /TEST_32 /rflags_of_bwop /ZF_of /=.
  have -> : kappa_e = zero by smt().
have ->/= : zeroextu32 dsep `^` of_int 65530 <> zero 
   by rewrite W32.WRing.addr_eq0 /= to_uint_eq to_uint_zeroextu32 /oppw /=; smt(W32.to_uint_eq W32.of_uintK W32.to_uintK pow2_32).
   rewrite /zeroextu64/=;  smt(W32.to_uint_eq W32.of_uintK W32.to_uintK pow2_32).
  
move : Hd.
have ->/= : kappa = 13105 by smt().
move => Hd.
rewrite eqT /SETcc /TEST_32 /rflags_of_bwop /ZF_of /=. 
  have ->/= : kappa_e = zero by smt().
  rewrite to_uint_eq to_uint_zeroextu64.
  have -> /= : dsep = of_int 65530 by smt(W16.to_uint_eq W16.of_uintK W16.to_uintK pow2_16).
  by rewrite /zeroextu32 /=.
  qed.

(* Companion: the exit-flag update. Given the 0/1 invariant on the norm-check
   result (`ncr`) and on the kappa-exceeded flag (`kappa_exc_R`), the new
   exit flag `ers_R = ncr `^` 1 `|` kappa_exc_R` is zero iff both the norm
   checks passed (`ncr = 1` on Jasmin side is failure, `= 0` is success —
   so a zero exit flag requires `ncr = 1`, i.e. *failure*, and kappa not
   yet exceeded). The branching on `bz`/`bh` in the spec gives exactly
   `zh_L = None <=> ncr = 1` at the call site. *)

lemma exit_loop_update (ncr kappa_exc_R : W64.t) :
  (ncr = W64.zero \/ ncr = W64.one) =>
  (kappa_exc_R = W64.one \/ kappa_exc_R = W64.zero) =>
  let ers_R = ncr `^` W64.one `|` kappa_exc_R in
  (ers_R = W64.zero) = (ncr = W64.one /\ kappa_exc_R = W64.zero).
  proof.
simplify => H H0.
elim H => ->; elim H0 => -> /=;
  smt(W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64 W64.WRing.addr_eq0).
qed.

lemma s2_valid_commutes (sk : W8.t Array4032.t) :
     valid_s2_bytes (init (fun (i : int) => sk.[768 + i])) =>
        valid_sk_s2 (BytesSK.of_list (to_list sk)).
proof. 
have Hlvec   := mldsa65_lvec.
have Hkvec   := mldsa65_kvec.
have HEta    := mldsa65_Eta.
have Hgamma1 := mldsa65_gamma1.
have Htau    := mldsa65_tau.
  rewrite /valid_s2_bytes /valid_sk_s2 /valid_eta_bytes   mldsa65_Eta /==> H k kb.
  move  =>  i ib.
  have := H k kb => Hi.
  have := Hi i ib.
  rewrite BytesSK.of_listK;1: by rewrite size_to_list /#.
  rewrite /BitsToInteger /to_uint.
  pose a := BS2Int.bs2int _.
  pose b := BS2Int.bs2int _.
  suff : (a = b) by smt().
  rewrite /a /b;congr; apply (eq_from_nth false).
  + rewrite  size_nth_chunk;1,3:smt(ilog_ge0).
    by rewrite size_BytesToBits size_take 1:/# size_drop 1:/# size_to_list ifT /#.
  move => j; rewrite  size_w2bits => jb.
  rewrite get_w2bits initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  rewrite (nth_change_dfl [] witness);1: by  rewrite size_chunk 1:/#  size_BytesToBits /= size_take 1:/# /= size_drop 1:/# /= size_to_list /#.
   rewrite nth_chunk; 1,2: by smt().
   + by rewrite size_BytesToBits size_take 1:/# /= size_drop 1:/# /= size_to_list /#.
   rewrite nth_take 1,2:/# nth_drop 1,2:/# /BytesToBits (nth_flatten false 8).
   + by rewrite allP => ii; rewrite mapP => He /=; elim He => x [# ? ->]; rewrite size_w2bits.
   rewrite (nth_map witness); 1: by rewrite size_take 1:/# size_drop 1:/# size_to_list /#.
   rewrite get_w2bits nth_take 1,2:/# nth_drop 1,2:/# get_to_list /#.
qed.

(* Correctness of the AVX2 ML-DSA-65 signing function.
   We prove an equiv between:
     - MLDSA(...).sign_derand(sk, m, coins) on the spec side
     - M.ml_dsa_65_sign(sig, sk, ctx, msg_ptr, msg_size, randomness) on the Jasmin side

   The _m parameter is a snapshot of Glob.mem so that memread expressions are stable.
   The precondition connects:
     - sk (BytesSK.t) to the Jasmin signing_key (Array4032)
     - coins via rnd_to_list (abstract rnd_ type) to the Jasmin randomness (Array32)
     - m (W8.t list) to the context-prefixed message read from memory
   The postcondition connects the output signatures byte-for-byte and confirms
   the Jasmin result code is 0 (success, kappa not exceeded). *)

lemma ml_dsa_65_sign_correct _m :
    kappa_max = (65535 - lvec) %/ lvec =>
    equiv [ MLDSA(MLDSA_XOFA, MLDSA_XOFS, MLDSA_XOF_SIB, SIB_RO).sign_derand
            ~ M.ml_dsa_65_sign :
       Glob.mem{2} = _m
    /\ sk{1} = BytesSK.of_list (to_list signing_key{2})
    /\ rnd_to_list coins{1} = to_list randomness{2}
    /\ W64.to_uint context{2}.[1] <= 255
    /\ 0 <= message_size{2}
    /\ to_uint context{2}.[0] + to_uint context{2}.[1] < W64.modulus
    /\ message_pointer{2} + message_size{2} < W64.modulus
    /\ m{1} = [W8.zero; truncateu8 context{2}.[1]]
              ++ memread _m (W64.to_uint context{2}.[0]) (W64.to_uint context{2}.[1])
              ++ memread _m message_pointer{2} message_size{2}
    /\ valid_s1_bytes (Array640.init (fun i => signing_key{2}.[128 + i]))
    /\ valid_s2_bytes (Array768.init (fun i => signing_key{2}.[768 + i]))
       ==>
       Glob.mem{2} = _m
    /\ (res{1}.`1 = None <=> res{2}.`2 = -W64.one)
    /\ (res{1}.`1 <> None =>
          BytesSig.to_list (oget res{1}.`1) = to_list res{2}.`1 /\
          res{2}.`2 = W64.zero)
    ].
proof.
have Hlvec   := mldsa65_lvec.
have Hkvec   := mldsa65_kvec.
have HEta    := mldsa65_Eta.
have Hgamma1 := mldsa65_gamma1.
have Htau    := mldsa65_tau.
move => Hkappa_max.
proc*.
transitivity {1} { r <@ MLDSA(MLDSA_XOFA, MLDSA_XOFS, MLDSA_XOF_SIB, SIB_RO).sign_eager(sk,m, coins); }
    (={sk,m,coins, glob MLDSA_XOFA, glob MLDSA_XOFS, glob MLDSA_XOF_SIB, glob SIB_RO}
     /\ valid_sk_s2 sk{1} ==> ={r})
    (   Glob.mem{2} = _m
    /\ sk{1} = BytesSK.of_list (to_list signing_key{2})
    /\ rnd_to_list coins{1} = to_list randomness{2}
    /\ W64.to_uint context{2}.[1] <= 255
    /\ 0 <= message_size{2}
    /\ to_uint context{2}.[0] + to_uint context{2}.[1] < W64.modulus
    /\ message_pointer{2} + message_size{2} < W64.modulus
    /\ m{1} = [W8.zero; truncateu8 context{2}.[1]]
              ++ memread _m (W64.to_uint context{2}.[0]) (W64.to_uint context{2}.[1])
              ++ memread _m message_pointer{2} message_size{2}
    /\ valid_s1_bytes (Array640.init (fun i => signing_key{2}.[128 + i]))
    /\ valid_s2_bytes (Array768.init (fun i => signing_key{2}.[768 + i]))
       ==>
       Glob.mem{2} = _m
    /\ (r{1}.`1 = None <=> r{2}.`2 = -W64.one)
    /\ (r{1}.`1 <> None =>
          BytesSig.to_list (oget r{1}.`1) = to_list r{2}.`1 /\
          r{2}.`2 = W64.zero)
    ).
+ auto => /> &1 &2 ??????H.
  exists (MLDSA_XOFA.pos{1}) (MLDSA_XOFA.seed{1}) MLDSA_XOFS.pos{1} MLDSA_XOFS.seed{1}.
  exists MLDSA_XOF_SIB.pos{1} MLDSA_XOF_SIB.seed{1}. print rnd_to_list.
  exists coins{1} (zero :: truncateu8 context{2}.[1] :: (memread _m (to_uint context{2}.[0]) (to_uint context{2}.[1]) ++ memread _m message_pointer{2} message_size{2})).
  exists (BytesSK.of_list (to_list signing_key{2})).
  simplify;split; last by smt().
  by apply s2_valid_commutes=> /#.
+ smt().
+ by call sign_eager_equiv; auto.
  
call(:  Glob.mem{2} = _m
    /\ sk{1} = BytesSK.of_list (to_list signing_key{2})
    /\ rnd_to_list coins{1} = to_list randomness{2}
    /\ W64.to_uint context{2}.[1] <= 255
    /\ 0 <= message_size{2}
    /\ to_uint context{2}.[0] + to_uint context{2}.[1] < W64.modulus
    /\ message_pointer{2} + message_size{2} < W64.modulus
    /\ m{1} = [W8.zero; truncateu8 context{2}.[1]]
              ++ memread _m (W64.to_uint context{2}.[0]) (W64.to_uint context{2}.[1])
              ++ memread _m message_pointer{2} message_size{2}
    /\ valid_s1_bytes (Array640.init (fun i => signing_key{2}.[128 + i]))
    /\ valid_s2_bytes (Array768.init (fun i => signing_key{2}.[768 + i]))
       ==>
       Glob.mem{2} = _m
    /\ (res{1}.`1 = None <=> res{2}.`2 = -W64.one)
    /\ (res{1}.`1 <> None =>
          BytesSig.to_list (oget res{1}.`1) = to_list res{2}.`1 /\
          res{2}.`2 = W64.zero)
    ); last by auto.
proc => /=.
conseq (: _ ==>
        (zh{1} = None <=> result{2} = - one) /\
  (zh{1} <> None =>
   BytesSig.to_list sigma{1} = to_list signature{2} /\ result{2} = zero)); 1: by smt().
   
(* Jasmin: compute context_pointer and context_size from context array *)
sp 0 2.

(* Jasmin: the context-size guard must hold (given by precondition) *)
rcondt {2} ^if; 1: by auto => /> /#.

(* Inline the Jasmin __sign_internal body *)
inline {2} M.__sign_internal.

sp 0 7.
seq 4 19 : #pre; 1: by auto.

(* ── Step 1: SkDecode (spec only) ────────────────────────────────────────
   Spec: (rho,_K,tr,s1,s2,t0) <@ SkEncDec.skDecode(sk)
   Jasmin: nothing yet (Jasmin decodes each piece separately below) *)
seq 1 0 : (#pre /\
    rho{1} = Bytes32.of_list (take 32 (BytesSK.to_list sk{1})) /\
    _K{1} = Bytes32.of_list (take 32 (drop 32 (BytesSK.to_list sk{1}))) /\
    tr{1} = Bytes64.of_list (take 64 (drop 64 (BytesSK.to_list sk{1}))) /\
    s1{1} = LArray.init (fun i =>
        BitUnpack (take ((n * noise_bits) %/ 8)
                        (drop (128 + i * ((n * noise_bits) %/ 8)) (BytesSK.to_list sk{1})))
                  Eta Eta) /\
    s2{1} = KArray.init (fun i =>
        BitUnpack (take ((n * noise_bits) %/ 8)
                        (drop (128 + s1_bytes + i * ((n * noise_bits) %/ 8)) (BytesSK.to_list sk{1})))
                  Eta Eta) /\
    t0{1} = KArray.init (fun i =>
        BitUnpack (take ((n * d) %/ 8)
                        (drop (128 + s1_bytes + s2_bytes + i * ((n * d) %/ 8)) (BytesSK.to_list sk{1})))
                  (2^(d-1)-1) (2^(d-1))));
   1: by ecall{1} (skDecode_corr sk{1}); auto => |> *; smt().

(* ── Step 3: ExpandA (spec) ~ sample____matrix_A (Jasmin) ───────────────
   Jasmin: matrix_A <@ sample____matrix_A(seed_for_matrix_A) *)
sp;seq 1 1 : (#pre /\
    liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
    wpolymat_urng (mat_unflatten256 matrix_A{2}) q).
+ ecall{1} (ExpandA_correct rho{1}).
  ecall{2} (matrix_A_correct seed_for_matrix_A{2}).
  auto => |> &1 &2 H ??????rr  -> Hr;congr; rewrite Bytes32.tP => k kb.
  by rewrite !Bytes32.get_of_list // get_to_list initiE 1:/# /= nth_take 1,2:/# /= BytesSK.get_of_list 1:/# get_to_list.

(* ── Step 4: mu = H_mu tr m (spec simple) ───────────────────────────────
   Spec: mu <- H_mu tr m
   Jasmin: nothing (message representative computed next) *)
sp 1 0.

(* ── Step 5: derive_message_representative (Jasmin) ─────────────────────
   Spec: (mu already assigned above)
   Jasmin: message_representative <@ __derive_message_representative(...) *)
seq 0 1 : (#pre /\
    message_representative{2} =
      Array64.of_list witness (Bytes64.to_list mu{1})).
+ ecall{2} (derive_message_representative_ph
              (Array64.init (fun i => signing_key{2}.[64 + i]))
              (memread _m context_pointer{2} context_size{2})
              (memread _m message_pointer{2} message_size{2})).
  wp; skip => |> &1 &2 *; do split.
  + rewrite size_memread; smt(W64.to_uint_cmp). 
  + rewrite size_memread; smt(W64.to_uint_cmp). 
  + rewrite size_memread; smt(W64.to_uint_cmp). 
  + rewrite size_memread; smt(W64.to_uint_cmp). 
  move => ????; congr;congr;congr.
  + rewrite Bytes64.tP => k kb.
    by rewrite !Bytes64.get_of_list // get_to_list initiE 1:/# /= nth_take 1,2:/# nth_drop 1,2:/# BytesSK.of_listK ?size_to_list /#.
  by rewrite size_memread; smt(W64.to_uint_cmp). 

(* ── Step 6: rhopp = H_rhopp _K coins mu (spec simple) ─────────────────
   Spec: rhopp <- H_rhopp _K coins mu *)
sp 1 0.

(* ── Step 7: derive_seed_for_mask (Jasmin) ──────────────────────────────
   Spec: (rhopp already assigned above)
   Jasmin: seed_for_mask <@ derive_seed_for_mask(k, randomness, message_representative) *)
seq 0 1 : (#pre /\
    seed_for_mask{2} = Array64.of_list witness (Bytes64.to_list rhopp{1})).
+ ecall{2} (derive_seed_for_mask_ph
              (Array32.init (fun i => signing_key{2}.[32 + i]))
              randomness{2}
              message_representative{2}
              seed_for_mask{2}).
  wp; skip => |> &1 &2 <- *; rewrite /H_rhopp.
  rewrite !Bytes64.of_listK ?Keccak1600_Spec.size_SHAKE256 //;1,2: by rewrite size_take // size_drop // BytesSK.size_to_list /#.
  rewrite Bytes32.of_listK; 1: by rewrite size_take // size_drop // BytesSK.size_to_list /#.
  rewrite BytesSK.of_listK; 1: by rewrite size_to_list /#.
  congr;congr;congr.
  + congr;apply (eq_from_nth witness); 1: by rewrite size_to_list // size_take // size_drop // size_to_list /#.
    move => i; rewrite size_to_list /= => ib; rewrite nth_take 1,2:/# initiE 1:/# /= nth_drop /#.
    by rewrite of_listK ?Keccak1600_Spec.size_SHAKE256 //.


(* ── Step 9: Decode s1 (Jasmin) ─────────────────────────────────────────
   Jasmin: s1 <@ s1____decode(signing_key[128:768])
   Spec: (s1 already decoded in Step 1, via skDecode) *)
seq 0 1 : (#pre /\
    lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1{1} /\
    wpolylvec_srng (lvec_unflatten256 s1{2}) Eta Eta).
+ ecall{2} (s1_decode_ph (Array640.init (fun i => signing_key{2}.[128 + i]))).
  auto => |> &1 &2 8? rr Hfun Hrng.
  + rewrite Hfun tP => k kb.
    rewrite initiE 1:/# /= mapiE 1:/# /=;do congr.
    apply (eq_from_nth witness).
    + by rewrite size_to_list /= size_take 1:/# size_drop 1:/# BytesSK.size_to_list /#.
    move => i; rewrite size_to_list => ib.
    rewrite get_to_list nth_take 1,2:/# nth_drop 1,2:/#  BytesSK.get_to_list  BytesSK.get_of_list 1:/# get_to_list  initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= initiE /#.
    
(* ── Step 10: Decode s2 (Jasmin) ────────────────────────────────────────
   Jasmin: s2 <@ s2____decode(signing_key[768:1536]) *)
seq 0 1 : (#pre /\
    lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2{1} /\
    wpolykvec_srng (kvec_unflatten256 s2{2}) Eta Eta).
+ ecall{2} (s2_decode_ph (Array768.init (fun i => signing_key{2}.[768 + i]))).
  auto => |> &1 &2 10? rr Hfun Hrng.
  + rewrite Hfun tP => k kb.
    rewrite initiE 1:/# /= mapiE 1:/# /=;do congr.
    apply (eq_from_nth witness).
    + by rewrite size_to_list /= size_take 1:/# size_drop 1:/# BytesSK.size_to_list /#.
    move => i; rewrite size_to_list => ib.
    rewrite get_to_list nth_take 1,2:/# nth_drop 1,2:/#  BytesSK.get_to_list  BytesSK.get_of_list 1:/# get_to_list  initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= initiE /#.

   
(* ── Step 11: Decode t0 (Jasmin) ────────────────────────────────────────
   Jasmin: t0 <@ t0__decode(signing_key[1536:4032]) *)
seq 0 1 : (#pre /\
    lifts_wpolykvec (kvec_unflatten256 t0{2}) = t0{1} /\
    wpolykvec_srng (kvec_unflatten256 t0{2}) (dpow-1) dpow).
+ ecall{2} (t0_decode_ph (Array2496.init (fun i => signing_key{2}.[1536 + i]))).
  auto => |> &1 &2 12? rr Hfun Hrng.
  + rewrite Hfun tP => k kb.
    rewrite initiE 1:/# /= mapiE 1:/# /=;do congr; last 2 by smt().
    apply (eq_from_nth witness).
    + by rewrite size_to_list /= size_take 1:/# size_drop 1:/# BytesSK.size_to_list /#.
    move => i; rewrite size_to_list => ib.
    rewrite get_to_list nth_take 1,2:/# nth_drop 1,2:/#  BytesSK.get_to_list  BytesSK.get_of_list 1:/# get_to_list  initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= initiE /#.
    
(* ── Step 12: NTT s1/s2/t0 + loop variable inits ───────────────────────
   Jasmin: row_vector__ntt(s1); column_vector__ntt(s2); column_vector__ntt(t0)
           domain_separator_for_mask <- 0
           exit_rejection_sampling_loop <- 0
           kappa_exceeded <- 0
   Spec: (kappa <- 0, zh <- None already done; s1h/s2h/t0h from Step 2 above) *)
seq 0 3 : (#{/~s1{2}}{/~s2{2}}{/~t0{2}}pre /\
    lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1h{1} /\
    lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2h{1} /\
    lifts_wpolykvec (kvec_unflatten256 t0{2}) = t0h{1} /\
    wpolylvec_ntt_orng (lvec_unflatten256 s1{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 s2{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 t0{2})).
+ wp; ecall{2} (column_vector__ntt_ph t0{2}).
  wp; ecall{2} (column_vector__ntt_ph s2{2}).
  wp; ecall{2} (row_vector__ntt_ph s1{2}).
  auto => |> &1 &2 *.
  split; first by apply wpolylvec_srng_ntt_irng;
    apply (wpolylvec_srng_widen _ Eta Eta (q-1) (q-1)); smt(mldsa65_Eta).
  move => _ result Hs1_lift Hs1_orng.
  split; first by apply wpolykvec_srng_ntt_irng;
    apply (wpolykvec_srng_widen _ Eta Eta (q-1) (q-1)); smt(mldsa65_Eta).
  move => _ result0 Hs2_lift Hs2_orng.
  split; first by apply wpolykvec_srng_ntt_irng;
    apply (wpolykvec_srng_widen _ (dpow-1) dpow (q-1) (q-1)); smt().
  move => _ result1 Ht0_lift Ht0_orng.
  by rewrite Hs1_lift Hs2_lift Ht0_lift /#.

(* ── Rejection sampling loop + post-loop ──────────────────────────────── *)

seq 3 5 : (
liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
    wpolymat_urng (mat_unflatten256 matrix_A{2}) q /\
    seed_for_mask{2} = Array64.of_list witness (Bytes64.to_list rhopp{1}) /\
    message_representative{2} = Array64.of_list witness (Bytes64.to_list mu{1}) /\
    lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1h{1} /\
    lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2h{1} /\
    lifts_wpolykvec (kvec_unflatten256 t0{2}) = t0h{1} /\
    wpolylvec_ntt_orng (lvec_unflatten256 s1{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 s2{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 t0{2}) /\
    W16.to_uint domain_separator_for_mask{2} = kappa{1} * lvec /\
    (kappa_exceeded{2} = one) = (kappa_max <= kappa{1}) /\
    (kappa_exceeded{2} <> one => kappa_exceeded{2} = zero) /\
    (exit_rejection_sampling_loop{2} = zero) = (zh{1} = None /\ ! (kappa_max <= kappa{1})) /\
    (zh{1} = None => (kappa_max <= kappa{1})) /\
    (zh{1} <> None => last_norm_check_result{2} = W64.zero) /\
    (zh{1} = None /\ kappa_max <= kappa{1} => last_norm_check_result{2} = W64.one) /\
    (zh{1} <> None =>
       (ct{1} = BytesCT.init (fun i => commitment_hash{2}.[i]) /\
       lifts_wpolylvec (lvec_unflatten256 signer_response{2}) =  (oget zh{1}).`1 /\
       liftu_wpolykvec (kvec_unflatten256 hint_0{2}) = (oget zh{1}).`2 /\
       wpolykvec_urng (kvec_unflatten256 hint_0{2}) 2 /\
       count_nonzero_coeffs_kvec (liftu_wpolykvec (kvec_unflatten256 hint_0{2})) <= w_hint /\
       wpolylvec_srng (lvec_unflatten256 signer_response{2}) (gamma1-1) gamma1))
); last first.
(* ── Post-loop goal ─────────────────────────────────────────────────── *)
+ if {1}; last first.
  (* failure: zh = None /\ kappa_max <= kappa, so last_norm_check_result = W64.one *)
  + wp; call {2} (: true ==> true).
    + exact signature____encode_ll.
    auto => |> &1 &2 *.
    have -> : last_norm_check_result{2} = W64.one by smt().
    rewrite wordP => i ib.
    by rewrite minus_one /= /(`<<`) /(`|>>`) /= ib /= sarE initiE 1:/# /= nth_one /#.
  (* success: zh <> None, so last_norm_check_result = W64.zero *)
  wp; ecall (signature_encode commitment_hash{2} signer_response{2} hint_0{2}).
  auto => |> &1 &2 ?????????????; do split; 1..6:smt().
  + move => ?????? rr1 rr2 ?.
    have -> : last_norm_check_result{2} = W64.zero by smt().
    split; 1: by rewrite wordP /= minus_one /= /(`<<`) /(`|>>`) /= sarE negb_forall; exists 0 => /=.
    rewrite wordP => i ib.
    by rewrite  /(`<<`) /(`|>>`) /= sarE initiE 1:/# /=. 
     

(* ── Rejection sampling loop  ──────────────────────────────── *)

while (
    0 <= kappa{1} /\
    liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
    wpolymat_urng (mat_unflatten256 matrix_A{2}) q /\
    seed_for_mask{2} = Array64.of_list witness (Bytes64.to_list rhopp{1}) /\
    message_representative{2} = Array64.of_list witness (Bytes64.to_list mu{1}) /\
    lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1h{1} /\
    lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2h{1} /\
    lifts_wpolykvec (kvec_unflatten256 t0{2}) = t0h{1} /\
    wpolylvec_ntt_orng (lvec_unflatten256 s1{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 s2{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 t0{2}) /\
    W16.to_uint domain_separator_for_mask{2} = kappa{1} * lvec /\
    (kappa_exceeded{2} = W64.of_int 1) = (kappa_max <= kappa{1}) /\
    (kappa_exceeded{2} <> W64.of_int 1 => kappa_exceeded{2} = W64.zero) /\
    (exit_rejection_sampling_loop{2} = W64.of_int 0) =
      (zh{1} = None /\ ! (kappa_max <= kappa{1})) /\
    (zh{1} <> None => last_norm_check_result{2} = W64.zero) /\
    (zh{1} = None /\ kappa_max <= kappa{1} => last_norm_check_result{2} = W64.one) /\
    (zh{1} <> None =>
       ct{1} = BytesCT.init (fun i => commitment_hash{2}.[i]) /\
       lifts_wpolylvec (lvec_unflatten256 signer_response{2}) = (oget zh{1}).`1 /\
       liftu_wpolykvec (kvec_unflatten256 hint_0{2}) = (oget zh{1}).`2 /\
       wpolykvec_urng (kvec_unflatten256 hint_0{2}) 2 /\
       count_nonzero_coeffs_kvec (liftu_wpolykvec (kvec_unflatten256 hint_0{2})) <= w_hint /\
       wpolylvec_srng (lvec_unflatten256 signer_response{2}) (gamma1-1) gamma1)); last
         by auto => |>  &1 &2 *; rewrite !W64.to_uint_eq /=; do split;smt().

 (* ── Loop body ──────────────────────────────────────────────────────── *)
 seq 1 1 : (#{/~to_uint domain_separator_for_mask{2} = kappa{1} * lvec}pre /\
     lifts_wpolylvec (lvec_unflatten256 mask{2}) = y{1} /\
     wpolylvec_srng (lvec_unflatten256 mask{2}) (gamma1 - 1) gamma1 /\
     W16.to_uint domain_separator_for_mask{2} = (kappa{1} + 1) * lvec).
 + exlim seed_for_mask{2}, domain_separator_for_mask{2} => _seed _dom.
   call (mask_correct _seed _dom).
   auto => |> &1 &2 *; do split.
   + apply Bytes64.tP => k kb.
     + rewrite of_listK; 1: by rewrite Bytes64.size_to_list /=.
       by rewrite Bytes64.to_listK. 
   + by smt().
   + by move => _ _ result_R _ Hdom; smt().

 sp 3 0.
 seq 0 8 : (#pre /\
     lifts_wpolykvec (kvec_unflatten256 w0{2}) = w0{1} /\
     lifts_wpolykvec (kvec_unflatten256 w1{2}) = w1{1} /\
     wpolykvec_srng (kvec_unflatten256 w0{2}) (gamma2 - 1) gamma2 /\
     wpolykvec_urng (kvec_unflatten256 w1{2}) ((q-1) %/ (2*gamma2))).
   seq 0 2 : (#pre /\ mask_as_ntt{2} = mask{2}).
   + conseq (_: true ==> mask_as_ntt{2} = mask{2}); 1: smt().
     sp 0 1.
     while{2} (0 <= j{2} <= 5120 /\ j{2} %% 32 = 0 /\
               (forall i, 0 <= i < j{2} %/ w1_bits => mask_as_ntt{2}.[i] = mask{2}.[i]))
              (5120 - j{2}).
     + move => _ z; auto => |> &hr Hj_lo Hj_hi Hj_mod Hcopied Hguard.
       do split; 1,2,3,5: smt().
       move => i Hi_lo Hi_hi; rewrite Array1280.initiE 1:/# /=.
       rewrite get32_set256_direct_eq 1,2,3,4:/#.
       case (j{hr} %/ w1_bits <= i < j{hr} %/ w1_bits + 8) => Hi_region.
       + rewrite get256_direct_init32_bits32 1,2,3,4:/# /= /#.
       rewrite get32_init32 1:/# /=; apply Hcopied; smt().
     skip; move => &1 &2 Hj0; split; 1: smt().
     move => j_R mask_as_ntt_R; split; 1: smt().
     move => Hguard_neg [# Hj_lo Hj_hi Hj_mod Hcopied].
     apply Array1280.tP => k Hk; apply Hcopied; smt().
   wp; ecall{2} (column_vector____decompose_ph w{2}).
   wp; ecall{2} (column_vector____conditionally_add_modulus_ph w{2}).
   wp; ecall{2} (column_vector__invert_ntt_montgomery_ph w{2}).
   wp; ecall{2} (column_vector__reduce32_ph w{2}).
   wp; ecall{2} (row_vector____multiply_with_matrix_A_ph matrix_A{2} mask_as_ntt{2}).
   wp; ecall{2} (row_vector__ntt_ph mask_as_ntt{2}).
   auto => |> &1 &2 *.
   have Hbound := invntt_obound_fits_for_caddq.
   split; first by apply wpolylvec_srng_ntt_irng;
     apply (wpolylvec_srng_widen _ (gamma1-1) gamma1 (q-1) (q-1)); smt(mldsa65_gamma1).
   move => _ result Hntt_eq Hntt_orng.
   split; first exact (wpolylvec_ntt_orng_bmul_irng _ Hntt_orng).
   move => _ result0 Hmul_eq Hmul_srng.
   move => result1 Hred_eq Hred_srng.
   split; first by apply wpolykvec_bmul_orng_intt_irng;
     apply (wpolykvec_srng_widen _ ((q-1) %/ 2) ((q-1) %/ 2) (q-1) (q-1)); smt().
   move => _ result2 Hinvntt_eq Hinvntt_srng.
   split;
     first by apply (wpolykvec_srng_widen _ invntt_obound invntt_obound (q-1) (q-1)); smt().
   move => _ result3 Hcond_eq Hcond_urng.
   move => result4 Hw0_eq Hw1_eq Hw0_srng Hw1_urng.
   (* After `auto => |> &1 &2 *`, _A{1} and y{1} have been substituted out;
      goal uses (liftu_wpolymat (mat_unflatten256 matrix_A{2})) and
      (lifts_wpolylvec (lvec_unflatten256 mask{2})) directly. Chain via the
      ecall post equalities, no need for intermediate HA_lift / Hmask_lift. *)
   have Hreachable : lifts_wpolykvec (kvec_unflatten256 result3) =
                     invnttv (ntt_mulmxv (liftu_wpolymat (mat_unflatten256 matrix_A{2}))
                                         (nttv (lifts_wpolylvec (lvec_unflatten256 mask{2})))).
   + by rewrite Hcond_eq Hinvntt_eq Hred_eq Hmul_eq Hntt_eq.
   have Heq_liftu_lifts := wpolykvec_urng_lifts_eq_liftu _ Hcond_urng.
   have Hw1_lifts : lifts_wpolykvec (kvec_unflatten256 result4.`2) =
                    liftu_wpolykvec (kvec_unflatten256 result4.`2).
   + apply wpolykvec_urng_lifts_eq_liftu;
     apply (wpolykvec_urng_widen _ ((q-1) %/ (2*gamma2)) q); smt(mldsa65_gamma2).
   rewrite Hw0_eq Hw1_lifts Hw1_eq -Heq_liftu_lifts Hreachable; done.

 seq 3 3 : (#pre /\
     ct{1} = BytesCT.init (fun i => commitment_hash{2}.[i]) /\
     lifts_wpoly verifier_challenge{2} = c{1} /\
     wpoly_ntt_irng verifier_challenge{2}).
 + seq 0 1 : (#pre /\ BytesW1.of_list (to_list commitment_encoded{2}) = w1Encode w1{1}); last first.
   + inline {1} SIB_RO(MLDSA_XOF_SIB).get.
     sp 3 0.
     wp.
     call sample_challenge_correct.
     ecall{2} (derive_commitment_hash_ph message_representative{2} commitment_encoded{2}).
     auto => |> &1 &2 *.
     rewrite Array64.of_listK 1:Bytes64.size_to_list //.
     rewrite Bytes64.to_listK.
     rewrite Array48.of_listK;1: by rewrite BytesCT.size_to_list;  smt(mldsa65_lambda).
     rewrite BytesCT.to_listK.
     split; first by smt().
     move => Hcteq result_L result_R Hrl Hsrng; split.
     + rewrite Hcteq; apply BytesCT.tP => i Hi; rewrite BytesCT.initiE 1:/# /=.
       smt(Array48.get_of_list BytesCT.size_to_list BytesCT.get_to_list mldsa65_lambda).
     apply wpoly_srng_ntt_irng; apply (wpoly_srng_widen _ 1 1 (q-1) (q-1)); smt().
   (* Step 1: commitment_encode bridge. Flatten/map algebra tying
      commitment_encode's output to w1Encode — pattern from verify.ec:200-219. *)
   ecall{2} (commitment_encode_ph w1{2}).
   auto => |> &1 &2 *.
   split; first by smt(mldsa65_gamma2).
   move => _ result1 Hunflat.
   rewrite /w1Encode.
   have Hw1eq : liftu_wpolykvec (kvec_unflatten256 w1{2}) =
                lifts_wpolykvec (kvec_unflatten256 w1{2}).
   + rewrite eq_sym; apply wpolykvec_urng_lifts_eq_liftu.
     apply (wpolykvec_urng_widen _ (8380416 %/ (2 * gamma2)) q); smt(mldsa65_gamma2).
   have Hb_w1 : (q - 1) %/ (2 * gamma2) - 1 = b_w1
     by rewrite /b_w1 /=; smt(mldsa65_gamma2).
   rewrite Hb_w1; apply BytesW1.tP => k kb.
   rewrite !BytesW1.get_of_list 1,2:/# get_to_list (kvec_unflatten128iE result1 k) 1:/# Hunflat.
   rewrite KArray.mapiE; 1: smt(mldsa65_kvec).
   rewrite /= Array128.get_of_list 1:/# (BitChunking.nth_flatten witness 128).
   + rewrite allP => s /mapP [wi [_ ->]] /=.
     by rewrite size_SimpleBitPack' /b_w1 /= /#.
   rewrite (nth_map witness); 1: by rewrite size_mkseq; smt(mldsa65_kvec).
   rewrite nth_mkseq; 1: smt(mldsa65_kvec).
   by rewrite Hw1eq /= /#.

sp 6 0.
seq 1 0 : #pre; 1: by auto.

 seq 0 1 : (#{~lifts_wpoly verifier_challenge{2} = c{1}}{~wpoly_ntt_irng verifier_challenge{2}}pre /\
     wpoly_ntt_orng verifier_challenge{2} /\
     lifts_wpoly verifier_challenge{2} = ch{1}).
 + ecall{2} (polynomial__ntt_ph verifier_challenge{2}).
   by auto => |> /#.

 (* Jasmin pure: infinity_norm_check_result <- 0 *)
 sp 0 1.

 (* ── Step 1: cs2 norm check ──────────────────────────────── *)
 seq 0 1 : (#{~infinity_norm_check_result{2} = W64.zero}pre /\
     (infinity_norm_check_result{2} = W64.zero \/ infinity_norm_check_result{2} = W64.one) /\
     (infinity_norm_check_result{2} = W64.zero =>
        wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 w0_minus_cs2{2}) /\
        lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2{2}) =
          lifts_wpolykvec (kvec_unflatten256 w0{2}) -
          PolyKVec.invnttv (PolyKVec.ntt_smul
            (lifts_wpoly verifier_challenge{2})
            (lifts_wpolykvec (kvec_unflatten256 s2{2})))) /\
     (infinity_norm_check_result{2} = W64.zero <=>
        PolyKVec.infnorm_lt
          (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
           PolyKVec.invnttv (PolyKVec.ntt_smul
             (lifts_wpoly verifier_challenge{2})
             (lifts_wpolykvec (kvec_unflatten256 s2{2}))))
          (gamma2 - Beta))).
 + ecall{2} (__apply_cs2_and_check_norm_ph
              w0_minus_cs2{2} w0{2} s2{2} verifier_challenge{2}
              W64.zero).
   by auto => |>.

 (* ── Step 2: ct0 norm check ──────────────────────────────── *)
 seq 0 1 : (#{~(infinity_norm_check_result{2} = W64.zero <=>
               PolyKVec.infnorm_lt
                 (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
                  PolyKVec.invnttv (PolyKVec.ntt_smul
                    (lifts_wpoly verifier_challenge{2})
                    (lifts_wpolykvec (kvec_unflatten256 s2{2}))))
                 (gamma2 - Beta))}pre /\
     (infinity_norm_check_result{2} = W64.zero \/ infinity_norm_check_result{2} = W64.one) /\
     (* Conditional range from ct0 add: tightest bound from norm checks. *)
     (infinity_norm_check_result{2} = W64.zero =>
        wpolykvec_srng (kvec_unflatten256 w0_minus_cs2_plus_ct0{2}) (2*gamma2 - Beta - 2) (2*gamma2 - Beta - 2)) /\
     (infinity_norm_check_result{2} = W64.zero =>
        let ct0 = PolyKVec.invnttv (PolyKVec.ntt_smul
                    (lifts_wpoly verifier_challenge{2})
                    (lifts_wpolykvec (kvec_unflatten256 t0{2}))) in
        PolyKVec.infnorm_lt ct0 gamma2 /\
        lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0{2}) =
          lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2{2}) + ct0) /\
     (infinity_norm_check_result{2} = W64.zero <=>
        PolyKVec.infnorm_lt
          (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
           PolyKVec.invnttv (PolyKVec.ntt_smul
             (lifts_wpoly verifier_challenge{2})
             (lifts_wpolykvec (kvec_unflatten256 s2{2}))))
          (gamma2 - Beta) /\
        PolyKVec.infnorm_lt
          (PolyKVec.invnttv (PolyKVec.ntt_smul
             (lifts_wpoly verifier_challenge{2})
             (lifts_wpolykvec (kvec_unflatten256 t0{2}))))
          gamma2)).
 + ecall{2} (__apply_ct0_and_check_norm_ph
              w0_minus_cs2_plus_ct0{2} w0_minus_cs2{2} t0{2}
              verifier_challenge{2} infinity_norm_check_result{2}).
   by auto => |> &1 &2 *; smt().

 (* ── Step 3: z norm check ──────────────────────────────── *)
 seq 0 2 : (#{~(infinity_norm_check_result{2} = W64.zero <=>
               PolyKVec.infnorm_lt
                 (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
                  PolyKVec.invnttv (PolyKVec.ntt_smul
                    (lifts_wpoly verifier_challenge{2})
                    (lifts_wpolykvec (kvec_unflatten256 s2{2}))))
                 (gamma2 - Beta) /\
               PolyKVec.infnorm_lt
                 (PolyKVec.invnttv (PolyKVec.ntt_smul
                    (lifts_wpoly verifier_challenge{2})
                    (lifts_wpolykvec (kvec_unflatten256 t0{2}))))
                 gamma2)}pre /\
     (infinity_norm_check_result{2} = W64.zero \/ infinity_norm_check_result{2} = W64.one) /\
     (infinity_norm_check_result{2} = W64.zero =>
        wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 signer_response{2}) /\
        lifts_wpolylvec (lvec_unflatten256 signer_response{2}) =
          lifts_wpolylvec (lvec_unflatten256 mask{2}) +
          PolyLVec.invnttv (PolyLVec.ntt_smul
            (lifts_wpoly verifier_challenge{2})
            (lifts_wpolylvec (lvec_unflatten256 s1{2}))) /\
        wpolylvec_srng (lvec_unflatten256 signer_response{2}) (gamma1 - 1) gamma1) /\
     (infinity_norm_check_result{2} = W64.zero <=>
        PolyKVec.infnorm_lt
          (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
           PolyKVec.invnttv (PolyKVec.ntt_smul
             (lifts_wpoly verifier_challenge{2})
             (lifts_wpolykvec (kvec_unflatten256 s2{2}))))
          (gamma2 - Beta) /\
        PolyKVec.infnorm_lt
          (PolyKVec.invnttv (PolyKVec.ntt_smul
             (lifts_wpoly verifier_challenge{2})
             (lifts_wpolykvec (kvec_unflatten256 t0{2}))))
          gamma2 /\
        PolyLVec.infnorm_lt
          (lifts_wpolylvec (lvec_unflatten256 mask{2}) +
           PolyLVec.invnttv (PolyLVec.ntt_smul
             (lifts_wpoly verifier_challenge{2})
             (lifts_wpolylvec (lvec_unflatten256 s1{2}))))
          (gamma1 - Beta))).
 + wp. ecall{2} (__compute_z_and_check_norm_ph
              s1{2} verifier_challenge{2} mask{2} signer_response{2}
              infinity_norm_check_result{2}).
   by auto => |> &1 &2 *; smt().

 (* ── Step 4: make_hint ────────────────────────────────────── *)
 seq 0 2 : (#{~(infinity_norm_check_result{2} = zero <=>
   infnorm_lt
     (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
      invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolykvec (kvec_unflatten256 s2{2}))))
     (gamma2 - Beta) /\
   infnorm_lt (invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolykvec (kvec_unflatten256 t0{2}))))
     gamma2 /\
   infnorm_lt
     (lifts_wpolylvec (lvec_unflatten256 mask{2}) +
      invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolylvec (lvec_unflatten256 s1{2}))))
     (gamma1 - Beta))}pre /\
     (infinity_norm_check_result{2} = W64.zero \/ infinity_norm_check_result{2} = W64.one) /\
     (infinity_norm_check_result{2} = W64.zero =>
          liftu_wpolykvec (kvec_unflatten256 hint_0{2}) =
            MakeHintImpl
              (lifts_wpolykvec (kvec_unflatten256 w1{2}))
              (lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0{2}))) /\
     (PolyKVec.infnorm_lt
        (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
         PolyKVec.invnttv (PolyKVec.ntt_smul
           (lifts_wpoly verifier_challenge{2})
           (lifts_wpolykvec (kvec_unflatten256 s2{2}))))
        (gamma2 - Beta) /\
      PolyKVec.infnorm_lt
        (PolyKVec.invnttv (PolyKVec.ntt_smul
           (lifts_wpoly verifier_challenge{2})
           (lifts_wpolykvec (kvec_unflatten256 t0{2}))))
        gamma2 /\
      PolyLVec.infnorm_lt
        (lifts_wpolylvec (lvec_unflatten256 mask{2}) +
         PolyLVec.invnttv (PolyLVec.ntt_smul
           (lifts_wpoly verifier_challenge{2})
           (lifts_wpolylvec (lvec_unflatten256 s1{2}))))
        (gamma1 - Beta) =>
      lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0{2}) =
        (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
         PolyKVec.invnttv (PolyKVec.ntt_smul
           (lifts_wpoly verifier_challenge{2})
           (lifts_wpolykvec (kvec_unflatten256 s2{2})))) +
        PolyKVec.invnttv (PolyKVec.ntt_smul
           (lifts_wpoly verifier_challenge{2})
           (lifts_wpolykvec (kvec_unflatten256 t0{2})))) /\
     (infinity_norm_check_result{2} = W64.zero =>
        wpolykvec_urng (kvec_unflatten256 hint_0{2}) 2) /\
        
     (infinity_norm_check_result{2} = W64.zero <=>
        (PolyKVec.infnorm_lt
          (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
           PolyKVec.invnttv (PolyKVec.ntt_smul
             (lifts_wpoly verifier_challenge{2})
             (lifts_wpolykvec (kvec_unflatten256 s2{2}))))
          (gamma2 - Beta) /\
        PolyKVec.infnorm_lt
          (PolyKVec.invnttv (PolyKVec.ntt_smul
             (lifts_wpoly verifier_challenge{2})
             (lifts_wpolykvec (kvec_unflatten256 t0{2}))))
          gamma2 /\
        PolyLVec.infnorm_lt
          (lifts_wpolylvec (lvec_unflatten256 mask{2}) +
           PolyLVec.invnttv (PolyLVec.ntt_smul
             (lifts_wpoly verifier_challenge{2})
             (lifts_wpolylvec (lvec_unflatten256 s1{2}))))
          (gamma1 - Beta) /\
        PolyKVec.hammw
          (MakeHintImpl
              (lifts_wpolykvec (kvec_unflatten256 w1{2}))
              (lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0{2})))
          w_hint))).
 + wp. ecall{2} (__make_hint_vector_ph
                   w0_minus_cs2_plus_ct0{2} w1{2} hint_0{2}
                   infinity_norm_check_result{2}).
   auto => |> &1 &2 *;smt().  
 auto => |> &1 &2 ??????????????????????? Hh0 ??Hz.
 (* Instantiate the kappa-counter machine-arithmetic helper. *)
 have Hkbu :=
   kappa_bit_update kappa{1} kappa_exceeded{2} domain_separator_for_mask{2}
     _ Hkappa_max _ _ _; 1..4: smt().
 move : Hkbu => /= [Hkappa_R_one Hkappa_R_dicho].
 (* Goal: wpolykvec_srng w0_minus_cs2_plus_ct0 (gamma2-1) gamma2 /\ (srng => forall result1, ...) *)
 split.
 + move => Hn1 Hn2;split.
   + move => Hn3?.
     have := Hz.
     have -> /= : infnorm_lt
  (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
   invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolykvec (kvec_unflatten256 s2{2})))) (
  gamma2 - Beta) by smt().
  have -> /= : infnorm_lt
  (lifts_wpolylvec (lvec_unflatten256 mask{2}) +
   invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolylvec (lvec_unflatten256 s1{2})))) (
  gamma1 - Beta) by smt().
  have -> : infnorm_lt (invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolykvec (kvec_unflatten256 t0{2})))) gamma2 by smt().
  have -> /=: PolyKVec.hammw
  (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 w1{2})) (lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0{2}))) w_hint by smt().

  move => H0.
     do split;1..3,5,6,7,8:smt().
     + rewrite  H0 /=;smt(or64_ne0). search count_nonzero_coeffs_kvec .
     + by smt(hammw_count_nonzero).
     + by smt().
     + rewrite  H0 /=;smt(or64_ne0). search count_nonzero_coeffs_kvec .
 + move => Hn3.
   have := Hz.
   have  -> /=: !(infnorm_lt
  (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
   invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolykvec (kvec_unflatten256 s2{2})))) (
  gamma2 - Beta) /\
infnorm_lt (invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolykvec (kvec_unflatten256 t0{2})))) gamma2 /\
infnorm_lt
  (lifts_wpolylvec (lvec_unflatten256 mask{2}) +
   invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolylvec (lvec_unflatten256 s1{2})))) (
  gamma1 - Beta) /\
hammw
  (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 w1{2})) (lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0{2})))
  w_hint ) by smt().

  move => H0.
  have H1 : infinity_norm_check_result{2} = one by smt().
   + do split;1..3:smt(). 
     + rewrite  H1 /=;smt(or64_ne0).
     + smt().
     + rewrite  H1 /=;smt(or64_ne0).
     + rewrite  H1 /=;smt(or64_ne0).
       
 + move => Hn3.
   have := Hz.
   have  -> /=: !(infnorm_lt
  (lifts_wpolykvec (kvec_unflatten256 w0{2}) -
   invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolykvec (kvec_unflatten256 s2{2})))) (
  gamma2 - Beta) /\
infnorm_lt (invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolykvec (kvec_unflatten256 t0{2})))) gamma2 /\
infnorm_lt
  (lifts_wpolylvec (lvec_unflatten256 mask{2}) +
   invnttv (ntt_smul (lifts_wpoly verifier_challenge{2}) (lifts_wpolylvec (lvec_unflatten256 s1{2})))) (
  gamma1 - Beta) /\
hammw
  (MakeHintImpl (lifts_wpolykvec (kvec_unflatten256 w1{2})) (lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0{2})))
  w_hint ) by smt().
  move => H0.
  have H1 : infinity_norm_check_result{2} = one by smt().
   + do split;1..3:smt(). 
     + rewrite  H1 /=;smt(or64_ne0).
     + smt().
     + rewrite  H1 /=;smt(or64_ne0).
     + rewrite  H1 /=;smt(or64_ne0).
qed.
