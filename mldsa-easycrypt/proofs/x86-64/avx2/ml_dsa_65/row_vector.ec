require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Hashing
                           Signature Challenge Common_modular Common_ntt.

require import CircuitBindings Bindings XArray48.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

require import Polynomial.
                         
import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq.

require import Array2 Array32 Array48 Array64 Array256 Array768 Array1280 Array1536
               Array1920 Array1952 Array3309 Array7680.
               require import WArray48.

require import BitEncoding.
from CryptoSpecs require import JWordList.
import BitChunking.

lemma or64_ne0 w1 w2 :
        w1 `|` w2 <> W64.zero <=>
        (w1 <> W64.zero \/ w2 <> W64.zero).
have ? := W64.wordP w1 w2.
have ? := W64.orwE w1 w2.
split => H; 1: by smt(W64.orw0 W64.or0w W64.zerowE).
by elim H; rewrite !wordP /= negb_forall /= /#.
qed.

(* ================================================================== *)
(* row_vector__ntt                                                      *)
(* Applies forward NTT to each of 5 polynomials.                        *)
(* Calls polynomial__ntt in a 5-iteration loop.                         *)
(* Spec: nttv from VecMat.ec                                            *)
(* ================================================================== *)

lemma row_vector__ntt_ll : islossless M.row_vector__ntt.
proof.
proc.
while (0 <= i <= 5) (5 - i); last by auto => /#.
move => *.
wp; call polynomial__ntt_ll.
by auto => /#.
qed.

lemma row_vector__ntt_correct (_v : W32.t Array1280.t) :
    hoare [ M.row_vector__ntt :
        vector = _v /\
        wpolylvec_ntt_irng (lvec_unflatten256 _v)
        ==>
        lifts_wpolylvec (lvec_unflatten256 res) =
          nttv (lifts_wpolylvec (lvec_unflatten256 _v)) /\
        wpolylvec_ntt_orng (lvec_unflatten256 res)
    ].
proof.
have lvec_val := mldsa65_lvec.
proc.
while (0 <= i <= 5 /\
       wpolylvec_ntt_irng (lvec_unflatten256 _v) /\
       (forall k, 0 <= k < i =>
         lifts_wpoly (lvec_unflatten256 vector).[k] =
           ntt (lifts_wpoly (lvec_unflatten256 _v).[k]) /\
         wpoly_ntt_orng (lvec_unflatten256 vector).[k]) /\
       (forall k, i <= k < 5 =>
         (lvec_unflatten256 vector).[k] = (lvec_unflatten256 _v).[k])
      ); last first.
+ (* Exit: combine per-component facts into vector-level properties *)
  auto => |> Hrng_pre; split; 1: smt().
  move => i0 v0 Hng Hi1 Hi2 Hdone Huntouched; split.
  + apply LArray.tP => k kb.
    rewrite /lifts_wpolylvec mapiE; 1: smt(mldsa65_lvec).
    rewrite /nttv mapiE; 1: smt(mldsa65_lvec).
    rewrite mapiE; 1: smt(mldsa65_lvec).
    by have /= [-> _] := Hdone k _; smt().
  + by rewrite /wpolylvec_ntt_orng allP => k kb; have [_ ?] := Hdone k _; smt().
wp; ecall (polynomial__ntt_correct
             (Array256.init (fun j => vector.[i * 256 + j]))).
auto => /> &hr Hi1 Hi2 Hrng_pre Hprocessed Huntouched Hguard; split.
+ (* Pre for polynomial__ntt: slice of vector at i is ntt_irng *)
  rewrite -lvec_slice_eq; 1,2: smt().
  have -> : i{hr} * n %/ n = i{hr} by smt().
  rewrite (Huntouched i{hr} _); 1: smt().
  by move: Hrng_pre; rewrite /wpolylvec_ntt_irng LArray.allP => H; apply H; smt().
+ (* Post: invariant at i+1 *)
  move => _ result Hlifts Hrng; do split; 1,2: smt().
  + (* Processed components k < i+1 *)
    move => k ? Hk.
    have /= Hwb := lvec_unflatten256_writeback_iE vector{hr} result (i{hr} * 256) k _ _;
      1,2: smt().
    case (k = i{hr}) => Hki.
    + subst k; rewrite Hwb ifT; 1: smt().
      split; last exact Hrng.
      rewrite Hlifts; congr.
      have /= <- := Huntouched i{hr} _; 1: smt().
      by rewrite -lvec_slice_eq; smt().
    + rewrite Hwb ifF; 1: smt().
      by have := Hprocessed k _; smt().
  + (* Untouched components k >= i+1 *)
    move => k ? Hk.
    have /= Hwb := lvec_unflatten256_writeback_iE vector{hr} result (i{hr} * 256) k _ _;
      1,2: smt().
    rewrite Hwb ifF; 1: smt().
    by have := Huntouched k _; smt().
qed.

lemma row_vector__ntt_ph (_v : W32.t Array1280.t) :
    phoare [ M.row_vector__ntt :
        vector = _v /\
        wpolylvec_ntt_irng (lvec_unflatten256 _v)
        ==>
        lifts_wpolylvec (lvec_unflatten256 res) =
          nttv (lifts_wpolylvec (lvec_unflatten256 _v)) /\
        wpolylvec_ntt_orng (lvec_unflatten256 res)
    ] = 1%r
  by conseq row_vector__ntt_ll (row_vector__ntt_correct _v).

lemma row_vector____check_infinity_norm_correct (_a : W32.t Array1280.t) (_threshold : int) :
    phoare [ M.row_vector____check_infinity_norm :
       _threshold = (1 `<<` gamma1m1_bits) - 49 * w1_bits /\
       arg.`1 = _a /\ arg.`2 = _threshold /\
       wpolylvec_srng (lvec_unflatten256 _a) (gamma1-1) gamma1 
        ==>
        (wpolylvec_infnorm_lt _threshold (lvec_unflatten256 _a) => res = W64.zero) /\
        (!wpolylvec_infnorm_lt _threshold (lvec_unflatten256 _a) => res <> W64.zero)
    ] = 1%r.
proof.
have Hlvec := mldsa65_lvec.
have Hgamma1 := mldsa65_gamma1.
  
rewrite /(`<<`) /=.
proc => /=.
while (0 <= i <= 5 /\ threshold = _threshold /\ vector = _a /\ _threshold = 524092 /\
       wpolylvec_srng (lvec_unflatten256 _a) (gamma1 - 1) gamma1  /\
       ((forall k, 0<=k<i =>
          wpoly_srng (524092-1) (524092-1) (lvec_unflatten256 _a).[k]) => result = W64.zero) /\
        (! (forall k, 0<=k<i =>
          wpoly_srng (524092-1) (524092-1) (lvec_unflatten256 _a).[k]) => result <> W64.zero)) (5 - i); last first.
+ auto => |> ?; split;1:smt().
  move => i rr;split;1:smt().
  move => ??? Ht Hf; rewrite /wpolylvec_infnorm_lt /wpolylvec_srng !allP /= /#.

 move => ?.
 exlim i => _i.
 wp; call (polynomial____check_infinity_norm_ph ((lvec_unflatten256 _a).[_i]) _threshold).
 rewrite /(`<<`) /=; auto => |> &hr ??Hrng Ht Hf ?;split.
 + split.
   + by rewrite tP => k kb; rewrite initiE 1:/# /= /lvec_unflatten256 initiE 1:/# /= get_of_list /= 1:/# nth_sub /#.
   +  move : Hrng; rewrite /wpolylvec_srng /wpoly_srng !allP /= => H.
      have := H _i _;1:smt().
      by rewrite allP /#. 

move => H H0 rr0 Htp Hfp;do split;1,2,5..:smt().
+ case (result{hr} = W64.zero) => ?; smt(W64.or0w).
+ case (result{hr} = W64.zero) => HH.
  + move => ?; have Hj : !wpoly_srng 524091 524091 (lvec_unflatten256 _a).[_i] by smt().
    move : Hfp; rewrite /wpoly_infnorm_lt /= Hj /= => ->;apply or64_ne0; smt(W64.to_uint_eq W64.of_uintK W64.to_uintK W64.to_uint_cmp pow2_64).
  + move => ?; move : HH.
    by smt(or64_ne0).
qed.

(* ================================================================== *)
(* row_vector____dot_product                                            *)
(* Computes dot product of two row vectors (5 polynomials each):       *)
(*   output = sum_{i=0}^{4} pmmar(lhs[i], rhs[i])                    *)
(* Calls polynomial____zero, polynomial__pointwise_montgomery_multiply *)
(* _and_reduce, polynomial____pointwise_add_to_total in a 5-iter loop.*)
(* Spec: ntt_dotp from VecMat.ec                                       *)
(* ================================================================== *)

lemma row_vector____dot_product_ll : islossless M.row_vector____dot_product.
proof.
proc.
while (0 <= i <= 5) (5 - i); last first.
+ wp; call polynomial____zero_ll.
  by auto => /#.
move => *.
wp; call polynomial____pointwise_add_to_total_ll.
wp; call polynomial__pointwise_montgomery_multiply_and_reduce_ll.
by auto => /#.
qed.

lemma row_vector____dot_product_correct
      (_out : W32.t Array256.t)
      (_lhs : W32.t Array1280.t) (_rhs : W32.t Array1280.t) :
    hoare [ M.row_vector____dot_product :
        output = _out /\ lhs = _lhs /\ rhs = _rhs /\
        wpolylvec_bmul_irng (lvec_unflatten256 _lhs) /\
        wpolylvec_bmul_irng (lvec_unflatten256 _rhs)
        ==>
        lifts_wpoly res = ntt_dotp (lifts_wpolylvec (lvec_unflatten256 _lhs))
                                    (lifts_wpolylvec (lvec_unflatten256 _rhs)) /\
        wpoly_srng (lvec * (q-1)) (lvec * (q-1)) res
    ].
proof.
have lvec_val := mldsa65_lvec.
proc.
while (0 <= i <= 5 /\ lhs = _lhs /\ rhs = _rhs /\
       wpolylvec_bmul_irng (lvec_unflatten256 _lhs) /\
       wpolylvec_bmul_irng (lvec_unflatten256 _rhs) /\
       lifts_wpoly output =
         dotp_partial (lifts_wpolylvec (lvec_unflatten256 _lhs))
                      (lifts_wpolylvec (lvec_unflatten256 _rhs)) i /\
       wpoly_srng (i * (q-1)) (i * (q-1)) output
      ); last first.
+ (* Exit + pre-loop: zero then initial invariant *)
  wp; ecall (polynomial____zero_correct output). wp.
  auto => /> Hbmul_lhs Hbmul_rhs result Hzero Hsrng; split.
  + (* Initial invariant at i=0: lifts of zero = dotp_partial 0 *)
    rewrite /dotp_partial /= /lifts_wpoly /poly_zero.
    apply Array256.tP => j jb.
    rewrite mapiE; 1: smt().
    rewrite /= Hzero; 1: smt().
    by rewrite (iota0 0 0) //= /create initiE 1:/# /= /to_sint /= /smod /= /zero.
  + (* Exit: i=5, dotp_partial 5 = ntt_dotp *)
    move => i0 out0 Hng Hi1 Hi2 Hlifts Hsrng0.
    have Hi0 : i0 = lvec by smt(mldsa65_lvec).
    split.
    + by rewrite Hlifts Hi0 dotp_partial_ntt_dotp.
    by subst i0; exact Hsrng0.
(* Loop body: pmmar then add_to_total *)
wp; ecall (polynomial____pointwise_add_to_total_correct output product (i * (q-1)) (q-1)).
ecall (polynomial__pointwise_montgomery_multiply_and_reduce_correct
         product
         (Array256.init (fun j => lhs.[(256 * i) + j]))
         (Array256.init (fun j => rhs.[(256 * i) + j]))).
auto => /> &hr Hi1 Hi2 Hbmul_lhs Hbmul_rhs Hlifts Hsrng Hguard.
split.
+ (* bmul preconditions *)
  split.
  - have /= Heq_lhs := lvec_slice_eq _lhs (256 * i{hr}) _ _; 1,2: smt().
    rewrite -Heq_lhs.
    by move: Hbmul_lhs; rewrite /wpolylvec_bmul_irng LArray.allP => H; apply H; smt().
  - have /= Heq_rhs := lvec_slice_eq _rhs (256 * i{hr}) _ _; 1,2: smt().
    rewrite -Heq_rhs.
    by move: Hbmul_rhs; rewrite /wpolylvec_bmul_irng LArray.allP => H; apply H; smt().
+ (* continuation after pmmar *)
  move => _ _ product Hbmul_eq Hbmul_rng; split; 1: smt().
  move => Hoverflow result0 Hadd_eq Hadd_rng.
  do split; 1,2: smt().
  + (* lifts: dotp_partial at i+1 *)
    have Hlhs_slice : lifts_wpoly (init (fun j => _lhs.[n * i{hr} + j])) =
        (lifts_wpolylvec (lvec_unflatten256 _lhs)).[i{hr}].
    + rewrite /lifts_wpolylvec mapiE; 1: smt(mldsa65_lvec).
      by rewrite -lvec_slice_eq; smt().
    have Hrhs_slice : lifts_wpoly (init (fun j => _rhs.[n * i{hr} + j])) =
        (lifts_wpolylvec (lvec_unflatten256 _rhs)).[i{hr}].
    + rewrite /lifts_wpolylvec mapiE; 1: smt(mldsa65_lvec).
      by rewrite -lvec_slice_eq; smt().
    rewrite Hadd_eq Hlifts Hbmul_eq Hlhs_slice Hrhs_slice dotp_partialS; 1: smt().
    pose a := dotp_partial _ _.
    pose b := basemul _ _.
    by rewrite Rq_addC.
  + (* range: (i+1)*(q-1) *)
    by have -> : (i{hr} + 1) * (q - 1) = i{hr} * (q - 1) + (q - 1) by ring.
qed.

lemma row_vector____dot_product_ph
      (_out : W32.t Array256.t)
      (_lhs : W32.t Array1280.t) (_rhs : W32.t Array1280.t) :
    phoare [ M.row_vector____dot_product :
        output = _out /\ lhs = _lhs /\ rhs = _rhs /\
        wpolylvec_bmul_irng (lvec_unflatten256 _lhs) /\
        wpolylvec_bmul_irng (lvec_unflatten256 _rhs)
        ==>
        lifts_wpoly res = ntt_dotp (lifts_wpolylvec (lvec_unflatten256 _lhs))
                                    (lifts_wpolylvec (lvec_unflatten256 _rhs)) /\
        wpoly_srng (lvec * (q-1)) (lvec * (q-1)) res
    ] = 1%r
  by conseq row_vector____dot_product_ll
            (row_vector____dot_product_correct _out _lhs _rhs).

(* ================================================================== *)
(* row_vector____multiply_with_matrix_A                                 *)
(* Computes A * v where A is 6x5 matrix and v is 5-element row vector.*)
(* Calls row_vector____dot_product in a 6-iteration loop.              *)
(* Spec: ntt_mulmxv from VecMat.ec                                     *)
(* ================================================================== *)

lemma row_vector____multiply_with_matrix_A_ll :
    islossless M.row_vector____multiply_with_matrix_A.
proof.
proc.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *.
wp; call row_vector____dot_product_ll.
by auto => /#.
qed.

lemma row_vector____multiply_with_matrix_A_correct
      (_mat : W32.t Array7680.t) (_vec : W32.t Array1280.t) :
    hoare [ M.row_vector____multiply_with_matrix_A :
        matrix_A = _mat /\ vector = _vec /\
        wpolymat_urng (mat_unflatten256 _mat) q /\
        wpolylvec_bmul_irng (lvec_unflatten256 _vec)
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          ntt_mulmxv (liftu_wpolymat (mat_unflatten256 _mat))
                     (lifts_wpolylvec (lvec_unflatten256 _vec)) /\
        wpolykvec_srng (kvec_unflatten256 res) (lvec * (q-1)) (lvec * (q-1))
    ].
proof.
have lvec_val := mldsa65_lvec.
have kvec_val := mldsa65_kvec.
proc.
while (0 <= i <= 6 /\ matrix_A = _mat /\ vector = _vec /\
       wpolymat_urng (mat_unflatten256 _mat) q /\
       wpolylvec_bmul_irng (lvec_unflatten256 _vec) /\
       (forall k, 0 <= k < i =>
          (lifts_wpolykvec (kvec_unflatten256 out)).[k] =
          ntt_dotp (row (lifts_wpolymat (mat_unflatten256 _mat)) k)
                   (lifts_wpolylvec (lvec_unflatten256 _vec)) /\
          wpoly_srng (lvec * (q-1)) (lvec * (q-1)) (kvec_unflatten256 out).[k])
      ); last first.
+ (* Exit + pre-loop *)
  auto => /> Hmurng Hvbmul; split; 1: smt().
  move => i out Hng Hi1 Hi2 Hinv; have {Hi2} Hi2 : i = 6 by smt().
  subst i.
  (* lifts_wpolymat = liftu_wpolymat under urng q *)
  have Hlifts_eq_liftu :
      lifts_wpolymat (mat_unflatten256 _mat) = liftu_wpolymat (mat_unflatten256 _mat).
  + rewrite /lifts_wpolymat /liftu_wpolymat.
    apply KLMatrix.tP => j jb.
    rewrite !mapiE 1,2:/# /=.
    move: Hmurng; rewrite /wpolymat_urng KLMatrix.allP => Hj.
    apply wpoly_urng_lifts_eq_liftu.
    by apply (Hj j _); smt().
  split.
  + rewrite /ntt_mulmxv; apply KArray.tP => k kb.
    rewrite KArray.initiE 1:/# /= -Hlifts_eq_liftu.
    by have /= [-> _] := Hinv k _; smt().
  + rewrite /wpolykvec_srng KArray.allP => k kb.
    by have /= [_ ?] := Hinv k _; smt().

(* Loop body *)
wp; ecall (row_vector____dot_product_correct
            (Array256.init (fun j => out.[256 * i + j]))
            (Array1280.init (fun j => matrix_A.[5 * 256 * i + j]))
            vector).
auto => /> &hr Hi1 Hi2 Hmurng Hvbmul Hinv Hguard.
split.
+ (* wpolylvec_bmul_irng on row slice: each element is urng q and hence bmul_irng *)
  rewrite /wpolylvec_bmul_irng LArray.allP => l lb.
  have /= -> := mat_row_slice_unflatten _mat i{hr} l _ _; 1,2: smt().
  apply wpoly_urng_bmul_irng.
  move: Hmurng; rewrite /wpolymat_urng KLMatrix.allP => Hj.
  by apply (Hj (i{hr}*lvec + l) _); smt().
+ (* Post-call: establish invariant at i+1 *)
  move => _ aux Haux Hrng.
  do split; 1,2: smt().
  move => k kl ku.
  have /= Hwb :=
    kvec_unflatten256_writeback_iE out{hr} aux (256 * i{hr}) k _ _; 1,2: smt().
  split.
  + (* Lifts equality *)
    rewrite /lifts_wpolykvec mapiE; 1: smt(mldsa65_kvec).
    rewrite Hwb.
    case (k = i{hr}) => Hki.
    + subst k.
      have -> : 256 * i{hr} %/ 256 = i{hr} by smt().
      rewrite ifT // Haux.
      have -> : (Array1280.init (fun j => _mat.[5 * 256 * i{hr} + j])) =
                (Array1280.init (fun j => _mat.[1280 * i{hr} + j])).
      + by apply Array1280.tP => j jb; rewrite !Array1280.initiE 1,2:/# /= /#.
      congr.
      apply LArray.tP => l lb.
      rewrite /lifts_wpolylvec mapiE 1:/# /=.
      have /= -> := mat_row_slice_unflatten _mat i{hr} l _ _; 1,2: smt().
      rewrite /row LArray.initiE 1:/# /=.
      by rewrite /lifts_wpolymat mapiE 1:/#.
    + have -> : (k = 256 * i{hr} %/ 256) = false by smt().
      rewrite /=.
      have /= [Heq _] := Hinv k _; 1: smt().
      move: Heq; rewrite /lifts_wpolykvec mapiE 1:/# /=.
      by move => ->.
  + (* Range *)
    rewrite Hwb.
    case (k = i{hr}) => Hki.
    + subst k; have -> : 256 * i{hr} %/ 256 = i{hr} by smt().
      by rewrite ifT //.
    + have -> : (k = 256 * i{hr} %/ 256) = false by smt().
      by have /= [_ ?] := Hinv k _; smt().
qed.

lemma row_vector____multiply_with_matrix_A_ph
      (_mat : W32.t Array7680.t) (_vec : W32.t Array1280.t) :
    phoare [ M.row_vector____multiply_with_matrix_A :
        matrix_A = _mat /\ vector = _vec /\
        wpolymat_urng (mat_unflatten256 _mat) q /\
        wpolylvec_bmul_irng (lvec_unflatten256 _vec)
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          ntt_mulmxv (liftu_wpolymat (mat_unflatten256 _mat))
                     (lifts_wpolylvec (lvec_unflatten256 _vec)) /\
        wpolykvec_srng (kvec_unflatten256 res) (lvec * (q-1)) (lvec * (q-1))
    ] = 1%r
  by conseq row_vector____multiply_with_matrix_A_ll
            (row_vector____multiply_with_matrix_A_correct _mat _vec).
