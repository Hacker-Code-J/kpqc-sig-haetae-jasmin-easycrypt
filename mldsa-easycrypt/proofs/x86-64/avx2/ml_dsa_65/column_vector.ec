require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Common_modular
                           Common_invert_ntt Common_ntt Common_rounding Rounding.

require import Polynomial.

from Spec require import GFq Rq Parameters MLDSA_W32_Rep VecMat.

import Round ZModQ Zq PolyKVec.

require import Array256 Array1536.

lemma lifts_wpolykvec_slice (v : W32.t Array1536.t) (base : int) :
  base %% 256 = 0 => 0 <= base %/ 256 < kvec =>
  lifts_wpoly (Array256.init (fun i => v.[base + i])) =
  (lifts_wpolykvec (kvec_unflatten256 v)).[base %/ 256].
proof.
move => Hmod Hk.
rewrite /lifts_wpolykvec mapiE 1:/# /=.
by rewrite -kvec_slice_eq.
qed.

(* ================================================================== *)
(* Column vector operations: loops over polynomial-level operations.   *)
(* All operate on Array1536 (6 * 256 = kvec * n coefficients).        *)
(* Spec connections use kvec_unflatten256 to get polykvec view.        *)
(* ================================================================== *)

(* ================================================================== *)
(* column_vector__reduce32                                              *)
(* Reduces each of 6 polynomials modulo q to centered representative.  *)
(* Calls polynomial__reduce32 in a 6-iteration loop.                   *)
(* ================================================================== *)

lemma column_vector__reduce32_ll : islossless M.column_vector__reduce32.
proof.
proc.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *.
wp; call polynomial__reduce32_ll.
by auto => /#.
qed.

lemma column_vector__reduce32_correct (_v : W32.t Array1536.t) :
    hoare [ M.column_vector__reduce32 :
        vector = _v
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          lifts_wpolykvec (kvec_unflatten256 _v) /\
        wpolykvec_srng (kvec_unflatten256 res) ((q-1) %/ 2) ((q-1) %/ 2)
    ].
proof.
have kvec_val := mldsa65_kvec.
proc.
while (0 <= i <= 6 /\
       (forall k, 0 <= k < i =>
         lifts_wpoly (kvec_unflatten256 vector).[k] =
           lifts_wpoly (kvec_unflatten256 _v).[k] /\
         wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2) (kvec_unflatten256 vector).[k]) /\
       (forall k, i <= k < 6 =>
         (kvec_unflatten256 vector).[k] = (kvec_unflatten256 _v).[k])
      ); last first.
+ (* Exit: combine per-component facts into vector-level properties *)
  auto => |>; split; 1: smt().
  move => i0 v0 Hng Hi1 Hi2 Hdone Huntouched; split.
  + apply KArray.tP => k kb.
    rewrite /lifts_wpolykvec mapiE; 1: smt(mldsa65_kvec).
    rewrite mapiE; 1: smt(mldsa65_kvec).
    by have /= [-> _] := Hdone k _; smt().
  + by rewrite /wpolykvec_srng allP => k kb; have [_ ?] := Hdone k _; smt().
wp; ecall (polynomial__reduce32_correct
             (Array256.init (fun j => vector.[(i * 256) + j]))).
auto => /> &hr Hi1 Hi2 Hprocessed Huntouched Hguard result Hlifts Hrng; do split; 1,2: smt().
+ (* Processed components: k < i + 1 *)
  move => k ? Hk.
  have /= Hwb := kvec_unflatten256_writeback_iE vector{hr} result (i{hr} * 256) k _ _;
    1,2: smt().
  case (k = i{hr}) => Hki.
  + (* New component k = i *)
    subst k; rewrite Hwb ifT; 1: smt().
    split; last exact Hrng.
    rewrite Hlifts; congr.
    have /= <- := Huntouched i{hr} _; 1: smt().
    by rewrite -kvec_slice_eq; smt().
  + (* Old component k < i *)
    rewrite Hwb ifF; 1: smt().
    by have := Hprocessed k _; smt().
+ (* Untouched components: k >= i + 1 *)
  move => k ? Hk.
  have /= Hwb := kvec_unflatten256_writeback_iE vector{hr} result (i{hr} * 256) k _ _;
    1,2: smt().
  rewrite Hwb ifF; 1: smt().
  by have := Huntouched k _; smt().
qed.

lemma column_vector__reduce32_ph (_v : W32.t Array1536.t) :
    phoare [ M.column_vector__reduce32 :
        vector = _v
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          lifts_wpolykvec (kvec_unflatten256 _v) /\
        wpolykvec_srng (kvec_unflatten256 res) ((q-1) %/ 2) ((q-1) %/ 2)
    ] = 1%r
  by conseq column_vector__reduce32_ll (column_vector__reduce32_correct _v).

(* ================================================================== *)
(* column_vector__ntt                                                   *)
(* Applies NTT to each of 6 polynomials.                               *)
(* Calls polynomial__ntt in a 6-iteration loop.                        *)
(* Spec: nttv from VecMat.ec                                           *)
(* ================================================================== *)

lemma column_vector__ntt_ll : islossless M.column_vector__ntt.
proof.
proc.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *.
wp; call polynomial__ntt_ll.
by auto => /#.
qed.

lemma column_vector__ntt_correct (_v : W32.t Array1536.t) :
    hoare [ M.column_vector__ntt :
        vector = _v /\
        wpolykvec_ntt_irng (kvec_unflatten256 _v)
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          nttv (lifts_wpolykvec (kvec_unflatten256 _v)) /\
        wpolykvec_ntt_orng (kvec_unflatten256 res)
    ].
proof.
have kvec_val := mldsa65_kvec.
proc.
while (0 <= i <= 6 /\
       wpolykvec_ntt_irng (kvec_unflatten256 _v) /\
       (forall k, 0 <= k < i =>
         lifts_wpoly (kvec_unflatten256 vector).[k] =
           ntt (lifts_wpoly (kvec_unflatten256 _v).[k]) /\
         wpoly_ntt_orng (kvec_unflatten256 vector).[k]) /\
       (forall k, i <= k < 6 =>
         (kvec_unflatten256 vector).[k] = (kvec_unflatten256 _v).[k])
      ); last first.
+ auto => |> Hrng_pre; split; 1: smt().
  move => i0 v0 Hng Hi1 Hi2 Hdone Huntouched; split.
  + apply KArray.tP => k kb.
    rewrite /lifts_wpolykvec mapiE; 1: smt(mldsa65_kvec).
    rewrite /nttv mapiE; 1: smt(mldsa65_kvec).
    rewrite mapiE; 1: smt(mldsa65_kvec).
    by have /= [-> _] := Hdone k _; smt().
  + by rewrite /wpolykvec_ntt_orng allP => k kb; have [_ ?] := Hdone k _; smt().
wp; ecall (polynomial__ntt_correct
             (Array256.init (fun j => vector.[i * 256 + j]))).
auto => /> &hr Hi1 Hi2 Hrng_pre Hprocessed Huntouched Hguard; split.
+ rewrite -kvec_slice_eq; 1,2: smt().
  have -> : i{hr} * n %/ n = i{hr} by smt().
  rewrite (Huntouched i{hr} _); 1: smt().
  by move: Hrng_pre; rewrite /wpolykvec_ntt_irng KArray.allP => H; apply H; smt().
+ move => _ result Hlifts Hrng; do split; 1,2: smt().
  + move => k ? Hk.
    have /= Hwb := kvec_unflatten256_writeback_iE vector{hr} result (i{hr} * 256) k _ _;
      1,2: smt().
    case (k = i{hr}) => Hki.
    + subst k; rewrite Hwb ifT; 1: smt().
      split; last exact Hrng.
      rewrite Hlifts; congr.
      have /= <- := Huntouched i{hr} _; 1: smt().
      by rewrite -kvec_slice_eq; smt().
    + rewrite Hwb ifF; 1: smt().
      by have := Hprocessed k _; smt().
  + move => k ? Hk.
    have /= Hwb := kvec_unflatten256_writeback_iE vector{hr} result (i{hr} * 256) k _ _;
      1,2: smt().
    rewrite Hwb ifF; 1: smt().
    by have := Huntouched k _; smt().
qed.

lemma column_vector__ntt_ph (_v : W32.t Array1536.t) :
    phoare [ M.column_vector__ntt :
        vector = _v /\
        wpolykvec_ntt_irng (kvec_unflatten256 _v)
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          nttv (lifts_wpolykvec (kvec_unflatten256 _v)) /\
        wpolykvec_ntt_orng (kvec_unflatten256 res)
    ] = 1%r
  by conseq column_vector__ntt_ll (column_vector__ntt_correct _v).

(* ================================================================== *)
(* column_vector__invert_ntt_montgomery                                 *)
(* Applies inverse NTT (with Montgomery) to each of 6 polynomials.     *)
(* Calls polynomial__invert_ntt_montgomery in a 6-iteration loop.      *)
(* Spec: invnttv from VecMat.ec                                        *)
(* ================================================================== *)

lemma column_vector__invert_ntt_montgomery_ll :
    islossless M.column_vector__invert_ntt_montgomery.
proof.
proc.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *.
wp; call polynomial__invert_ntt_montgomery_ll.
by auto => /#.
qed.

lemma column_vector__invert_ntt_montgomery_correct (_v : W32.t Array1536.t) :
    hoare [ M.column_vector__invert_ntt_montgomery :
        vector = _v /\
        wpolykvec_intt_irng (kvec_unflatten256 _v)
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          invnttv (lifts_wpolykvec (kvec_unflatten256 _v)) /\
        wpolykvec_srng (kvec_unflatten256 res) invntt_obound invntt_obound
    ].
proof.
have kvec_val := mldsa65_kvec.
proc.
while (0 <= i <= 6 /\
       wpolykvec_intt_irng (kvec_unflatten256 _v) /\
       (forall k, 0 <= k < i =>
         lifts_wpoly (kvec_unflatten256 vector).[k] =
           invntt (lifts_wpoly (kvec_unflatten256 _v).[k]) /\
         wpoly_srng invntt_obound invntt_obound (kvec_unflatten256 vector).[k]) /\
       (forall k, i <= k < 6 =>
         (kvec_unflatten256 vector).[k] = (kvec_unflatten256 _v).[k])
      ); last first.
+ auto => |> Hrng_pre; split; 1: smt().
  move => i0 v0 Hng Hi1 Hi2 Hdone Huntouched; split.
  + apply KArray.tP => k kb.
    rewrite /lifts_wpolykvec mapiE; 1: smt(mldsa65_kvec).
    rewrite /invnttv mapiE; 1: smt(mldsa65_kvec).
    rewrite mapiE; 1: smt(mldsa65_kvec).
    by have /= [-> _] := Hdone k _; smt().
  + by rewrite /wpolykvec_srng allP => k kb; have [_ ?] := Hdone k _; smt().
wp; ecall (polynomial__invert_ntt_montgomery_correct
             (Array256.init (fun j => vector.[i * 256 + j]))).
auto => /> &hr Hi1 Hi2 Hrng_pre Hprocessed Huntouched Hguard; split.
+ rewrite -kvec_slice_eq; 1,2: smt().
  have -> : i{hr} * n %/ n = i{hr} by smt().
  rewrite (Huntouched i{hr} _); 1: smt().
  by move: Hrng_pre; rewrite /wpolykvec_intt_irng KArray.allP => H; apply H; smt().
+ move => _ result Hlifts Hrng; do split; 1,2: smt().
  + move => k ? Hk.
    have /= Hwb := kvec_unflatten256_writeback_iE vector{hr} result (i{hr} * 256) k _ _;
      1,2: smt().
    case (k = i{hr}) => Hki.
    + subst k; rewrite Hwb ifT; 1: smt().
      split; last exact Hrng.
      rewrite Hlifts; congr.
      have /= <- := Huntouched i{hr} _; 1: smt().
      by rewrite -kvec_slice_eq; smt().
    + rewrite Hwb ifF; 1: smt().
      by have := Hprocessed k _; smt().
  + move => k ? Hk.
    have /= Hwb := kvec_unflatten256_writeback_iE vector{hr} result (i{hr} * 256) k _ _;
      1,2: smt().
    rewrite Hwb ifF; 1: smt().
    by have := Huntouched k _; smt().
qed.

lemma column_vector__invert_ntt_montgomery_ph (_v : W32.t Array1536.t) :
    phoare [ M.column_vector__invert_ntt_montgomery :
        vector = _v /\
        wpolykvec_intt_irng (kvec_unflatten256 _v)
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          invnttv (lifts_wpolykvec (kvec_unflatten256 _v)) /\
        wpolykvec_srng (kvec_unflatten256 res) invntt_obound invntt_obound
    ] = 1%r
  by conseq column_vector__invert_ntt_montgomery_ll
            (column_vector__invert_ntt_montgomery_correct _v).

(* ================================================================== *)
(* column_vector____add                                                 *)
(* Pointwise addition of two column vectors (6 polynomials each).      *)
(* Calls polynomial__add in a 6-iteration loop.                        *)
(* ================================================================== *)

lemma column_vector____add_ll : islossless M.column_vector____add.
proof.
proc.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *.
wp; call polynomial__add_ll.
by auto => /#.
qed.

lemma column_vector____add_correct
      (_lhs : W32.t Array1536.t) (_rhs : W32.t Array1536.t) (A B : int) :
    hoare [ M.column_vector____add :
        lhs = _lhs /\ rhs = _rhs /\
        wpolykvec_srng (kvec_unflatten256 _lhs) A A /\
        wpolykvec_srng (kvec_unflatten256 _rhs) B B /\
        A + B < 2^31
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          lifts_wpolykvec (kvec_unflatten256 _lhs) +
          lifts_wpolykvec (kvec_unflatten256 _rhs) /\
        wpolykvec_srng (kvec_unflatten256 res) (A + B) (A + B)
    ].
proof.
have kvec_val := mldsa65_kvec.
proc.
while (0 <= i <= 6 /\ lhs = _lhs /\ rhs = _rhs /\
       wpolykvec_srng (kvec_unflatten256 _lhs) A A /\
       wpolykvec_srng (kvec_unflatten256 _rhs) B B /\
       A + B < 2^31 /\
       (forall k, 0 <= k < i =>
         lifts_wpoly (kvec_unflatten256 sum).[k] =
           lifts_wpoly (kvec_unflatten256 _lhs).[k] &+
           lifts_wpoly (kvec_unflatten256 _rhs).[k] /\
         wpoly_srng (A + B) (A + B) (kvec_unflatten256 sum).[k])
      ); last first.
+ (* Exit: combine per-component &+ into vector-level + via polykvec_add_iE *)
  auto => /> Hsrng_lhs Hsrng_rhs HAB; split; 1: smt().
  move => i0 s0 Hng Hi1 Hi2 Hdone; split.
  + apply KArray.tP => k kb.
    rewrite /lifts_wpolykvec mapiE; 1: smt(mldsa65_kvec).
    have /= [-> _] := Hdone k _; 1: smt().
    rewrite polykvec_add_iE; 1: smt(mldsa65_kvec).
    congr.
    - by rewrite mapiE; smt(mldsa65_kvec).
    - by rewrite mapiE; smt(mldsa65_kvec).
  + by rewrite /wpolykvec_srng allP => k kb; have [_ ?] := Hdone k _; smt().
(* Loop body *)
wp; ecall (polynomial__add_correct
             (Array256.init (fun j => sum.[(256 * i) + j]))
             (Array256.init (fun j => lhs.[(256 * i) + j]))
             (Array256.init (fun j => rhs.[(256 * i) + j]))
             A B).
auto => /> &hr Hi1 Hi2 Hsrng_lhs Hsrng_rhs HAB Hprocessed Hguard.
split.
+ (* Precondition: lhs/rhs slice ranges *)
  split.
  - have /= <- := kvec_slice_eq _lhs (256 * i{hr}) _ _; 1,2: smt().
    by move: Hsrng_lhs; rewrite /wpolykvec_srng allP => H; apply H; smt().
  - have /= <- := kvec_slice_eq _rhs (256 * i{hr}) _ _; 1,2: smt().
    by move: Hsrng_rhs; rewrite /wpolykvec_srng allP => H; apply H; smt().
+ (* Postcondition: update invariant *)
  move => _ _ result Hlifts Hrng; do split; 1,2: smt().
  move => k ? Hk.
  have /= Hwb := kvec_unflatten256_writeback_iE sum{hr} result (256 * i{hr}) k _ _;
    1,2: smt().
  case (k = i{hr}) => Hki.
  + (* New component k = i *)
    subst k; rewrite Hwb ifT; 1: smt().
    split; last exact Hrng.
    rewrite Hlifts; congr.
    + by rewrite -kvec_slice_eq; smt().
    + by rewrite -kvec_slice_eq; smt().
  + (* Old component k < i *)
    rewrite Hwb ifF; 1: smt().
    by have := Hprocessed k _; smt().
qed.

lemma column_vector____add_ph
      (_lhs : W32.t Array1536.t) (_rhs : W32.t Array1536.t) (A B : int) :
    phoare [ M.column_vector____add :
        lhs = _lhs /\ rhs = _rhs /\
        wpolykvec_srng (kvec_unflatten256 _lhs) A A /\
        wpolykvec_srng (kvec_unflatten256 _rhs) B B /\
        A + B < 2^31
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          lifts_wpolykvec (kvec_unflatten256 _lhs) +
          lifts_wpolykvec (kvec_unflatten256 _rhs) /\
        wpolykvec_srng (kvec_unflatten256 res) (A + B) (A + B)
    ] = 1%r
  by conseq column_vector____add_ll (column_vector____add_correct _lhs _rhs A B).

(* ================================================================== *)
(* column_vector____conditionally_add_modulus                           *)
(* Converts centered to standard [0, q-1] representation.              *)
(* Calls polynomial__conditionally_add_modulus in a 6-iteration loop.  *)
(* ================================================================== *)

lemma column_vector____conditionally_add_modulus_ll :
    islossless M.column_vector____conditionally_add_modulus.
proof.
proc.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *.
wp; call polynomial__conditionally_add_modulus_ll.
by auto => /#.
qed.

lemma column_vector____conditionally_add_modulus_correct
      (_v : W32.t Array1536.t) :
    hoare [ M.column_vector____conditionally_add_modulus :
        vector = _v /\
        wpolykvec_srng (kvec_unflatten256 _v) (q-1) (q-1)
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          lifts_wpolykvec (kvec_unflatten256 _v) /\
        wpolykvec_urng (kvec_unflatten256 res) q
    ].
proof.
have kvec_val := mldsa65_kvec.
proc.
while (0 <= i <= 6 /\
       wpolykvec_srng (kvec_unflatten256 _v) (q-1) (q-1) /\
       (forall k, 0 <= k < i =>
         lifts_wpoly (kvec_unflatten256 vector).[k] =
           lifts_wpoly (kvec_unflatten256 _v).[k] /\
         wpoly_urng q (kvec_unflatten256 vector).[k]) /\
       (forall k, i <= k < 6 =>
         (kvec_unflatten256 vector).[k] = (kvec_unflatten256 _v).[k])
      ); last first.
+ (* Exit: combine per-component facts into vector-level properties *)
  auto => /> Hsrng; split; 1: smt().
  move => i0 v0 Hng Hi1 Hi2 Hdone Huntouched; split.
  + apply KArray.tP => k kb.
    rewrite /lifts_wpolykvec mapiE; 1: smt(mldsa65_kvec).
    rewrite mapiE; 1: smt(mldsa65_kvec).
    by have /= [-> _] := Hdone k _; smt().
  + by rewrite /wpolykvec_urng allP => k kb; have [_ ?] := Hdone k _; smt().
(* Loop body *)
wp; ecall (polynomial__conditionally_add_modulus_correct
             (Array256.init (fun j => vector.[(i * 256) + j]))).
auto => /> &hr Hi1 Hi2 Hsrng_v Hprocessed Huntouched Hguard.
split.
+ (* Poly precondition: wpoly_srng ((q-1)%/2) ((q-1)%/2) (slice) *)
  rewrite -kvec_slice_eq; 1,2: smt().
  rewrite (Huntouched (i{hr} * n %/ n)); 1: smt().
  by move: Hsrng_v; rewrite /wpolykvec_srng allP => H;
     have := H (i{hr} * n %/ n) _; smt(mldsa65_kvec).
move => _ result Hlifts Hurng; do split; 1,2: smt().
+ (* Processed components: k < i + 1 *)
  move => k ? Hk.
  have /= Hwb := kvec_unflatten256_writeback_iE vector{hr} result (i{hr} * 256) k _ _;
    1,2: smt().
  case (k = i{hr}) => Hki.
  + (* New component k = i *)
    subst k; rewrite Hwb ifT; 1: smt().
    split; last exact Hurng.
    rewrite Hlifts; congr.
    have /= <- := Huntouched i{hr} _; 1: smt().
    by rewrite -kvec_slice_eq; smt().
  + (* Old component k < i *)
    rewrite Hwb ifF; 1: smt().
    by have := Hprocessed k _; smt().
+ (* Untouched components: k >= i + 1 *)
  move => k ? Hk.
  have /= Hwb := kvec_unflatten256_writeback_iE vector{hr} result (i{hr} * 256) k _ _;
    1,2: smt().
  rewrite Hwb ifF; 1: smt().
  by have := Huntouched k _; smt().
qed.

lemma column_vector____conditionally_add_modulus_ph
      (_v : W32.t Array1536.t) :
    phoare [ M.column_vector____conditionally_add_modulus :
        vector = _v /\
        wpolykvec_srng (kvec_unflatten256 _v) (q-1) (q-1)
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          lifts_wpolykvec (kvec_unflatten256 _v) /\
        wpolykvec_urng (kvec_unflatten256 res) q
    ] = 1%r
  by conseq column_vector____conditionally_add_modulus_ll
            (column_vector____conditionally_add_modulus_correct _v).

(* ================================================================== *)
(* column_vector____decompose                                           *)
(* Decomposes each polynomial into (LowBits, HighBits).                *)
(* Calls polynomial__decompose in a 6-iteration loop.                  *)
(* Spec: polykvec_LowBits, polykvec_HighBits from VecMat.ec            *)
(* ================================================================== *)

lemma column_vector____decompose_ll : islossless M.column_vector____decompose.
proof.
proc.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *.
wp; call (: true ==> true).
+ proc; wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
           ((256 * 32) %/ 8 - offset); last by auto => /#.
  by move => *; auto => /#.
by auto => /#.
qed.

lemma column_vector____decompose_correct (_v : W32.t Array1536.t) :
    hoare [ M.column_vector____decompose :
        vector = _v /\
        wpolykvec_urng (kvec_unflatten256 _v) q
        ==>
        lifts_wpolykvec (kvec_unflatten256 res.`1) =
          polykvec_LowBits (liftu_wpolykvec (kvec_unflatten256 _v)) /\
        liftu_wpolykvec (kvec_unflatten256 res.`2) =
          polykvec_HighBits (liftu_wpolykvec (kvec_unflatten256 _v)) /\
        wpolykvec_srng (kvec_unflatten256 res.`1) (gamma2 - 1) gamma2 /\
        wpolykvec_urng (kvec_unflatten256 res.`2) ((q - 1) %/ (2 * gamma2))
    ].
proof.
have kvec_val := mldsa65_kvec.
proc.
while (0 <= i <= 6 /\ vector = _v /\
       wpolykvec_urng (kvec_unflatten256 _v) q /\
       (forall k, 0 <= k < i =>
          lifts_wpoly (kvec_unflatten256 low).[k] =
            poly_LowBits (liftu_wpoly (kvec_unflatten256 _v).[k]) /\
          liftu_wpoly (kvec_unflatten256 high).[k] =
            poly_HighBits (liftu_wpoly (kvec_unflatten256 _v).[k]) /\
          wpoly_srng (gamma2 - 1) gamma2 (kvec_unflatten256 low).[k] /\
          wpoly_urng ((q - 1) %/ (2 * gamma2)) (kvec_unflatten256 high).[k])
      ); last first.
+ (* Exit *)
  auto => |> Hurng; split; 1: smt().
  move => i0 h0 l0 Hng Hi1 Hi2 Hdone; do split.
  + (* lifts_wpolykvec low = polykvec_LowBits *)
    rewrite /polykvec_LowBits; apply KArray.tP => k kb.
    rewrite /lifts_wpolykvec /liftu_wpolykvec mapiE 1:/# /= mapiE 1:/# /= mapiE 1:/# /=.
    by have /= [-> _] := Hdone k _; smt(mldsa65_kvec).
  + (* liftu_wpolykvec high = polykvec_HighBits *)
    rewrite /polykvec_HighBits; apply KArray.tP => k kb.
    rewrite /liftu_wpolykvec mapiE 1:/# /= mapiE 1:/# /= mapiE 1:/# /=.
    by have /= [_ [-> _]] := Hdone k _; smt(mldsa65_kvec).
  + by rewrite /wpolykvec_srng allP => k kb;
       have /= [_ [_ [? _]]] := Hdone k _; smt(mldsa65_kvec).
  + by rewrite /wpolykvec_urng allP => k kb;
       have /= [_ [_ [_ ?]]] := Hdone k _; smt(mldsa65_kvec).
(* Loop body *)
wp; ecall (polynomial__decompose_correct
             (Array256.init (fun j => low.[i * 256 + j]))
             (Array256.init (fun j => high.[i * 256 + j]))
             (Array256.init (fun j => vector.[i * 256 + j]))).
auto => /> &hr Hi1 Hi2 Hurng Hdone Hguard; split.
+ (* Pre: wpoly_urng q (slice of _v) *)
  rewrite -kvec_slice_eq; 1,2: smt().
  have -> : i{hr} * n %/ n = i{hr} by smt().
  by move: Hurng; rewrite /wpolykvec_urng KArray.allP => H; apply H; smt().
+ (* Post: invariant at i+1 *)
  move => _ result H_low_eq H_low_rng H_high_eq H_high_rng; split; 1: smt().
  move => k ? Hk.
  have /= Hwb_low :=
    kvec_unflatten256_writeback_iE low{hr} result.`1 (i{hr} * 256) k _ _; 1,2: smt().
  have /= Hwb_high :=
    kvec_unflatten256_writeback_iE high{hr} result.`2 (i{hr} * 256) k _ _; 1,2: smt().
  rewrite Hwb_low Hwb_high.
  case (k = i{hr}) => Hki.
  + (* New component k = i *)
    subst k; rewrite ifT 1:/# ifT 1:/#.
    have /= Hkslice := kvec_slice_eq _v (i{hr} * 256) _ _; 1,2: smt().
    have Heq_slice : (kvec_unflatten256 _v).[i{hr}] = init (fun j => _v.[i{hr} * n + j]) by smt().
    do split.
    + rewrite Heq_slice; apply Array256.tP => j jb.
      rewrite /lifts_wpoly mapiE 1:/# /= /poly_LowBits initiE 1:/# /=.
      by rewrite (H_low_eq j _) 1:/# /#.
    + rewrite Heq_slice; apply Array256.tP => j jb.
      rewrite /liftu_wpoly mapiE 1:/# /= /poly_HighBits initiE 1:/# /=.
      by rewrite (H_high_eq j _) 1:/# /#.
    + exact H_low_rng.
    + exact H_high_rng.
  + (* Old component k < i *)
    rewrite ifF 1:/# ifF 1:/#.
    by have := Hdone k _; smt().
qed.

lemma column_vector____decompose_ph (_v : W32.t Array1536.t) :
    phoare [ M.column_vector____decompose :
        vector = _v /\
        wpolykvec_urng (kvec_unflatten256 _v) q
        ==>
        lifts_wpolykvec (kvec_unflatten256 res.`1) =
          polykvec_LowBits (liftu_wpolykvec (kvec_unflatten256 _v)) /\
        liftu_wpolykvec (kvec_unflatten256 res.`2) =
          polykvec_HighBits (liftu_wpolykvec (kvec_unflatten256 _v)) /\
        wpolykvec_srng (kvec_unflatten256 res.`1) (gamma2 - 1) gamma2 /\
        wpolykvec_urng (kvec_unflatten256 res.`2) ((q - 1) %/ (2 * gamma2))
    ] = 1%r
  by conseq column_vector____decompose_ll
            (column_vector____decompose_correct _v).

(* ================================================================== *)
(* column_vector____power2round                                         *)
(* Splits each polynomial into (t1, t0) via Power2Round.               *)
(* Calls polynomial____power2round in a 6-iteration loop.              *)
(* Spec: Power2Round from VecMat.ec                                    *)
(* ================================================================== *)

lemma column_vector____power2round_ll :
    islossless M.column_vector____power2round.
proof.
proc.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *.
wp; call (: true ==> true).
+ proc; wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
           ((256 * 32) %/ 8 - offset); last by auto => /#.
  by move => *; auto => /#.
by auto => /#.
qed.

lemma column_vector____power2round_correct (_v : W32.t Array1536.t) :
    hoare [ M.column_vector____power2round :
        vector = _v /\
        wpolykvec_urng (kvec_unflatten256 _v) q
        ==>
        (liftu_wpolykvec (kvec_unflatten256 res.`1),
         lifts_wpolykvec (kvec_unflatten256 res.`2)) =
          Power2Round (liftu_wpolykvec (kvec_unflatten256 _v)) /\
        wpolykvec_urng (kvec_unflatten256 res.`1) (2^(23-d)) /\
        wpolykvec_srng (kvec_unflatten256 res.`2) (2^(d-1) - 1) (2^(d-1))
    ].
proof.
have kvec_val := mldsa65_kvec.
proc.
while (0 <= i <= 6 /\ vector = _v /\
       wpolykvec_urng (kvec_unflatten256 _v) q /\
       (forall k, 0 <= k < i =>
          liftu_wpoly (kvec_unflatten256 t1).[k] =
            (poly_Power2Round (liftu_wpoly (kvec_unflatten256 _v).[k])).`1 /\
          lifts_wpoly (kvec_unflatten256 t0).[k] =
            (poly_Power2Round (liftu_wpoly (kvec_unflatten256 _v).[k])).`2 /\
          wpoly_urng (2^(23-d)) (kvec_unflatten256 t1).[k] /\
          wpoly_srng (2^(d-1) - 1) (2^(d-1)) (kvec_unflatten256 t0).[k])
      ); last first.
+ (* Exit *)
  auto => |> Hurng; split; 1: smt().
  move => i0 t00 t10 Hng Hi1 Hi2 Hdone.
  rewrite /Power2Round /=; do split.
  + (* t1 aggregate *)
    apply KArray.tP => k kb.
    rewrite /liftu_wpolykvec mapiE 1:/# mapiE 1:/# /= mapiE 1:/# /=.
    by have /= [-> _] := Hdone k _; smt(mldsa65_kvec).
  + (* t0 aggregate *)
    apply KArray.tP => k kb.
    rewrite /lifts_wpolykvec mapiE 1:/# mapiE 1:/# /= mapiE 1:/# /=.
    by have /= [_ [-> _]] := Hdone k _; smt(mldsa65_kvec).
  + by rewrite /wpolykvec_urng allP => k kb;
       have /= [_ [_ [? _]]] := Hdone k _; smt(mldsa65_kvec).
  + by rewrite /wpolykvec_srng allP => k kb;
       have /= [_ [_ [_ ?]]] := Hdone k _; smt(mldsa65_kvec).
(* Loop body *)
wp; ecall (polynomial____power2round_correct
             (Array256.init (fun j => t1.[i * 256 + j]))
             (Array256.init (fun j => t0.[i * 256 + j]))
             (Array256.init (fun j => vector.[i * 256 + j]))).
auto => /> &hr Hi1 Hi2 Hurng Hdone Hguard; split.
+ (* Pre: wpoly_urng q (slice of _v) *)
  rewrite -kvec_slice_eq; 1,2: smt().
  have -> : i{hr} * n %/ n = i{hr} by smt().
  by move: Hurng; rewrite /wpolykvec_urng KArray.allP => H; apply H; smt().
+ (* Post: invariant at i+1 *)
  move => _ result H_t1_eq H_t1_rng H_t0_eq H_t0_rng; split; 1: smt().
  move => k ? Hk.
  have /= Hwb1 :=
    kvec_unflatten256_writeback_iE t1{hr} result.`1 (i{hr} * 256) k _ _; 1,2: smt().
  have /= Hwb0 :=
    kvec_unflatten256_writeback_iE t0{hr} result.`2 (i{hr} * 256) k _ _; 1,2: smt().
  rewrite Hwb1 Hwb0.
  case (k = i{hr}) => Hki.
  + (* New component k = i *)
    subst k; rewrite ifT 1:/# ifT 1:/#.
    have /= Hkslice := kvec_slice_eq _v (i{hr} * 256) _ _; 1,2: smt().
    have Heq_slice : (kvec_unflatten256 _v).[i{hr}] = init (fun j => _v.[i{hr} * n + j]) by smt().
    do split.
    + rewrite Heq_slice; apply Array256.tP => j jb.
      rewrite /liftu_wpoly mapiE 1:/# /poly_Power2Round /= initiE 1:/# /=.
      by rewrite (H_t1_eq j _) 1:/# asintK /#.
    + rewrite Heq_slice; apply Array256.tP => j jb.
      rewrite /lifts_wpoly mapiE 1:/# /= /poly_Power2Round /= initiE 1:/# /=.
      by rewrite (H_t0_eq j _) 1:/# asintK /#.
    + exact H_t1_rng.
    + exact H_t0_rng.
  + (* Old component k < i *)
    rewrite ifF 1:/# ifF 1:/#.
    by have := Hdone k _; smt().
qed.

lemma column_vector____power2round_ph (_v : W32.t Array1536.t) :
    phoare [ M.column_vector____power2round :
        vector = _v /\
        wpolykvec_urng (kvec_unflatten256 _v) q
        ==>
        (liftu_wpolykvec (kvec_unflatten256 res.`1),
         lifts_wpolykvec (kvec_unflatten256 res.`2)) =
          Power2Round (liftu_wpolykvec (kvec_unflatten256 _v)) /\
        wpolykvec_urng (kvec_unflatten256 res.`1) (2^(23-d)) /\
        wpolykvec_srng (kvec_unflatten256 res.`2) (2^(d-1) - 1) (2^(d-1))
    ] = 1%r
  by conseq column_vector____power2round_ll
            (column_vector____power2round_correct _v).
