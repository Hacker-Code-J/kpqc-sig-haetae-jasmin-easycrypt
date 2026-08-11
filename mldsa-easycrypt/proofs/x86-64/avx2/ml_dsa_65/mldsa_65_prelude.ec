require import AllCore List IntDiv RealExp StdBigop.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.

from JazzEC require import Array320 Array416 Array1280 Array640 Array1536 Array768 Array256 Array128 Array1920 Array3200 Array7680 Array2496.

import LArray KArray.

axiom mldsa65_lvec: lvec = 5.
axiom mldsa65_kvec: kvec = 6.
axiom mldsa65_w_hint : w_hint = 55.
axiom mldsa65_lambda : lambda = 192.
axiom mldsa65_gamma1 : gamma1 = 524288. (* 2**19 *)
axiom mldsa65_gamma2 : gamma2 = 261888. (* (q-1)/32 *)
axiom mldsa65_Eta : Eta = 4.
axiom mldsa65_tau : tau = 49.

op  lvec_unflatten640(a : 'a Array3200.t) =
     LArray.init (fun i => Array640.of_list witness (sub a (640*i) 640)).

op  lvec_unflatten256(a : 'a Array1280.t) =
     LArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).

op  lvec_unflatten128(a : 'a Array640.t) =
     LArray.init (fun i => Array128.of_list witness (sub a (128*i) 128)).

op  kvec_unflatten256(a : 'a Array1536.t) =
     KArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).

op  kvec_unflatten128(a : 'a Array768.t) =
     KArray.init (fun i => Array128.of_list witness (sub a (128*i) 128)).

op  kvec_unflatten320(a : 'a Array1920.t) =
     KArray.init (fun i => Array320.of_list witness (sub a (320*i) 320)).

op  kvec_unflatten416(a : 'a Array2496.t) =
     KArray.init (fun i => Array416.of_list witness (sub a (416*i) 416)).

lemma lvec_unflatten640iE (v : 'a Array3200.t) i :
   0 <= i < 3200 => v.[i] = (lvec_unflatten640 v).[i %/ 640].[i %% 640].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_lvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma lvec_unflatten256iE (v : 'a Array1280.t) i :
   0 <= i < 1280 => v.[i] = (lvec_unflatten256 v).[i %/ 256].[i %% 256].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_lvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma lvec_unflatten128iE (v : 'a Array640.t) i :
   0 <= i < 640 => v.[i] = (lvec_unflatten128 v).[i %/ 128].[i %% 128].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_lvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma kvec_unflatten256iE (v : 'a Array1536.t) i :
   0 <= i < 1536 => v.[i] = (kvec_unflatten256 v).[i %/ 256].[i %% 256].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_kvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma kvec_unflatten128iE (v : 'a Array768.t) i :
   0 <= i < 768 => v.[i] = (kvec_unflatten128 v).[i %/ 128].[i %% 128].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_kvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma kvec_unflatten320iE (v : 'a Array1920.t) i :
   0 <= i < 1920 => v.[i] = (kvec_unflatten320 v).[i %/ 320].[i %% 320].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_kvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma kvec_unflatten416iE (v : 'a Array2496.t) i :
   0 <= i < 2496 => v.[i] = (kvec_unflatten416 v).[i %/ 416].[i %% 416].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_kvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.



lemma kvec_unflatten256E i j (h : 'a Array1536.t) (P : 'a -> bool) :
   0 <= i < kvec =>
   0 <= j < 256 =>
        all (all P) (kvec_unflatten256 h) =>
        P h.[i*256+j].
have eq_kvec := mldsa65_kvec.
move => ??;rewrite allP => Hii. 
have := Hii i _;1:smt().
rewrite allP => Hjj. 
have := Hjj j _;1:smt().
by rewrite initiE 1:/# /= get_of_list 1:/# /= nth_sub /#. 
qed.

lemma kvec_unflatten256P i j (h1 : 'a Array1536.t) (h2 : ('b Array256.t) KArray.t) (F : 'a -> 'b) :
   0 <= i < kvec =>
   0 <= j < 256 =>
        map (map F) (kvec_unflatten256 h1) = h2 =>
        F h1.[i*256+j] = h2.[i].[j].
have eq_kvec := mldsa65_kvec.
move => ??; rewrite tP => Hii.
have := Hii i _; 1:smt().
rewrite tP => Hjj.
have := Hjj j _; 1:smt().
rewrite mapiE 1:/# /= mapiE 1:/# /= initiE 1:/# initiE 1:/# /=.
by rewrite  /= !nth_sub /#. 
qed.

op mat_unflatten256(a : 'a Array7680.t) =
     KLMatrix.init (fun i => Array256.of_list witness (sub a (256*i) 256)).

(* -------------------------------------------------------------------- *)
(* Slice / writeback helper lemmas                                        *)
(* -------------------------------------------------------------------- *)

(** [kvec_slice_eq]: the k-th component of kvec_unflatten256 equals the
    256-element window starting at base = 256*k of the flat array. *)
lemma kvec_slice_eq (v : 'a Array1536.t) (base : int) :
  base %% 256 = 0 => 0 <= base %/ 256 < kvec =>
  (kvec_unflatten256 v).[base %/ 256] =
  Array256.init (fun i => v.[base + i]).
proof.
move => Hmod Hk.
apply Array256.tP => j jb.
rewrite Array256.initiE 1:/# /=.
rewrite /kvec_unflatten256 KArray.initiE 1:/# /=.
by rewrite get_of_list 1:/# nth_sub 1:/# /#.
qed.

(** [init_writeback_slice_eq]: reading back the [base, base+256) window
    from a writeback Array1536.init gives the written Array256. *)
lemma init_writeback_slice_eq (arr : 'a Array1536.t) (f : 'a Array256.t) (base : int) :
  0 <= base => base + 256 <= 1536 =>
  Array256.init (fun i => (Array1536.init (fun i0 =>
    if base <= i0 < base + 256 then f.[i0 - base] else arr.[i0])).[base + i]) = f.
proof.
move => Hbase Hend.
apply Array256.tP => j jb.
rewrite Array256.initiE 1:/# /= Array1536.initiE 1:/# /=.
by smt().
qed.

(** [kvec_unflatten256_writeback_iE]: unflattening a writeback init gives
    the written array at component k = base/256, and the original elsewhere. *)
lemma kvec_unflatten256_writeback_iE (arr : 'a Array1536.t) (f : 'a Array256.t) (base k : int) :
  base %% 256 = 0 => 0 <= k < kvec =>
  (kvec_unflatten256 (Array1536.init (fun i =>
    if base <= i < base + 256 then f.[i - base] else arr.[i]))).[k] =
  if k = base %/ 256 then f else (kvec_unflatten256 arr).[k].
proof.
move => Hmod Hk.
have kvec_val := mldsa65_kvec.
apply Array256.tP => j jb.
rewrite /kvec_unflatten256 KArray.initiE 1:/# /=.
rewrite get_of_list 1:/# nth_sub 1:/# /=.
rewrite Array1536.initiE 1:/# /=.
case (k = base %/ 256) => Heq /=.
+ have -> : (base <= 256 * k + j && 256 * k + j < base + 256) = true by smt().
  by smt().
+ have -> : (base <= 256 * k + j && 256 * k + j < base + 256) = false by smt().
  by rewrite kvec_unflatten256iE 1:/# /#.
qed.

(* -------------------------------------------------------------------- *)
(* lvec (L=5) slice / writeback helpers — mirrors kvec versions above    *)
(* -------------------------------------------------------------------- *)

lemma lvec_slice_eq (v : 'a Array1280.t) (base : int) :
  base %% 256 = 0 => 0 <= base %/ 256 < lvec =>
  (lvec_unflatten256 v).[base %/ 256] =
  Array256.init (fun i => v.[base + i]).
proof.
move => Hmod Hk.
have lvec_val := mldsa65_lvec.
apply Array256.tP => j jb.
rewrite Array256.initiE 1:/# /=.
rewrite /lvec_unflatten256 LArray.initiE 1:/# /=.
by rewrite get_of_list 1:/# nth_sub 1:/# /#.
qed.

lemma lvec_unflatten256_writeback_iE (arr : 'a Array1280.t) (f : 'a Array256.t) (base k : int) :
  base %% 256 = 0 => 0 <= k < lvec =>
  (lvec_unflatten256 (Array1280.init (fun i =>
    if base <= i < base + 256 then f.[i - base] else arr.[i]))).[k] =
  if k = base %/ 256 then f else (lvec_unflatten256 arr).[k].
proof.
move => Hmod Hk.
have lvec_val := mldsa65_lvec.
apply Array256.tP => j jb.
rewrite /lvec_unflatten256 LArray.initiE 1:/# /=.
rewrite get_of_list 1:/# nth_sub 1:/# /=.
rewrite Array1280.initiE 1:/# /=.
case (k = base %/ 256) => Heq /=.
+ have -> : (base <= 256 * k + j && 256 * k + j < base + 256) = true by smt().
  by smt().
+ have -> : (base <= 256 * k + j && 256 * k + j < base + 256) = false by smt().
  by rewrite lvec_unflatten256iE 1:/# /#.
qed.

(* -------------------------------------------------------------------- *)
(* Matrix row slice: a 1280-wide row of a flat Array7680 matrix equals  *)
(* the corresponding row of mat_unflatten256 (stride lvec).              *)
(* -------------------------------------------------------------------- *)
lemma mat_row_slice_unflatten (m : 'a Array7680.t) (r k : int) :
  0 <= r < kvec => 0 <= k < lvec =>
  (lvec_unflatten256 (Array1280.init (fun j => m.[1280*r + j]))).[k] =
  (mat_unflatten256 m).[r*lvec + k].
proof.
have lvec_val := mldsa65_lvec.
have kvec_val := mldsa65_kvec.
move => Hr Hk.
apply Array256.tP => j jb.
rewrite /lvec_unflatten256 LArray.initiE 1:/# /=.
rewrite get_of_list 1:/# nth_sub 1:/# /= Array1280.initiE 1:/#.
rewrite /mat_unflatten256 KLMatrix.initiE 1:/# /=.
by rewrite get_of_list 1:/# nth_sub 1:/# /#.
qed.

