require import AllCore IntDiv List Ring StdOrder BitEncoding.

require import Array256.
require import GFq Rq NTT_Fq NTTFullSpec.

import Zq.

theory NTTRowProductSpec.

(* A dimension-parametric row-product boundary.  KeyGen mode 2 instantiates
   [cols] with 3 and Verify mode 2 with 4.  The stored matrix remains in the
   spectral domain; its coefficient-domain view is defined independently by
   the inverse transform. *)

op poly_sum (count : int) (polys : int -> Rq.poly) : Rq.poly =
  Array256.init (fun i =>
    Rq.BigDom.BAdd.bigi predT (fun k => (polys k).[i]) 0 count).

op coefficient_row_product
    (cols : int)
    (matrix : int -> int -> Rq.poly)
    (vector : int -> Rq.poly)
    (row : int) : Rq.poly =
  Array256.init (fun i =>
    Rq.BigDom.BAdd.bigi predT
      (fun col => (Rq.(&*) (matrix row col) (vector col)).[i])
      0 cols).

op montgomery_pointwise_product
    (ahat p : Rq.poly) : Rq.poly =
  Array256.init (fun j =>
    ahat.[j] * (NTTFullSpec.full_ntt p).[j] * inv NTT_Fq.R).

op pointwise_row_hat
    (cols : int)
    (matrix_hat : int -> int -> Rq.poly)
    (vector_hat : int -> Rq.poly)
    (row : int) : Rq.poly =
  Array256.init (fun j =>
    Rq.BigDom.BAdd.bigi predT
      (fun col =>
        (matrix_hat row col).[j] *
        (vector_hat col).[j] * inv NTT_Fq.R)
      0 cols).

op pointwise_row
    (cols : int)
    (matrix_hat : int -> int -> Rq.poly)
    (vector : int -> Rq.poly)
    (row : int) : Rq.poly =
  pointwise_row_hat cols matrix_hat
    (fun col => NTTFullSpec.full_ntt (vector col)) row.

op inverse_row (spectral_row : Rq.poly) : Rq.poly =
  NTT_Fq.array256_mont (NTTFullSpec.full_invntt spectral_row).

op matrix_inverse_repr
    (rows cols : int)
    (matrix_hat matrix : int -> int -> Rq.poly) : bool =
  forall row col,
    0 <= row < rows => 0 <= col < cols =>
    matrix row col = NTTFullSpec.full_invntt (matrix_hat row col).

op vector_forward_repr
    (cols : int)
    (vector_hat vector : int -> Rq.poly) : bool =
  forall col,
    0 <= col < cols =>
    vector_hat col = NTTFullSpec.full_ntt (vector col).

op pointwise_row_repr
    (cols : int)
    (acc : Rq.poly)
    (matrix_hat : int -> int -> Rq.poly)
    (vector_hat : int -> Rq.poly)
    (row : int) : bool =
  acc = pointwise_row_hat cols matrix_hat vector_hat row.

op inverse_row_repr (out acc : Rq.poly) : bool =
  out = inverse_row acc.

(* Freezing is a word-representation boundary, not part of the field-level
   convolution theorem.  This predicate states only coefficient preservation;
   an actual freeze implementation must establish it independently. *)
op freeze_repr (before after : BArray1024.t) : bool =
  forall i,
    i \in range 0 256 =>
    NTT_Fq.word_to_coeff (BArray1024.get32 after i) =
    NTT_Fq.word_to_coeff (BArray1024.get32 before i).

lemma coefficient_row_product_get cols matrix vector row i :
  0 <= i < 256 =>
  (coefficient_row_product cols matrix vector row).[i] =
    Rq.BigDom.BAdd.bigi predT
      (fun col => (Rq.(&*) (matrix row col) (vector col)).[i])
      0 cols.
proof.
move=> hi.
by rewrite /coefficient_row_product Array256.initiE.
qed.

lemma poly_sum_get count polys i :
  0 <= i < 256 =>
  (poly_sum count polys).[i] =
    Rq.BigDom.BAdd.bigi predT (fun k => (polys k).[i]) 0 count.
proof.
move=> hi.
by rewrite /poly_sum Array256.initiE.
qed.

lemma coefficient_row_product_as_poly_sum cols matrix vector row :
  coefficient_row_product cols matrix vector row =
    poly_sum cols (fun col => Rq.(&*) (matrix row col) (vector col)).
proof. by rewrite /coefficient_row_product /poly_sum. qed.

lemma montgomery_pointwise_product_get ahat p j :
  0 <= j < 256 =>
  (montgomery_pointwise_product ahat p).[j] =
    ahat.[j] * (NTTFullSpec.full_ntt p).[j] * inv NTT_Fq.R.
proof.
move=> hj.
by rewrite /montgomery_pointwise_product Array256.initiE.
qed.

lemma pointwise_row_get cols matrix_hat vector row j :
  0 <= j < 256 =>
  (pointwise_row cols matrix_hat vector row).[j] =
    Rq.BigDom.BAdd.bigi predT
      (fun col =>
        (matrix_hat row col).[j] *
        (NTTFullSpec.full_ntt (vector col)).[j] * inv NTT_Fq.R)
      0 cols.
proof.
move=> hj.
by rewrite /pointwise_row /pointwise_row_hat Array256.initiE.
qed.

lemma pointwise_row_hat_get cols matrix_hat vector_hat row j :
  0 <= j < 256 =>
  (pointwise_row_hat cols matrix_hat vector_hat row).[j] =
    Rq.BigDom.BAdd.bigi predT
      (fun col =>
        (matrix_hat row col).[j] *
        (vector_hat col).[j] * inv NTT_Fq.R)
      0 cols.
proof.
move=> hj.
by rewrite /pointwise_row_hat Array256.initiE.
qed.

lemma pointwise_row_as_poly_sum cols matrix_hat vector row :
  pointwise_row cols matrix_hat vector row =
    poly_sum cols (fun col =>
      montgomery_pointwise_product (matrix_hat row col) (vector col)).
proof.
apply Array256.ext_eq => j hj.
rewrite pointwise_row_get 1:hj poly_sum_get 1:hj.
apply Rq.BigDom.BAdd.eq_big_int => col hcol /=.
by rewrite montgomery_pointwise_product_get.
qed.

lemma matrix_inverse_reprE rows cols matrix_hat matrix row col :
  matrix_inverse_repr rows cols matrix_hat matrix =>
  0 <= row < rows => 0 <= col < cols =>
  matrix row col = NTTFullSpec.full_invntt (matrix_hat row col).
proof. by rewrite /matrix_inverse_repr; move=> h; apply h. qed.

lemma vector_forward_reprE cols vector_hat vector col :
  vector_forward_repr cols vector_hat vector =>
  0 <= col < cols =>
  vector_hat col = NTTFullSpec.full_ntt (vector col).
proof. by rewrite /vector_forward_repr; move=> h; apply h. qed.

lemma matrix_inverse_repr_full_invntt rows cols matrix_hat :
  matrix_inverse_repr rows cols matrix_hat
    (fun row col => NTTFullSpec.full_invntt (matrix_hat row col)).
proof. by rewrite /matrix_inverse_repr. qed.

lemma vector_forward_repr_full_ntt cols vector :
  vector_forward_repr cols
    (fun col => NTTFullSpec.full_ntt (vector col)) vector.
proof. by rewrite /vector_forward_repr. qed.

lemma pointwise_row_repr_exact cols matrix_hat vector row :
  pointwise_row_repr cols
    (pointwise_row_hat cols matrix_hat vector row)
    matrix_hat vector row.
proof. by rewrite /pointwise_row_repr. qed.

lemma pointwise_row_from_forward_repr cols matrix_hat vector_hat vector row :
  vector_forward_repr cols vector_hat vector =>
  pointwise_row_hat cols matrix_hat vector_hat row =
    pointwise_row cols matrix_hat vector row.
proof.
move=> hforward.
apply Array256.ext_eq => j hj.
rewrite pointwise_row_hat_get 1:hj pointwise_row_get 1:hj.
apply Rq.BigDom.BAdd.eq_big_int => col hcol /=.
by rewrite (vector_forward_reprE cols vector_hat vector col hforward hcol).
qed.

lemma inverse_row_repr_exact acc :
  inverse_row_repr (inverse_row acc) acc.
proof. by rewrite /inverse_row_repr. qed.

lemma freeze_repr_preserves_poly before after p :
  freeze_repr before after =>
  NTT_Fq.poly_repr before p =>
  NTT_Fq.poly_repr after p.
proof.
move=> hfreeze hbefore.
have harrays :
    NTT_Fq.barray256_to_poly after =
    NTT_Fq.barray256_to_poly before.
+ apply Array256.ext_eq => i hi.
  have himem : i \in range 0 256 by rewrite mem_range.
  have hafter := NTT_Fq.barray256_to_polyE after i himem.
  have hbefore' := NTT_Fq.barray256_to_polyE before i himem.
  have hfreeze' := hfreeze i himem.
  smt().
move: hbefore; rewrite /NTT_Fq.poly_repr => hbefore.
rewrite /NTT_Fq.poly_repr.
by rewrite harrays hbefore.
qed.

end NTTRowProductSpec.
