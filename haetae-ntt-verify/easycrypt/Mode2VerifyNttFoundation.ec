require import AllCore.

require import Array256.
require import GFq Rq NTT_Fq NTTFullSpec NTTRowProductSpec NTTFullSpectralAction.

import Zq.

theory Mode2VerifyNttFoundation.

op mode2_verify_rows : int = 2.
op mode2_verify_cols : int = 4.

op verify_mode2_row_product
    (matrix : int -> int -> Rq.poly)
    (vector : int -> Rq.poly)
    (row : int) : Rq.poly =
  NTTRowProductSpec.coefficient_row_product
    mode2_verify_cols matrix vector row.

op verify_mode2_pointwise_row
    (matrix_hat : int -> int -> Rq.poly)
    (vector : int -> Rq.poly)
    (row : int) : Rq.poly =
  NTTRowProductSpec.pointwise_row
    mode2_verify_cols matrix_hat vector row.

op verify_mode2_pointwise_row_hat
    (matrix_hat : int -> int -> Rq.poly)
    (vector_hat : int -> Rq.poly)
    (row : int) : Rq.poly =
  Array256.init (fun j =>
    Rq.BigDom.BAdd.bigi predT
      (fun col =>
        (matrix_hat row col).[j] *
        (vector_hat col).[j] * inv NTT_Fq.R)
      0 mode2_verify_cols).

op verify_mode2_matrix_inverse_repr
    (matrix_hat matrix : int -> int -> Rq.poly) : bool =
  NTTRowProductSpec.matrix_inverse_repr
    mode2_verify_rows mode2_verify_cols matrix_hat matrix.

op verify_mode2_vector_forward_repr
    (vector_hat vector : int -> Rq.poly) : bool =
  NTTRowProductSpec.vector_forward_repr
    mode2_verify_cols vector_hat vector.

op verify_mode2_pointwise_repr
    (acc : Rq.poly)
    (matrix_hat : int -> int -> Rq.poly)
    (vector_hat : int -> Rq.poly)
    (row : int) : bool =
  acc = verify_mode2_pointwise_row_hat matrix_hat vector_hat row.

op verify_mode2_inverse_repr (out acc : Rq.poly) : bool =
  NTTRowProductSpec.inverse_row_repr out acc.

lemma verify_mode2_matrix_inverse_reprE matrix_hat matrix row col :
  verify_mode2_matrix_inverse_repr matrix_hat matrix =>
  0 <= row < mode2_verify_rows =>
  0 <= col < mode2_verify_cols =>
  matrix row col = NTTFullSpec.full_invntt (matrix_hat row col).
proof.
move=> hrepr hrow hcol.
exact (NTTRowProductSpec.matrix_inverse_reprE
  mode2_verify_rows mode2_verify_cols matrix_hat matrix row col
  hrepr hrow hcol).
qed.

lemma verify_mode2_vector_forward_reprE vector_hat vector col :
  verify_mode2_vector_forward_repr vector_hat vector =>
  0 <= col < mode2_verify_cols =>
  vector_hat col = NTTFullSpec.full_ntt (vector col).
proof.
move=> hrepr hcol.
exact (NTTRowProductSpec.vector_forward_reprE
  mode2_verify_cols vector_hat vector col hrepr hcol).
qed.

lemma verify_mode2_pointwise_row_hat_get matrix_hat vector_hat row j :
  0 <= j < 256 =>
  (verify_mode2_pointwise_row_hat matrix_hat vector_hat row).[j] =
    Rq.BigDom.BAdd.bigi predT
      (fun col =>
        (matrix_hat row col).[j] *
        (vector_hat col).[j] * inv NTT_Fq.R)
      0 mode2_verify_cols.
proof.
move=> hj.
by rewrite /verify_mode2_pointwise_row_hat Array256.initiE.
qed.

lemma verify_mode2_pointwise_row_hat_from_forward_repr
    matrix_hat vector_hat vector row :
  verify_mode2_vector_forward_repr vector_hat vector =>
  verify_mode2_pointwise_row_hat matrix_hat vector_hat row =
  verify_mode2_pointwise_row matrix_hat vector row.
proof.
move=> hforward.
apply Array256.ext_eq => j hj.
rewrite verify_mode2_pointwise_row_hat_get 1:hj.
rewrite /verify_mode2_pointwise_row.
rewrite NTTRowProductSpec.pointwise_row_get 1:hj.
apply Rq.BigDom.BAdd.eq_big_int => col hcol /=.
by rewrite (verify_mode2_vector_forward_reprE vector_hat vector col).
qed.

lemma verify_mode2_pointwise_repr_exact matrix_hat vector_hat row :
  verify_mode2_pointwise_repr
    (verify_mode2_pointwise_row_hat matrix_hat vector_hat row)
    matrix_hat vector_hat row.
proof. by rewrite /verify_mode2_pointwise_repr. qed.

lemma verify_mode2_inverse_repr_exact acc :
  verify_mode2_inverse_repr (NTTRowProductSpec.inverse_row acc) acc.
proof. by rewrite /verify_mode2_inverse_repr /NTTRowProductSpec.inverse_row_repr. qed.

lemma verify_mode2_vector_forward_repr_full_ntt vector :
  verify_mode2_vector_forward_repr
    (fun col => NTTFullSpec.full_ntt (vector col)) vector.
proof.
exact (NTTRowProductSpec.vector_forward_repr_full_ntt
  mode2_verify_cols vector).
qed.

lemma verify_mode2_matrix_inverse_repr_full_invntt matrix_hat :
  verify_mode2_matrix_inverse_repr matrix_hat
    (fun row col => NTTFullSpec.full_invntt (matrix_hat row col)).
proof.
exact (NTTRowProductSpec.matrix_inverse_repr_full_invntt
  mode2_verify_rows mode2_verify_cols matrix_hat).
qed.

lemma verify_mode2_row_product_direct matrix_hat vector row :
  NTTRowProductSpec.inverse_row
    (verify_mode2_pointwise_row matrix_hat vector row) =
  verify_mode2_row_product
    (fun r col => NTTFullSpec.full_invntt (matrix_hat r col))
    vector row.
proof.
exact (NTTFullSpectralAction.full_ntt_montgomery_row_product
  mode2_verify_cols matrix_hat vector row).
qed.

lemma verify_mode2_row_product_from_component_reprs
    matrix_hat matrix vector_hat vector acc out row :
  0 <= row < mode2_verify_rows =>
  verify_mode2_matrix_inverse_repr matrix_hat matrix =>
  verify_mode2_vector_forward_repr vector_hat vector =>
  verify_mode2_pointwise_repr acc matrix_hat vector_hat row =>
  verify_mode2_inverse_repr out acc =>
  out = verify_mode2_row_product matrix vector row.
proof.
move=> hrow hmatrix hforward hpoint hinv.
rewrite /verify_mode2_inverse_repr /NTTRowProductSpec.inverse_row_repr in hinv.
rewrite /verify_mode2_pointwise_repr in hpoint.
rewrite hinv hpoint.
rewrite (verify_mode2_pointwise_row_hat_from_forward_repr
  matrix_hat vector_hat vector row hforward).
rewrite (verify_mode2_row_product_direct matrix_hat vector row).
apply Array256.ext_eq => i hi.
rewrite /verify_mode2_row_product.
rewrite !NTTRowProductSpec.coefficient_row_product_get 1,2:hi.
apply Rq.BigDom.BAdd.eq_big_int => col hcol /=.
have hcell := verify_mode2_matrix_inverse_reprE
  matrix_hat matrix row col hmatrix hrow hcol.
by rewrite hcell.
qed.

end Mode2VerifyNttFoundation.
