require import AllCore.

require import Rq NTTFullSpec NTTRowProductSpec NTTFullSpectralAction.

theory NTTMode2RowSpecializations.

op keygen_mode2_cols : int = 3.
op verify_mode2_rows : int = 2.
op verify_mode2_cols : int = 4.

lemma keygen_mode2_row_product_direct matrix_hat vector row :
  NTTRowProductSpec.inverse_row
    (NTTRowProductSpec.pointwise_row
      keygen_mode2_cols matrix_hat vector row) =
  NTTRowProductSpec.coefficient_row_product
    keygen_mode2_cols
    (fun r col => NTTFullSpec.full_invntt (matrix_hat r col))
    vector row.
proof.
exact (NTTFullSpectralAction.full_ntt_montgomery_row_product
  keygen_mode2_cols matrix_hat vector row).
qed.

lemma keygen_mode2_row_product_from_reprs
    matrix_hat matrix vector_hat vector acc out row :
  NTTRowProductSpec.matrix_inverse_repr
    2 keygen_mode2_cols matrix_hat matrix =>
  NTTRowProductSpec.vector_forward_repr
    keygen_mode2_cols vector_hat vector =>
  NTTRowProductSpec.pointwise_row_repr
    keygen_mode2_cols acc matrix_hat vector_hat row =>
  NTTRowProductSpec.inverse_row_repr out acc =>
  0 <= row < 2 =>
  out = NTTRowProductSpec.coefficient_row_product
    keygen_mode2_cols matrix vector row.
proof.
move=> hmatrix hforward hpointwise hinverse hrow.
exact (NTTFullSpectralAction.full_ntt_montgomery_row_product_from_reprs
  2 keygen_mode2_cols matrix_hat matrix vector_hat vector acc out row
  hrow hmatrix hforward hpointwise hinverse).
qed.

lemma verify_mode2_row_product_direct matrix_hat vector row :
  NTTRowProductSpec.inverse_row
    (NTTRowProductSpec.pointwise_row
      verify_mode2_cols matrix_hat vector row) =
  NTTRowProductSpec.coefficient_row_product
    verify_mode2_cols
    (fun r col => NTTFullSpec.full_invntt (matrix_hat r col))
    vector row.
proof.
exact (NTTFullSpectralAction.full_ntt_montgomery_row_product
  verify_mode2_cols matrix_hat vector row).
qed.

lemma verify_mode2_row_product_from_reprs
    matrix_hat matrix vector_hat vector acc out row :
  NTTRowProductSpec.matrix_inverse_repr
    verify_mode2_rows verify_mode2_cols matrix_hat matrix =>
  NTTRowProductSpec.vector_forward_repr
    verify_mode2_cols vector_hat vector =>
  NTTRowProductSpec.pointwise_row_repr
    verify_mode2_cols acc matrix_hat vector_hat row =>
  NTTRowProductSpec.inverse_row_repr out acc =>
  0 <= row < verify_mode2_rows =>
  out = NTTRowProductSpec.coefficient_row_product
    verify_mode2_cols matrix vector row.
proof.
move=> hmatrix hforward hpointwise hinverse hrow.
exact (NTTFullSpectralAction.full_ntt_montgomery_row_product_from_reprs
  verify_mode2_rows verify_mode2_cols
  matrix_hat matrix vector_hat vector acc out row
  hrow hmatrix hforward hpointwise hinverse).
qed.

end NTTMode2RowSpecializations.
