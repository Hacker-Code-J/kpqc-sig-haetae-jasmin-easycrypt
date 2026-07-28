require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import KeygenMode2ParentTarget
               KeygenMode2ParentSpec
               KeygenSamplerCallersSpec
               KeygenSeedXofSpec KeygenUniformXofLeafSpec
               KeygenEtaSamplerSpec Fq
               KeygenM23MatrixSpec KeygenM23ArithmeticSpec
               TargetKeygenMode2ParentComposition
               TargetKeygenM23Matrix
               TargetKeygenM23Arithmetic.

theory TargetKeygenM23ParentComposition.

module Parent = KeygenMode2ParentTarget.M.

lemma sampler_matrix_range_mode2_bound16 m :
  KeygenSamplerCallersSpec.uniform_matrix_range32768
    m KeygenSamplerCallersSpec.mode2_k_i
      KeygenSamplerCallersSpec.mode2_m_i =>
  KeygenM23ArithmeticSpec.matrix_active_bound16 m.
proof.
rewrite /KeygenSamplerCallersSpec.uniform_matrix_range32768
        /KeygenM23ArithmeticSpec.matrix_active_bound16.
move=> hrange row col j hrow hcol hj.
have hrow' :
    0 <= row < KeygenSamplerCallersSpec.mode2_k_i.
+ rewrite /KeygenSamplerCallersSpec.mode2_k_i
          /KeygenM23MatrixSpec.mode2_rows_i in hrow.
  exact hrow.
have hcol' :
    0 <= col < KeygenSamplerCallersSpec.mode2_m_i.
+ rewrite /KeygenSamplerCallersSpec.mode2_m_i
          /KeygenM23MatrixSpec.mode2_cols_i in hcol.
  exact hcol.
have hcell := hrange row col hrow' hcol'.
rewrite /KeygenUniformXofLeafSpec.bounded_prefix32768 in hcell.
have hj' :
    0 <= j < KeygenUniformXofLeafSpec.uniform_poly_words_i.
+ rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i
          /KeygenM23MatrixSpec.poly_words_i in hj.
  exact hj.
have hvalue := hcell j hj'.
rewrite /KeygenSamplerCallersSpec.matrix_base_i
        /KeygenSamplerCallersSpec.poly_stride_i
        /KeygenM23MatrixSpec.mode2_cols_i
        /KeygenM23MatrixSpec.poly_words_i
        /KeygenUniformXofLeafSpec.uniform_q_i /= in hvalue.
rewrite /Fq.bw32 W32.to_sintE /W32.smod /=.
have hu :=
  W32.to_uint_cmp
    (BArray32768.get32 m ((row * 3 + col) * 256 + j)).
smt().
qed.

lemma centered_wide_slice_bound16 s base :
  KeygenEtaSamplerSpec.centered_interval8192
    s 0 0 KeygenM23MatrixSpec.mode2_s1_words_i =>
  0 <= base /\
  base + KeygenM23MatrixSpec.poly_words_i <=
    KeygenM23MatrixSpec.mode2_s1_words_i =>
  KeygenM23ArithmeticSpec.wide_slice_bound s base 16.
proof.
rewrite /KeygenEtaSamplerSpec.centered_interval8192
        /KeygenM23ArithmeticSpec.wide_slice_bound.
move=> hcenter hbase j hj.
have hidx :
    0 <= base + j <
      KeygenM23MatrixSpec.mode2_s1_words_i by smt().
have hvalue := hcenter (base + j) hidx.
rewrite /Fq.bw32.
smt().
qed.

lemma sampler_eta_mode2_input_repr_bound16 s :
  KeygenSamplerCallersSpec.eta_vector_centered8192
    s KeygenSamplerCallersSpec.mode2_m_i =>
  KeygenM23ArithmeticSpec.mode2_input_repr_bound16 s
    (KeygenM23ArithmeticSpec.wide_poly s 0)
    (KeygenM23ArithmeticSpec.wide_poly
      s KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23ArithmeticSpec.wide_poly
      s (2 * KeygenM23MatrixSpec.poly_words_i)).
proof.
rewrite /KeygenSamplerCallersSpec.eta_vector_centered8192
        /KeygenSamplerCallersSpec.eta_vector_words_i
        /KeygenSamplerCallersSpec.mode2_m_i
        /KeygenEtaSamplerSpec.eta_poly_words_i
        /KeygenM23MatrixSpec.mode2_s1_words_i
        /KeygenM23MatrixSpec.mode2_cols_i /=.
move=> hcenter.
rewrite /KeygenM23ArithmeticSpec.mode2_input_repr_bound16.
split.
+ apply KeygenM23ArithmeticSpec.wide_slice_repr_bound_self.
  apply (centered_wide_slice_bound16 s 0 hcenter).
  by rewrite /KeygenM23MatrixSpec.poly_words_i
             /KeygenM23MatrixSpec.mode2_s1_words_i
             /KeygenM23MatrixSpec.mode2_cols_i.
split.
+ apply KeygenM23ArithmeticSpec.wide_slice_repr_bound_self.
  apply (centered_wide_slice_bound16
           s KeygenM23MatrixSpec.poly_words_i hcenter).
  by rewrite /KeygenM23MatrixSpec.poly_words_i
             /KeygenM23MatrixSpec.mode2_s1_words_i
             /KeygenM23MatrixSpec.mode2_cols_i.
+ apply KeygenM23ArithmeticSpec.wide_slice_repr_bound_self.
  apply (centered_wide_slice_bound16
           s (2 * KeygenM23MatrixSpec.poly_words_i) hcenter).
  by rewrite /KeygenM23MatrixSpec.poly_words_i
             /KeygenM23MatrixSpec.mode2_s1_words_i
             /KeygenM23MatrixSpec.mode2_cols_i.
qed.

(* This proof-only observer extends the checked first-attempt sampler prefix
   through the actual extracted [_kp_m23_matrix] helper.  It is deliberately
   not [Parent._keypair_full_m23]: finalization, singularity rejection, retry
   control, and packing remain outside this procedure. *)
module CheckedMode2ParentM23Prefix = {
  proc run
      (seedbuf : BArray128.t, mat : BArray32768.t,
       avec : BArray8192.t, s1 : BArray8192.t, s2 : BArray8192.t,
       bp : BArray8192.t, s1hatp : BArray8192.t,
       raw_seed : BArray32.t)
      : BArray128.t * BArray32768.t * BArray8192.t *
        BArray8192.t * BArray8192.t = {
    var counter : W64.t;

    (seedbuf, mat, avec, s1, s2, counter) <@
      TargetKeygenMode2ParentComposition.CheckedMode2ParentSamplerPrefix.run
        (seedbuf, mat, avec, s1, s2, raw_seed);
    (bp, s1hatp) <@ Parent._kp_m23_matrix
      (bp, s1hatp, mat, s1,
       W64.of_int KeygenM23MatrixSpec.mode2_rows_i,
       W64.of_int KeygenM23MatrixSpec.mode2_cols_i);
    return (seedbuf, mat, s1, bp, s1hatp);
  }
}.

lemma checked_mode2_parent_m23_prefix_correct
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  hoare [CheckedMode2ParentM23Prefix.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0
    ==>
    KeygenSeedXofSpec.output_matches res.`1 raw_seed0 /\
    KeygenSeedXofSpec.uniform_seed_slice_matches res.`1 raw_seed0 /\
    KeygenSeedXofSpec.eta_seed_slice_matches res.`1 raw_seed0 /\
    KeygenSamplerCallersSpec.uniform_matrix_stream32768
      res.`2 res.`1 KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.uniform_matrix_range32768
      res.`2 KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.uniform_matrix_frame32768
      mat0 res.`2 KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.eta_vector_stream8192
      res.`3 res.`1 W64.zero KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.eta_vector_centered8192
      res.`3 KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenSamplerCallersSpec.eta_vector_frame8192
      s10 res.`3 KeygenSamplerCallersSpec.mode2_m_i /\
    KeygenM23ArithmeticSpec.matrix_active_bound16 res.`2 /\
    KeygenM23ArithmeticSpec.mode2_input_repr_bound16
      res.`3
      (KeygenM23ArithmeticSpec.wide_poly res.`3 0)
      (KeygenM23ArithmeticSpec.wide_poly
        res.`3 KeygenM23MatrixSpec.poly_words_i)
      (KeygenM23ArithmeticSpec.wide_poly
        res.`3 (2 * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23ArithmeticSpec.mode2_output_repr_bound16
      res.`4 res.`2
      (KeygenM23ArithmeticSpec.wide_poly res.`3 0)
      (KeygenM23ArithmeticSpec.wide_poly
        res.`3 KeygenM23MatrixSpec.poly_words_i)
      (KeygenM23ArithmeticSpec.wide_poly
        res.`3 (2 * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
      res.`5
      (KeygenM23ArithmeticSpec.wide_poly res.`3 0)
      (KeygenM23ArithmeticSpec.wide_poly
        res.`3 KeygenM23MatrixSpec.poly_words_i)
      (KeygenM23ArithmeticSpec.wide_poly
        res.`3 (2 * KeygenM23MatrixSpec.poly_words_i)) /\
    KeygenM23MatrixSpec.word_tail_frame
      bp0 res.`4 KeygenM23MatrixSpec.mode2_b_words_i /\
    KeygenM23MatrixSpec.word_tail_frame
      s1hat0 res.`5 KeygenM23MatrixSpec.mode2_s1_words_i].
proof.
proc.
seq 1 :
  (KeygenSeedXofSpec.output_matches seedbuf raw_seed0 /\
   KeygenSeedXofSpec.uniform_seed_slice_matches seedbuf raw_seed0 /\
   KeygenSeedXofSpec.eta_seed_slice_matches seedbuf raw_seed0 /\
   KeygenSamplerCallersSpec.uniform_matrix_stream32768
     mat seedbuf KeygenSamplerCallersSpec.mode2_k_i
       KeygenSamplerCallersSpec.mode2_m_i /\
   KeygenSamplerCallersSpec.uniform_matrix_range32768
     mat KeygenSamplerCallersSpec.mode2_k_i
       KeygenSamplerCallersSpec.mode2_m_i /\
   KeygenSamplerCallersSpec.uniform_matrix_frame32768
     mat0 mat KeygenSamplerCallersSpec.mode2_k_i
       KeygenSamplerCallersSpec.mode2_m_i /\
   KeygenSamplerCallersSpec.eta_vector_stream8192
     s1 seedbuf W64.zero KeygenSamplerCallersSpec.mode2_m_i /\
   KeygenSamplerCallersSpec.eta_vector_centered8192
     s1 KeygenSamplerCallersSpec.mode2_m_i /\
   KeygenSamplerCallersSpec.eta_vector_frame8192
     s10 s1 KeygenSamplerCallersSpec.mode2_m_i /\
   bp = bp0 /\ s1hatp = s1hat0).
+ call
    (TargetKeygenMode2ParentComposition.checked_mode2_parent_sampler_prefix_correct
         seedbuf0 mat0 avec0 s10 s20 raw_seed0).
  auto => />.
exlim seedbuf => sampled_seed.
exlim mat => sampled_mat.
exlim s1 => sampled_s1.
call
  (TargetKeygenM23Arithmetic.kp_m23_matrix_mode2_arithmetic_correct
    bp0 s1hat0 sampled_mat sampled_s1
    (KeygenM23ArithmeticSpec.wide_poly sampled_s1 0)
    (KeygenM23ArithmeticSpec.wide_poly
      sampled_s1 KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23ArithmeticSpec.wide_poly
      sampled_s1 (2 * KeygenM23MatrixSpec.poly_words_i))).
auto => />;
  smt(sampler_matrix_range_mode2_bound16
      sampler_eta_mode2_input_repr_bound16).
qed.

lemma checked_mode2_parent_m23_prefix_progress_ll
    (seedbuf0 : BArray128.t) (raw_seed0 : BArray32.t)
    mat_limit vec_limit eta_limit :
  phoare [CheckedMode2ParentM23Prefix.run :
    seedbuf = seedbuf0 /\ raw_seed = raw_seed0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit
    ==> true] = 1%r.
proof.
proc.
call TargetKeygenM23Matrix.kp_m23_matrix_mode2_ll.
call
  (TargetKeygenMode2ParentComposition.checked_mode2_parent_sampler_prefix_progress_ll
       seedbuf0 raw_seed0 mat_limit vec_limit eta_limit).
auto => />.
qed.

end TargetKeygenM23ParentComposition.
