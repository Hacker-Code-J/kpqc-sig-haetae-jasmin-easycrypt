require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import KeygenMode2ParentTarget
               KeygenMode2ParentSpec
               KeygenSeedXofSpec KeygenSamplerCallersSpec
               KeygenM23MatrixSpec KeygenM23ArithmeticSpec
               KeygenM23FinalizeSpec
               TargetKeygenMode2ParentComposition
               TargetKeygenM23ParentComposition
               TargetKeygenM23Arithmetic
               TargetKeygenM23Matrix
               TargetKeygenM23Finalize.

theory TargetKeygenM23FinalizeComposition.

module Parent = KeygenMode2ParentTarget.M.

op mode2_sampler_facts
    (seedbuf : BArray128.t)
    (mat : BArray32768.t)
    (avec s1 s2 : BArray8192.t)
    (counter : W64.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 : BArray8192.t)
    (raw_seed0 : BArray32.t) : bool =
  KeygenSeedXofSpec.output_matches seedbuf raw_seed0 /\
  KeygenSeedXofSpec.uniform_seed_slice_matches seedbuf raw_seed0 /\
  KeygenSeedXofSpec.eta_seed_slice_matches seedbuf raw_seed0 /\
  KeygenSeedXofSpec.key_seed_slice_matches seedbuf raw_seed0 /\
  KeygenSamplerCallersSpec.uniform_matrix_stream32768
    mat seedbuf KeygenSamplerCallersSpec.mode2_k_i
      KeygenSamplerCallersSpec.mode2_m_i /\
  KeygenSamplerCallersSpec.uniform_matrix_range32768
    mat KeygenSamplerCallersSpec.mode2_k_i
      KeygenSamplerCallersSpec.mode2_m_i /\
  KeygenSamplerCallersSpec.uniform_matrix_frame32768
    mat0 mat KeygenSamplerCallersSpec.mode2_k_i
      KeygenSamplerCallersSpec.mode2_m_i /\
  KeygenSamplerCallersSpec.uniform_vector_stream8192
    avec seedbuf KeygenSamplerCallersSpec.mode2_k_i
      KeygenSamplerCallersSpec.mode2_m_i
      KeygenSamplerCallersSpec.mode2_k_i /\
  KeygenSamplerCallersSpec.uniform_vector_range8192
    avec KeygenSamplerCallersSpec.mode2_k_i /\
  KeygenSamplerCallersSpec.uniform_vector_frame8192
    avec0 avec KeygenSamplerCallersSpec.mode2_k_i /\
  KeygenSamplerCallersSpec.eta_vector_stream8192
    s1 seedbuf (W64.of_int 0)
      KeygenSamplerCallersSpec.mode2_m_i /\
  KeygenSamplerCallersSpec.eta_vector_centered8192
    s1 KeygenSamplerCallersSpec.mode2_m_i /\
  KeygenSamplerCallersSpec.eta_vector_frame8192
    s10 s1 KeygenSamplerCallersSpec.mode2_m_i /\
  KeygenSamplerCallersSpec.eta_vector_stream8192
    s2 seedbuf (W64.of_int KeygenSamplerCallersSpec.mode2_m_i)
      KeygenSamplerCallersSpec.mode2_k_i /\
  KeygenSamplerCallersSpec.eta_vector_centered8192
    s2 KeygenSamplerCallersSpec.mode2_k_i /\
  KeygenSamplerCallersSpec.eta_vector_frame8192
    s20 s2 KeygenSamplerCallersSpec.mode2_k_i /\
  counter =
    W64.of_int KeygenSamplerCallersSpec.mode2_retry_span_i /\
  counter = W64.of_int 5.

op mode2_m23_facts
    (mat : BArray32768.t)
    (s1 bp s1hatp : BArray8192.t)
    (bp0 s1hat0 : BArray8192.t) : bool =
  KeygenM23ArithmeticSpec.matrix_active_bound16 mat /\
  KeygenM23ArithmeticSpec.mode2_input_repr_bound16
    s1
    (KeygenM23ArithmeticSpec.wide_poly s1 0)
    (KeygenM23ArithmeticSpec.wide_poly
      s1 KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23ArithmeticSpec.wide_poly
      s1 (2 * KeygenM23MatrixSpec.poly_words_i)) /\
  KeygenM23ArithmeticSpec.mode2_output_repr_bound16
    bp mat
    (KeygenM23ArithmeticSpec.wide_poly s1 0)
    (KeygenM23ArithmeticSpec.wide_poly
      s1 KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23ArithmeticSpec.wide_poly
      s1 (2 * KeygenM23MatrixSpec.poly_words_i)) /\
  KeygenM23ArithmeticSpec.mode2_ntt_repr_bound24
    s1hatp
    (KeygenM23ArithmeticSpec.wide_poly s1 0)
    (KeygenM23ArithmeticSpec.wide_poly
      s1 KeygenM23MatrixSpec.poly_words_i)
    (KeygenM23ArithmeticSpec.wide_poly
      s1 (2 * KeygenM23MatrixSpec.poly_words_i)) /\
  KeygenM23MatrixSpec.word_tail_frame
    bp0 bp KeygenM23MatrixSpec.mode2_b_words_i /\
  KeygenM23MatrixSpec.word_tail_frame
    s1hat0 s1hatp KeygenM23MatrixSpec.mode2_s1_words_i.

(* This proof-only observer follows the checked first-attempt sampler through
   the actual extracted [_kp_m23_matrix] and [_keypair_finalize_m23] helpers.
   It is not [Parent._keypair_full_m23]: singularity rejection, retry control,
   and packing remain outside this procedure. *)
module CheckedMode2ParentM23Finalize = {
  proc run
      (seedbuf : BArray128.t, mat : BArray32768.t,
       avec : BArray8192.t, s1 : BArray8192.t, s2 : BArray8192.t,
       bp : BArray8192.t, s1hatp : BArray8192.t,
       raw_seed : BArray32.t)
      : BArray128.t * BArray32768.t *
        BArray8192.t * BArray8192.t * BArray8192.t * W64.t *
        BArray8192.t * BArray8192.t *
        BArray8192.t * BArray8192.t = {
    var counter : W64.t;
    var pre_bp : BArray8192.t;
    var sampled_s2 : BArray8192.t;
    var sampled_avec : BArray8192.t;

    (seedbuf, mat, avec, s1, s2, counter) <@
      TargetKeygenMode2ParentComposition.CheckedMode2ParentSamplerPrefix.run
        (seedbuf, mat, avec, s1, s2, raw_seed);
    (bp, s1hatp) <@ Parent._kp_m23_matrix
      (bp, s1hatp, mat, s1,
       W64.of_int KeygenM23MatrixSpec.mode2_rows_i,
       W64.of_int KeygenM23MatrixSpec.mode2_cols_i);
    pre_bp <- bp;
    sampled_s2 <- s2;
    sampled_avec <- avec;
    (bp, s2) <@ Parent._keypair_finalize_m23
      (bp, s2, avec,
       W64.of_int KeygenM23MatrixSpec.mode2_b_words_i);
    return
      (seedbuf, mat, sampled_avec, s1, sampled_s2, counter,
       pre_bp, s1hatp, bp, s2);
  }
}.

lemma checked_mode2_parent_m23_finalize_correct
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  hoare [CheckedMode2ParentM23Finalize.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\
    avec = avec0 /\ s1 = s10 /\ s2 = s20 /\
    bp = bp0 /\ s1hatp = s1hat0 /\ raw_seed = raw_seed0
    ==>
    mode2_sampler_facts
      res.`1 res.`2 res.`3 res.`4 res.`5 res.`6
      mat0 avec0 s10 s20 raw_seed0 /\
    mode2_m23_facts
      res.`2 res.`4 res.`7 res.`8 bp0 s1hat0 /\
    KeygenM23FinalizeSpec.finalize_output
      res.`7 res.`5 res.`3 res.`9 res.`10].
proof.
proc.
seq 1 :
  (mode2_sampler_facts
     seedbuf mat avec s1 s2 counter
     mat0 avec0 s10 s20 raw_seed0 /\
   bp = bp0 /\ s1hatp = s1hat0).
+ call
    (TargetKeygenMode2ParentComposition.checked_mode2_parent_sampler_prefix_correct
         seedbuf0 mat0 avec0 s10 s20 raw_seed0).
  auto => />.
  rewrite /mode2_sampler_facts.
  trivial.
exlim seedbuf => sampled_seed.
exlim mat => sampled_mat.
exlim avec => sampled_avec0.
exlim s1 => sampled_s1.
exlim s2 => sampled_s20.
exlim counter => sampled_counter.
seq 1 :
  (mode2_sampler_facts
     seedbuf mat avec s1 s2 counter
     mat0 avec0 s10 s20 raw_seed0 /\
   mode2_m23_facts
     mat s1 bp s1hatp bp0 s1hat0).
+ call
    (TargetKeygenM23Arithmetic.kp_m23_matrix_mode2_arithmetic_correct
      bp0 s1hat0 sampled_mat sampled_s1
      (KeygenM23ArithmeticSpec.wide_poly sampled_s1 0)
      (KeygenM23ArithmeticSpec.wide_poly
        sampled_s1 KeygenM23MatrixSpec.poly_words_i)
      (KeygenM23ArithmeticSpec.wide_poly
        sampled_s1 (2 * KeygenM23MatrixSpec.poly_words_i))).
  auto => />;
    rewrite /mode2_sampler_facts /mode2_m23_facts;
    smt(TargetKeygenM23ParentComposition.sampler_matrix_range_mode2_bound16
        TargetKeygenM23ParentComposition.sampler_eta_mode2_input_repr_bound16).
exlim bp => prefinal_bp.
exlim s2 => prefinal_s2.
exlim avec => sampled_avec1.
call
  (TargetKeygenM23Finalize.keypair_finalize_m23_mode2_correct
    prefinal_bp prefinal_s2 sampled_avec1).
auto => />.
qed.

lemma checked_mode2_parent_m23_finalize_progress_ll
    (seedbuf0 : BArray128.t) (raw_seed0 : BArray32.t)
    mat_limit vec_limit eta_limit :
  phoare [CheckedMode2ParentM23Finalize.run :
    seedbuf = seedbuf0 /\ raw_seed = raw_seed0 /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_seed0 mat_limit vec_limit eta_limit
    ==> true] = 1%r.
proof.
proc.
seq 1 : true 1%r 1%r 0%r _ => //=.
+ call
    (TargetKeygenMode2ParentComposition.checked_mode2_parent_sampler_prefix_progress_ll
       seedbuf0 raw_seed0 mat_limit vec_limit eta_limit).
  auto => />.
seq 1 : true 1%r 1%r 0%r _ => //=.
+ call TargetKeygenM23Matrix.kp_m23_matrix_mode2_ll.
  auto => />.
seq 3 : true 1%r 1%r 0%r _ => //=.
+ auto.
exlim bp => prefinal_bp.
exlim s2 => prefinal_s2.
exlim avec => sampled_avec.
call
  (TargetKeygenM23Finalize.keypair_finalize_m23_mode2_ll
    prefinal_bp prefinal_s2 sampled_avec).
auto => />.
qed.

end TargetKeygenM23FinalizeComposition.
