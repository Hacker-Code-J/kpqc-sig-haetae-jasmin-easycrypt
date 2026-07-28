require import AllCore.

from Jasmin require import JModel_x86.

require import BArray32 BArray128.
require import KeygenSeedXofSpec KeygenSamplerCallersSpec
               KeygenUniformXofLeafSpec KeygenEtaSamplerSpec.

theory KeygenMode2ParentSpec.

(* The endpoint maps are explicit deterministic witnesses.  Each entry
   certifies finite progress for exactly one sampler invocation in the
   mode-2 parent prefix; no distributional property is assumed here. *)
op mode2_matrix_uniform_progress
    (expanded : BArray128.t) (mat_limit : int -> int -> int) : bool =
  forall row col,
    0 <= row < KeygenSamplerCallersSpec.mode2_k_i =>
    0 <= col < KeygenSamplerCallersSpec.mode2_m_i =>
    KeygenUniformXofLeafSpec.uniform_progress_prefix
      expanded
      (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
      (KeygenSamplerCallersSpec.matrix_nonce_word row col)
      (mat_limit row col).

op mode2_vector_uniform_progress
    (expanded : BArray128.t) (vec_limit : int -> int) : bool =
  forall slot,
    0 <= slot < KeygenSamplerCallersSpec.mode2_k_i =>
    KeygenUniformXofLeafSpec.uniform_progress_prefix
      expanded
      (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
      (KeygenSamplerCallersSpec.vector_nonce_word
        KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i slot)
      (vec_limit slot).

op mode2_first_attempt_eta_progress
    (expanded : BArray128.t) (eta_limit : int -> int) : bool =
  forall slot,
    0 <= slot < KeygenSamplerCallersSpec.mode2_retry_span_i =>
    KeygenEtaSamplerSpec.eta_progress_prefix
      expanded
      (W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i)
      (W64.of_int
        (KeygenSamplerCallersSpec.mode2_eta_nonce_i 0 slot))
      (eta_limit slot).

op mode2_sampler_prefix_progress
    (raw_seed : BArray32.t)
    (mat_limit : int -> int -> int)
    (vec_limit : int -> int)
    (eta_limit : int -> int) : bool =
  forall expanded,
    KeygenSeedXofSpec.output_matches expanded raw_seed =>
    mode2_matrix_uniform_progress expanded mat_limit /\
    mode2_vector_uniform_progress expanded vec_limit /\
    mode2_first_attempt_eta_progress expanded eta_limit.

lemma mode2_matrix_uniform_progress_at
    expanded mat_limit row col :
  mode2_matrix_uniform_progress expanded mat_limit =>
  0 <= row < KeygenSamplerCallersSpec.mode2_k_i =>
  0 <= col < KeygenSamplerCallersSpec.mode2_m_i =>
  KeygenUniformXofLeafSpec.uniform_progress_prefix
    expanded
    (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
    (KeygenSamplerCallersSpec.matrix_nonce_word row col)
    (mat_limit row col).
proof.
rewrite /mode2_matrix_uniform_progress.
by move=> hprogress hrow hcol; apply hprogress.
qed.

lemma mode2_vector_uniform_progress_at expanded vec_limit slot :
  mode2_vector_uniform_progress expanded vec_limit =>
  0 <= slot < KeygenSamplerCallersSpec.mode2_k_i =>
  KeygenUniformXofLeafSpec.uniform_progress_prefix
    expanded
    (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
    (KeygenSamplerCallersSpec.vector_nonce_word
      KeygenSamplerCallersSpec.mode2_k_i
      KeygenSamplerCallersSpec.mode2_m_i slot)
    (vec_limit slot).
proof.
rewrite /mode2_vector_uniform_progress.
by move=> hprogress hslot; apply hprogress.
qed.

lemma mode2_first_attempt_eta_progress_at expanded eta_limit slot :
  mode2_first_attempt_eta_progress expanded eta_limit =>
  0 <= slot < KeygenSamplerCallersSpec.mode2_retry_span_i =>
  KeygenEtaSamplerSpec.eta_progress_prefix
    expanded
    (W64.of_int KeygenSamplerCallersSpec.eta_seed_offset_i)
    (W64.of_int
      (KeygenSamplerCallersSpec.mode2_eta_nonce_i 0 slot))
    (eta_limit slot).
proof.
rewrite /mode2_first_attempt_eta_progress.
by move=> hprogress hslot; apply hprogress.
qed.

lemma mode2_sampler_prefix_progress_expanded
    raw_seed mat_limit vec_limit eta_limit expanded :
  mode2_sampler_prefix_progress raw_seed mat_limit vec_limit eta_limit =>
  KeygenSeedXofSpec.output_matches expanded raw_seed =>
  mode2_matrix_uniform_progress expanded mat_limit /\
  mode2_vector_uniform_progress expanded vec_limit /\
  mode2_first_attempt_eta_progress expanded eta_limit.
proof.
rewrite /mode2_sampler_prefix_progress.
by move=> hprogress hmatches; apply hprogress.
qed.

end KeygenMode2ParentSpec.
