require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

require import BArray128 BArray8192.
require import KeygenShakeStreamSpec
               KeygenUniformXofLeafSpec KeygenSamplerCallersSpec.
require import KeygenM23FinalizeSemantics.
require import Mode2KeygenSnapshotAlgebra.

theory KgActualAvecQjSemantics.

(* Exact deterministic stream used for Mode-2 [a].  The XOF input is the
   first 32 bytes of [seed], followed by the little-endian row nonce. *)
op mode2_a_xof_bytes
    (seed : BArray128.t) (row blocks : int) : int list =
  KeygenShakeStreamSpec.shake128_squeeze_bytes
    (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
      seed (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
      (KeygenSamplerCallersSpec.vector_nonce_word 2 3 row))
    blocks.

op mode2_a_candidate
    (seed : BArray128.t) (row blocks pair : int) : int =
  KeygenUniformXofLeafSpec.uniform_le16
    (mode2_a_xof_bytes seed row blocks) pair.

op mode2_a_accepted_values
    (seed : BArray128.t) (row blocks pairs : int) : int list =
  KeygenUniformXofLeafSpec.uniform_accepted
    (mode2_a_xof_bytes seed row blocks) pairs.

lemma mode2_a_candidate_le16
    (seed : BArray128.t) row blocks pair :
  mode2_a_candidate seed row blocks pair =
    nth 0 (mode2_a_xof_bytes seed row blocks) (2 * pair) +
    256 * nth 0 (mode2_a_xof_bytes seed row blocks) (2 * pair + 1).
proof.
by rewrite /mode2_a_candidate /KeygenUniformXofLeafSpec.uniform_le16.
qed.

lemma mode2_a_rejection_filter
    (seed : BArray128.t) row blocks pairs :
  mode2_a_accepted_values seed row blocks pairs =
    filter
      (fun t => t < KeygenUniformXofLeafSpec.uniform_q_i)
      (mkseq (mode2_a_candidate seed row blocks) pairs).
proof.
by rewrite /mode2_a_accepted_values
           /KeygenUniformXofLeafSpec.uniform_accepted
           /KeygenUniformXofLeafSpec.uniform_candidates
           /mode2_a_candidate.
qed.

lemma caller_uniform_values_mode2
    (seed : BArray128.t) row blocks pairs :
  KeygenSamplerCallersSpec.caller_uniform_values
    seed (KeygenSamplerCallersSpec.vector_nonce_word 2 3 row)
    blocks pairs =
  mode2_a_accepted_values seed row blocks pairs.
proof.
by rewrite /KeygenSamplerCallersSpec.caller_uniform_values
           /mode2_a_accepted_values /mode2_a_xof_bytes.
qed.

lemma mode2_a_padding_bytes
    (seed : BArray128.t) row :
  nth 0
    (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
      seed (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
      (KeygenSamplerCallersSpec.vector_nonce_word 2 3 row)) 34 = 31 /\
  nth 0
    (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
      seed (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
      (KeygenSamplerCallersSpec.vector_nonce_word 2 3 row)) 167 = 128.
proof.
exact (KeygenShakeStreamSpec.shake128_padding_positions
  seed (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
  (KeygenSamplerCallersSpec.vector_nonce_word 2 3 row)).
qed.

lemma mode2_a_xof_bytes_size
    (seed : BArray128.t) row blocks :
  0 <= blocks =>
  size (mode2_a_xof_bytes seed row blocks) = blocks * 168.
proof.
move=> hblocks.
rewrite /mode2_a_xof_bytes /KeygenShakeStreamSpec.shake128_squeeze_bytes.
exact (KeygenShakeStreamSpec.squeeze_bytes_iter_size
  (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
    seed (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
    (KeygenSamplerCallersSpec.vector_nonce_word 2 3 row))
  168 blocks _ hblocks).
qed.

lemma mode2_a_initial_xof_bytes_size
    (seed : BArray128.t) row :
  size (mode2_a_xof_bytes seed row 4) = 672.
proof.
by rewrite mode2_a_xof_bytes_size.
qed.

(* Paper [a] is the two-polynomial output of ExpandVec_a.  This predicate is
   deliberately existential in the finite number of blocks/pairs consumed:
   it specifies every terminating deterministic execution, but neither
   sampler termination nor any probability distribution. *)
op paper_mode2_a_coeff
    (seed : BArray128.t) (row coeff value : int) : bool =
  exists blocks pairs,
    4 <= blocks /\
    0 <= pairs <=
      blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
    size (KeygenSamplerCallersSpec.caller_uniform_values
      seed
      (KeygenSamplerCallersSpec.vector_nonce_word
        KeygenSamplerCallersSpec.mode2_k_i
        KeygenSamplerCallersSpec.mode2_m_i row)
      blocks pairs) =
      KeygenUniformXofLeafSpec.uniform_poly_words_i /\
    value = nth 0
      (KeygenSamplerCallersSpec.caller_uniform_values
        seed
        (KeygenSamplerCallersSpec.vector_nonce_word
          KeygenSamplerCallersSpec.mode2_k_i
          KeygenSamplerCallersSpec.mode2_m_i row)
        blocks pairs) coeff.

(* The paper vector j=(1,0)^T contains the constant ring polynomial one in
   row zero.  Consequently q*j contributes +q only at flattened coefficient
   (row,coeff)=(0,0), not to the whole first polynomial. *)
op paper_j_coeff (row coeff : int) : int =
  if row = 0 /\ coeff = 0 then 1 else 0.

op paper_qj_coeff (row coeff : int) : int =
  KeygenM23FinalizeSemantics.q * paper_j_coeff row coeff.

lemma mode2_uniform_stream_paper_a_coeff
    (avec : BArray8192.t) (seed : BArray128.t) row coeff :
  KeygenSamplerCallersSpec.uniform_vector_stream8192
    avec seed
    KeygenSamplerCallersSpec.mode2_k_i
    KeygenSamplerCallersSpec.mode2_m_i
    KeygenSamplerCallersSpec.mode2_k_i =>
  0 <= row < KeygenSamplerCallersSpec.mode2_k_i =>
  0 <= coeff < KeygenUniformXofLeafSpec.uniform_poly_words_i =>
  paper_mode2_a_coeff seed row coeff
    (W32.to_uint
      (BArray8192.get32 avec
        (KeygenSamplerCallersSpec.uniform_vector_words_i row + coeff))).
proof.
rewrite /KeygenSamplerCallersSpec.uniform_vector_stream8192.
move=> hstream hrow hcoeff.
case: (hstream row hrow) => blocks pairs.
move=> [hblocks [hpairs [hsize hdecoded]]].
exists blocks pairs.
split; first exact hblocks.
split; first exact hpairs.
split; first exact hsize.
rewrite (hdecoded coeff _).
+ by rewrite hsize.
trivial.
qed.

lemma mode2_uniform_stream_paper_a_flat
    (avec : BArray8192.t) (seed : BArray128.t) row coeff :
  KeygenSamplerCallersSpec.uniform_vector_stream8192
    avec seed 2 3 2 =>
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  paper_mode2_a_coeff seed row coeff
    (W32.to_uint
      (BArray8192.get32 avec (row * 256 + coeff))).
proof.
move=> hstream hrow hcoeff.
have h := mode2_uniform_stream_paper_a_coeff
  avec seed row coeff _ _ _.
+ move: hstream.
  by rewrite /KeygenSamplerCallersSpec.mode2_k_i
             /KeygenSamplerCallersSpec.mode2_m_i.
+ move: hrow.
  by rewrite /KeygenSamplerCallersSpec.mode2_k_i.
+ move: hcoeff.
  by rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i.
move: h.
rewrite /KeygenSamplerCallersSpec.uniform_vector_words_i
        /KeygenUniformXofLeafSpec.uniform_poly_words_i.
done.
qed.

(* The stored coefficient is literally the selected accepted LE16 candidate.
   There is no subsequent reduction modulo q. *)
lemma mode2_uniform_stream_parsed_coefficient
    (avec : BArray8192.t) (seed : BArray128.t) row coeff :
  KeygenSamplerCallersSpec.uniform_vector_stream8192
    avec seed 2 3 2 =>
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  exists blocks pairs,
    4 <= blocks /\
    0 <= pairs <=
      blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
    size (mode2_a_accepted_values seed row blocks pairs) = 256 /\
    W32.to_uint
      (BArray8192.get32 avec (row * 256 + coeff)) =
    nth 0 (mode2_a_accepted_values seed row blocks pairs) coeff.
proof.
move=> hstream hrow hcoeff.
have hpaper := mode2_uniform_stream_paper_a_flat
  avec seed row coeff hstream hrow hcoeff.
case: hpaper => blocks pairs [hblocks [hpairs [hsize hvalue]]].
exists blocks pairs.
split; first exact hblocks.
split; first exact hpairs.
split.
+ move: hsize.
  rewrite caller_uniform_values_mode2
          /KeygenUniformXofLeafSpec.uniform_poly_words_i.
  trivial.
move: hvalue.
by rewrite caller_uniform_values_mode2.
qed.

lemma mode2_paper_a_coefficient_canonical
    (avec : BArray8192.t) (seed : BArray128.t) row coeff :
  KeygenSamplerCallersSpec.uniform_vector_stream8192 avec seed 2 3 2 =>
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  W32.to_uint (BArray8192.get32 avec (row * 256 + coeff)) <
    KeygenM23FinalizeSemantics.q.
proof.
move=> hstream hrow hcoeff.
have hrange :=
  KeygenSamplerCallersSpec.uniform_vector_stream8192_range
    avec seed 2 3 2 hstream.
rewrite /KeygenSamplerCallersSpec.uniform_vector_range8192 in hrange.
have hrow_range := hrange row hrow.
rewrite /KeygenUniformXofLeafSpec.bounded_prefix8192 in hrow_range.
have h := hrow_range coeff _.
+ move: hcoeff.
  by rewrite /KeygenUniformXofLeafSpec.uniform_poly_words_i.
move: h.
rewrite /KeygenSamplerCallersSpec.uniform_vector_words_i
        /KeygenUniformXofLeafSpec.uniform_poly_words_i
        /KeygenUniformXofLeafSpec.uniform_q_i
        /KeygenM23FinalizeSemantics.q.
done.
qed.

lemma mode2_paper_a_active_canonical
    (avec : BArray8192.t) (seed : BArray128.t) :
  KeygenSamplerCallersSpec.uniform_vector_stream8192 avec seed 2 3 2 =>
  forall flat,
    0 <= flat < 512 =>
    W32.to_uint (BArray8192.get32 avec flat) <
      KeygenM23FinalizeSemantics.q.
proof.
move=> hstream flat hflat.
pose row := flat %/ 256.
pose coeff := flat %% 256.
have hrow : 0 <= row < 2.
+ rewrite /row.
  smt(@IntDiv).
have hcoeff : 0 <= coeff < 256.
+ rewrite /coeff.
  smt(@IntDiv).
have hsplit : row * 256 + coeff = flat.
+ rewrite /row /coeff.
  have h := divz_eq flat 256.
  smt().
rewrite -hsplit.
exact (mode2_paper_a_coefficient_canonical
  avec seed row coeff hstream hrow hcoeff).
qed.

lemma mode2_paper_a_stored_without_reduction
    (avec : BArray8192.t) (seed : BArray128.t) row coeff :
  KeygenSamplerCallersSpec.uniform_vector_stream8192 avec seed 2 3 2 =>
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  W32.to_uint (BArray8192.get32 avec (row * 256 + coeff)) %%
    KeygenM23FinalizeSemantics.q =
  W32.to_uint (BArray8192.get32 avec (row * 256 + coeff)).
proof.
move=> hstream hrow hcoeff.
have hlt := mode2_paper_a_coefficient_canonical
  avec seed row coeff hstream hrow hcoeff.
apply modz_small.
split; first smt(W32.to_uint_cmp).
move: hlt.
by rewrite /KeygenM23FinalizeSemantics.q /=.
qed.

lemma mode2_vector_nonce_row0 :
  KeygenSamplerCallersSpec.vector_nonce_i 2 3 0 = 515.
proof. by []. qed.

lemma mode2_vector_nonce_row1 :
  KeygenSamplerCallersSpec.vector_nonce_i 2 3 1 = 516.
proof. by []. qed.

lemma mode2_vector_seed_byte
    (seed : BArray128.t) row byte_index :
  0 <= row < 2 =>
  0 <= byte_index < 32 =>
  nth 0
    (KeygenShakeStreamSpec.shake128_seed_nonce_input
      seed (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
      (KeygenSamplerCallersSpec.vector_nonce_word 2 3 row))
    byte_index =
  W8.to_uint (BArray128.get8 seed byte_index).
proof.
move=> _ hbyte.
exact (KeygenSamplerCallersSpec.caller_uniform_seed_input_prefix
  seed (KeygenSamplerCallersSpec.vector_nonce_word 2 3 row)
  byte_index hbyte).
qed.

lemma mode2_vector_nonce_bytes
    (seed : BArray128.t) row :
  0 <= row < 2 =>
  nth 0
    (KeygenShakeStreamSpec.shake128_seed_nonce_input
      seed (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
      (KeygenSamplerCallersSpec.vector_nonce_word 2 3 row)) 32 =
    3 + row /\
  nth 0
    (KeygenShakeStreamSpec.shake128_seed_nonce_input
      seed (W64.of_int KeygenSamplerCallersSpec.uniform_seed_offset_i)
      (KeygenSamplerCallersSpec.vector_nonce_word 2 3 row)) 33 = 2.
proof.
move=> hrow.
have h := KeygenSamplerCallersSpec.mode2_vector_uniform_nonce_input_tail
  seed row _.
+ move: hrow.
  by rewrite /KeygenSamplerCallersSpec.mode2_k_i.
move: h.
by rewrite /KeygenSamplerCallersSpec.mode2_k_i
           /KeygenSamplerCallersSpec.mode2_m_i.
qed.

lemma paper_qj_row0_coeff0 :
  paper_qj_coeff 0 0 = KeygenM23FinalizeSemantics.q.
proof. by rewrite /paper_qj_coeff /paper_j_coeff. qed.

lemma paper_qj_row0_other coeff :
  0 < coeff =>
  paper_qj_coeff 0 coeff = 0.
proof. by rewrite /paper_qj_coeff /paper_j_coeff; smt(). qed.

lemma paper_qj_remaining_row row coeff :
  0 < row =>
  paper_qj_coeff row coeff = 0.
proof. by rewrite /paper_qj_coeff /paper_j_coeff; smt(). qed.

lemma paper_qj_mode2_cases row coeff :
  0 <= row < 2 =>
  0 <= coeff < 256 =>
  paper_qj_coeff row coeff =
    if row = 0 /\ coeff = 0
    then KeygenM23FinalizeSemantics.q else 0.
proof. by rewrite /paper_qj_coeff /paper_j_coeff; smt(). qed.

lemma snapshot_paper_qj_coefficient row coeff mul e a :
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (Mode2KeygenSnapshotAlgebra.snapshot_expression_from_product
      mul e a (paper_j_coeff row coeff))
    (paper_qj_coeff row coeff).
proof.
rewrite /paper_qj_coeff.
exact
  (Mode2KeygenSnapshotAlgebra.snapshot_expression_from_product_congruent_mod_2q
    mul e a (paper_j_coeff row coeff)).
qed.

lemma snapshot_paper_qj_row0_coeff0 mul e a :
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (Mode2KeygenSnapshotAlgebra.snapshot_expression_from_product mul e a 1)
    KeygenM23FinalizeSemantics.q.
proof.
have h := snapshot_paper_qj_coefficient 0 0 mul e a.
move: h.
by rewrite /paper_j_coeff paper_qj_row0_coeff0.
qed.

lemma snapshot_paper_qj_row0_other coeff mul e a :
  0 < coeff =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (Mode2KeygenSnapshotAlgebra.snapshot_expression_from_product mul e a 0)
    0.
proof.
move=> hcoeff.
have h := snapshot_paper_qj_coefficient 0 coeff mul e a.
move: h.
by rewrite /paper_j_coeff paper_qj_row0_other 1:hcoeff; smt().
qed.

lemma snapshot_paper_qj_remaining_row
    (row coeff mul e a : int) :
  0 < row =>
  Mode2KeygenSnapshotAlgebra.congruent_mod_2q
    (Mode2KeygenSnapshotAlgebra.snapshot_expression_from_product mul e a 0)
    0.
proof.
move=> hrow.
have h := snapshot_paper_qj_coefficient row coeff mul e a.
move: h.
by rewrite /paper_j_coeff paper_qj_remaining_row 1:hrow; smt().
qed.

end KgActualAvecQjSemantics.
