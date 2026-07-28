require import AllCore IntDiv CoreMap List Distr Ring StdOrder.

from Jasmin require import JModel_x86.

require import BArray128 BArray8192 BArray32768.
require import KeygenSamplerCallersTarget KeygenUniformXofLeafSpec
               KeygenEtaSamplerSpec KeygenShakeStreamSpec.

theory KeygenSamplerCallersSpec.

op poly_stride_i : int = 256.
op uniform_seed_offset_i : int = 0.
op eta_seed_offset_i : int = 32.
op mode2_k_i : int = 2.
op mode2_m_i : int = 3.
op mode2_retry_span_i : int = mode2_k_i + mode2_m_i.

op matrix_nonce_i (i j : int) : int = 256 * i + j.
op matrix_base_i (cols i j : int) : int =
  (i * cols + j) * poly_stride_i.
op vector_nonce_i (k m i : int) : int = 256 * k + m + i.
op linear_base_i (i : int) : int = i * poly_stride_i.
op mode2_retry_counter_i (retry : int) : int =
  retry * mode2_retry_span_i.
op mode2_eta_nonce_i (retry slot : int) : int =
  mode2_retry_counter_i retry + slot.

op matrix_nonce_word (i j : int) : W64.t =
  W64.of_int (matrix_nonce_i i j).
op matrix_base_word (cols i j : int) : W64.t =
  W64.of_int (matrix_base_i cols i j).
op vector_nonce_word (k m i : int) : W64.t =
  W64.of_int (vector_nonce_i k m i).
op linear_base_word (i : int) : W64.t =
  W64.of_int (linear_base_i i).
op eta_nonce_word (start : W64.t) (i : int) : W64.t =
  start + W64.of_int i.
op nonce_low16 (nonce : W64.t) : int = W64.to_uint nonce %% 65536.

op eta_vector_words_i (count : int) : int =
  count * KeygenEtaSamplerSpec.eta_poly_words_i.

op uniform_vector_words_i (count : int) : int =
  count * KeygenUniformXofLeafSpec.uniform_poly_words_i.

op uniform_matrix_words_i (rows cols : int) : int =
  rows * cols * KeygenUniformXofLeafSpec.uniform_poly_words_i.

op uniform_prefix_frame8192
    (before after : BArray8192.t) (words : int) : bool =
  forall byte_index,
    0 <= byte_index < BArray8192.size =>
    ! (0 <= byte_index < 4 * words) =>
    BArray8192.get8 after byte_index =
      BArray8192.get8 before byte_index.

op uniform_prefix_frame32768
    (before after : BArray32768.t) (words : int) : bool =
  forall byte_index,
    0 <= byte_index < BArray32768.size =>
    ! (0 <= byte_index < 4 * words) =>
    BArray32768.get8 after byte_index =
      BArray32768.get8 before byte_index.

op uniform_vector_frame8192
    (before after : BArray8192.t) (count : int) : bool =
  uniform_prefix_frame8192 before after (uniform_vector_words_i count).

op uniform_matrix_frame32768
    (before after : BArray32768.t) (rows cols : int) : bool =
  uniform_prefix_frame32768 before after (uniform_matrix_words_i rows cols).

op caller_uniform_values
    (seed : BArray128.t) (nonce : W64.t) (blocks pairs : int) : int list =
  KeygenUniformXofLeafSpec.uniform_accepted
    (KeygenShakeStreamSpec.shake128_squeeze_bytes
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed (W64.of_int uniform_seed_offset_i) nonce)
      blocks)
    pairs.

op uniform_vector_stream8192
    (a : BArray8192.t) (seed : BArray128.t)
    (k m count : int) : bool =
  forall slot,
    0 <= slot < count =>
    exists blocks pairs,
      4 <= blocks /\
      0 <= pairs <=
        blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
      size (caller_uniform_values
        seed (vector_nonce_word k m slot) blocks pairs) =
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      KeygenUniformXofLeafSpec.decoded_prefix8192
        a (uniform_vector_words_i slot)
          (caller_uniform_values
            seed (vector_nonce_word k m slot) blocks pairs).

op uniform_vector_range8192 (a : BArray8192.t) (count : int) : bool =
  forall slot,
    0 <= slot < count =>
    KeygenUniformXofLeafSpec.bounded_prefix8192
      a (uniform_vector_words_i slot)
        KeygenUniformXofLeafSpec.uniform_poly_words_i.

op matrix_visited
    (rows cols next_row next_col row col : int) : bool =
  0 <= row < rows /\ 0 <= col < cols /\
  (row < next_row \/ (row = next_row /\ col < next_col)).

op uniform_matrix_stream_prefix32768
    (a : BArray32768.t) (seed : BArray128.t)
    (rows cols next_row next_col : int) : bool =
  forall row col,
    matrix_visited rows cols next_row next_col row col =>
    exists blocks pairs,
      4 <= blocks /\
      0 <= pairs <=
        blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i /\
      size (caller_uniform_values
        seed (matrix_nonce_word row col) blocks pairs) =
        KeygenUniformXofLeafSpec.uniform_poly_words_i /\
      KeygenUniformXofLeafSpec.decoded_prefix32768
        a (matrix_base_i cols row col)
          (caller_uniform_values
            seed (matrix_nonce_word row col) blocks pairs).

op uniform_matrix_stream32768
    (a : BArray32768.t) (seed : BArray128.t)
    (rows cols : int) : bool =
  uniform_matrix_stream_prefix32768 a seed rows cols rows 0.

op uniform_matrix_range32768
    (a : BArray32768.t) (rows cols : int) : bool =
  forall row col,
    0 <= row < rows => 0 <= col < cols =>
    KeygenUniformXofLeafSpec.bounded_prefix32768
      a (matrix_base_i cols row col)
        KeygenUniformXofLeafSpec.uniform_poly_words_i.

op eta_vector_centered8192 (a : BArray8192.t) (count : int) : bool =
  KeygenEtaSamplerSpec.centered_interval8192
    a 0 0 (eta_vector_words_i count).

op eta_vector_frame8192 (before after : BArray8192.t)
                        (count : int) : bool =
  KeygenEtaSamplerSpec.word_frame8192
    before after 0 0 (eta_vector_words_i count).

op caller_eta_values
    (seed : BArray128.t) (start : W64.t) (slot blocks : int) : int list =
  KeygenEtaSamplerSpec.eta_fill []
    (KeygenShakeStreamSpec.shake256_squeeze_bytes
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed (W64.of_int eta_seed_offset_i) (eta_nonce_word start slot))
      blocks).

op eta_vector_stream8192
    (a : BArray8192.t) (seed : BArray128.t) (start : W64.t)
    (count : int) : bool =
  forall slot,
    0 <= slot < count =>
    exists blocks,
      1 <= blocks /\
      size (caller_eta_values seed start slot blocks) =
        KeygenEtaSamplerSpec.eta_poly_words_i /\
      KeygenEtaSamplerSpec.eta_decoded_prefix8192
        a (eta_vector_words_i slot)
          (caller_eta_values seed start slot blocks).

lemma uniform_vector_words_i_succ count :
  uniform_vector_words_i (count + 1) =
  uniform_vector_words_i count +
    KeygenUniformXofLeafSpec.uniform_poly_words_i.
proof. by rewrite /uniform_vector_words_i; ring. qed.

lemma uniform_vector_words_linear count :
  uniform_vector_words_i count = linear_base_i count.
proof.
by rewrite /uniform_vector_words_i /linear_base_i /poly_stride_i
           /KeygenUniformXofLeafSpec.uniform_poly_words_i.
qed.

lemma uniform_matrix_words_base rows cols :
  uniform_matrix_words_i rows cols = matrix_base_i cols rows 0.
proof.
by rewrite /uniform_matrix_words_i /matrix_base_i /poly_stride_i
           /KeygenUniformXofLeafSpec.uniform_poly_words_i; ring.
qed.

lemma matrix_base_i_next_col cols row col :
  matrix_base_i cols row (col + 1) =
  matrix_base_i cols row col +
    KeygenUniformXofLeafSpec.uniform_poly_words_i.
proof.
by rewrite /matrix_base_i /poly_stride_i
           /KeygenUniformXofLeafSpec.uniform_poly_words_i; ring.
qed.

lemma matrix_base_i_rollover cols row :
  matrix_base_i cols row cols = matrix_base_i cols (row + 1) 0.
proof. by rewrite /matrix_base_i; ring. qed.

lemma matrix_base_word_uint cols row col :
  0 <= matrix_base_i cols row col < W64.modulus =>
  W64.to_uint (matrix_base_word cols row col) =
    matrix_base_i cols row col.
proof.
rewrite /matrix_base_word.
by apply W64.to_uint_small.
qed.

lemma matrix_prior_region cols row col prior_row prior_col :
  0 <= cols =>
  0 <= prior_col < cols =>
  0 <= col < cols =>
  (prior_row < row \/ (prior_row = row /\ prior_col < col)) =>
  matrix_base_i cols prior_row prior_col +
    KeygenUniformXofLeafSpec.uniform_poly_words_i <=
  matrix_base_i cols row col.
proof.
rewrite /matrix_base_i /poly_stride_i
        /KeygenUniformXofLeafSpec.uniform_poly_words_i.
by smt().
qed.

lemma uniform_prefix_frame8192_empty a :
  uniform_prefix_frame8192 a a 0.
proof. by rewrite /uniform_prefix_frame8192. qed.

lemma uniform_prefix_frame32768_empty a :
  uniform_prefix_frame32768 a a 0.
proof. by rewrite /uniform_prefix_frame32768. qed.

lemma uniform_prefix_frame8192_extend original before after words :
  0 <= words =>
  uniform_prefix_frame8192 original before words =>
  KeygenUniformXofLeafSpec.frame8192 before after words =>
  uniform_prefix_frame8192 original after
    (words + KeygenUniformXofLeafSpec.uniform_poly_words_i).
proof.
rewrite /uniform_prefix_frame8192
        /KeygenUniformXofLeafSpec.frame8192
        /KeygenUniformXofLeafSpec.in_poly_bytes
        /KeygenUniformXofLeafSpec.uniform_poly_words_i.
move=> hwords hprefix hcurrent byte_index hi hout.
have hsame := hcurrent byte_index hi _.
+ smt().
rewrite hsame.
apply hprefix; first exact hi.
by smt().
qed.

lemma uniform_prefix_frame32768_extend original before after words :
  0 <= words =>
  uniform_prefix_frame32768 original before words =>
  KeygenUniformXofLeafSpec.frame32768 before after words =>
  uniform_prefix_frame32768 original after
    (words + KeygenUniformXofLeafSpec.uniform_poly_words_i).
proof.
rewrite /uniform_prefix_frame32768
        /KeygenUniformXofLeafSpec.frame32768
        /KeygenUniformXofLeafSpec.in_poly_bytes
        /KeygenUniformXofLeafSpec.uniform_poly_words_i.
move=> hwords hprefix hcurrent byte_index hi hout.
have hsame := hcurrent byte_index hi _.
+ smt().
rewrite hsame.
apply hprefix; first exact hi.
by smt().
qed.

lemma uniform_frame8192_get32_before before after current_base word_index :
  0 <= word_index =>
  word_index + 1 <= current_base =>
  current_base + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
    BArray8192.size %/ 4 =>
  KeygenUniformXofLeafSpec.frame8192 before after current_base =>
  BArray8192.get32 after word_index = BArray8192.get32 before word_index.
proof.
move=> hword hbefore hcap hframe.
rewrite /KeygenUniformXofLeafSpec.frame8192 in hframe.
apply W4u8.wordP => byte hbyte.
rewrite BArray8192.get32d_byte 1://.
rewrite BArray8192.get32d_byte 1://.
have hsame := hframe (4 * word_index + byte) _ _.
+ rewrite /BArray8192.size; smt().
+ rewrite /KeygenUniformXofLeafSpec.in_poly_bytes
           /KeygenUniformXofLeafSpec.uniform_poly_words_i.
  smt().
by have := hsame; smt().
qed.

lemma uniform_frame32768_get32_before before after current_base word_index :
  0 <= word_index =>
  word_index + 1 <= current_base =>
  current_base + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
    BArray32768.size %/ 4 =>
  KeygenUniformXofLeafSpec.frame32768 before after current_base =>
  BArray32768.get32 after word_index = BArray32768.get32 before word_index.
proof.
move=> hword hbefore hcap hframe.
rewrite /KeygenUniformXofLeafSpec.frame32768 in hframe.
apply W4u8.wordP => byte hbyte.
rewrite BArray32768.get32d_byte 1://.
rewrite BArray32768.get32d_byte 1://.
have hsame := hframe (4 * word_index + byte) _ _.
+ rewrite /BArray32768.size; smt().
+ rewrite /KeygenUniformXofLeafSpec.in_poly_bytes
           /KeygenUniformXofLeafSpec.uniform_poly_words_i.
  smt().
by have := hsame; smt().
qed.

lemma uniform_decoded_prefix8192_before_frame
    before after prefix_base values current_base :
  0 <= prefix_base =>
  prefix_base + size values <= current_base =>
  current_base + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
    BArray8192.size %/ 4 =>
  KeygenUniformXofLeafSpec.decoded_prefix8192
    before prefix_base values =>
  KeygenUniformXofLeafSpec.frame8192 before after current_base =>
  KeygenUniformXofLeafSpec.decoded_prefix8192
    after prefix_base values.
proof.
rewrite /KeygenUniformXofLeafSpec.decoded_prefix8192.
move=> hbase hbefore hcap hdecoded hframe i hi.
have hsame := uniform_frame8192_get32_before
  before after current_base (prefix_base + i) _ _ hcap hframe.
+ smt().
+ smt().
rewrite hsame.
exact (hdecoded i hi).
qed.

lemma uniform_decoded_prefix32768_before_frame
    before after prefix_base values current_base :
  0 <= prefix_base =>
  prefix_base + size values <= current_base =>
  current_base + KeygenUniformXofLeafSpec.uniform_poly_words_i <=
    BArray32768.size %/ 4 =>
  KeygenUniformXofLeafSpec.decoded_prefix32768
    before prefix_base values =>
  KeygenUniformXofLeafSpec.frame32768 before after current_base =>
  KeygenUniformXofLeafSpec.decoded_prefix32768
    after prefix_base values.
proof.
rewrite /KeygenUniformXofLeafSpec.decoded_prefix32768.
move=> hbase hbefore hcap hdecoded hframe i hi.
have hsame := uniform_frame32768_get32_before
  before after current_base (prefix_base + i) _ _ hcap hframe.
+ smt().
+ smt().
rewrite hsame.
exact (hdecoded i hi).
qed.

lemma caller_uniform_values_lt seed nonce blocks pairs i :
  0 <= i < size (caller_uniform_values seed nonce blocks pairs) =>
  nth 0 (caller_uniform_values seed nonce blocks pairs) i <
    KeygenUniformXofLeafSpec.uniform_q_i.
proof.
move=> hi.
have hm := mem_nth 0 (caller_uniform_values seed nonce blocks pairs) i hi.
rewrite /caller_uniform_values
        /KeygenUniformXofLeafSpec.uniform_accepted mem_filter in hm.
by case: hm.
qed.

lemma uniform_vector_stream8192_empty a seed k m :
  uniform_vector_stream8192 a seed k m 0.
proof. by rewrite /uniform_vector_stream8192; smt(). qed.

lemma uniform_vector_stream8192_extend
    before after seed k m count blocks pairs :
  0 <= count =>
  uniform_vector_words_i (count + 1) <= BArray8192.size %/ 4 =>
  uniform_vector_stream8192 before seed k m count =>
  4 <= blocks =>
  0 <= pairs <=
    blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i =>
  size (caller_uniform_values
    seed (vector_nonce_word k m count) blocks pairs) =
    KeygenUniformXofLeafSpec.uniform_poly_words_i =>
  KeygenUniformXofLeafSpec.decoded_prefix8192
    after (uniform_vector_words_i count)
      (caller_uniform_values
        seed (vector_nonce_word k m count) blocks pairs) =>
  KeygenUniformXofLeafSpec.frame8192
    before after (uniform_vector_words_i count) =>
  uniform_vector_stream8192 after seed k m (count + 1).
proof.
move=> hcount hcap hstream hblocks hpairs hsize hdecoded hframe.
rewrite /uniform_vector_stream8192 in hstream.
rewrite /uniform_vector_stream8192.
move=> slot hslot.
case (slot < count) => hbefore.
+ have hslot_before : 0 <= slot < count by smt().
  case: (hstream slot hslot_before) => prior_blocks prior_pairs hprior.
  case: hprior => hprior_blocks hprior.
  case: hprior => hprior_pairs hprior.
  case: hprior => hprior_size hprior_decoded.
  exists prior_blocks prior_pairs.
  split; first exact hprior_blocks.
  split; first exact hprior_pairs.
  split; first exact hprior_size.
  apply (uniform_decoded_prefix8192_before_frame
    before after (uniform_vector_words_i slot)
    (caller_uniform_values
      seed (vector_nonce_word k m slot) prior_blocks prior_pairs)
    (uniform_vector_words_i count)).
  + rewrite /uniform_vector_words_i
            /KeygenUniformXofLeafSpec.uniform_poly_words_i.
    smt().
  + rewrite hprior_size /uniform_vector_words_i
            /KeygenUniformXofLeafSpec.uniform_poly_words_i.
    smt().
  + rewrite -uniform_vector_words_i_succ.
    exact hcap.
  + exact hprior_decoded.
  exact hframe.
have -> : slot = count by smt().
exists blocks pairs.
split; first exact hblocks.
split; first exact hpairs.
split; first exact hsize.
exact hdecoded.
qed.

lemma uniform_vector_stream8192_range a seed k m count :
  uniform_vector_stream8192 a seed k m count =>
  uniform_vector_range8192 a count.
proof.
rewrite /uniform_vector_stream8192 /uniform_vector_range8192.
move=> hstream slot hslot.
case: (hstream slot hslot) => blocks pairs hslot_stream.
move: hslot_stream =>
  [hblocks [hpairs [hsize hdecoded]]].
rewrite /KeygenUniformXofLeafSpec.bounded_prefix8192.
move=> i hi.
have hi_values :
    0 <= i < size (caller_uniform_values
      seed (vector_nonce_word k m slot) blocks pairs).
+ by rewrite hsize.
rewrite (hdecoded i hi_values).
exact (caller_uniform_values_lt
  seed (vector_nonce_word k m slot) blocks pairs i hi_values).
qed.

lemma uniform_matrix_stream_prefix32768_empty a seed rows cols :
  uniform_matrix_stream_prefix32768 a seed rows cols 0 0.
proof.
by rewrite /uniform_matrix_stream_prefix32768 /matrix_visited; smt().
qed.

lemma uniform_matrix_stream_prefix32768_extend
    before after seed rows cols row col blocks pairs :
  0 <= cols =>
  0 <= row < rows =>
  0 <= col < cols =>
  matrix_base_i cols row col +
    KeygenUniformXofLeafSpec.uniform_poly_words_i <=
    BArray32768.size %/ 4 =>
  uniform_matrix_stream_prefix32768
    before seed rows cols row col =>
  4 <= blocks =>
  0 <= pairs <=
    blocks * KeygenUniformXofLeafSpec.uniform_block_pairs_i =>
  size (caller_uniform_values
    seed (matrix_nonce_word row col) blocks pairs) =
    KeygenUniformXofLeafSpec.uniform_poly_words_i =>
  KeygenUniformXofLeafSpec.decoded_prefix32768
    after (matrix_base_i cols row col)
      (caller_uniform_values
        seed (matrix_nonce_word row col) blocks pairs) =>
  KeygenUniformXofLeafSpec.frame32768
    before after (matrix_base_i cols row col) =>
  uniform_matrix_stream_prefix32768
    after seed rows cols row (col + 1).
proof.
move=> hcols hrow hcol hcap hstream hblocks hpairs hsize
        hdecoded hframe.
rewrite /uniform_matrix_stream_prefix32768 in hstream.
rewrite /uniform_matrix_stream_prefix32768.
move=> prior_row prior_col hvisited.
case (prior_row < row \/
      (prior_row = row /\ prior_col < col)) => hbefore.
+ have hvisited_before :
      matrix_visited rows cols row col prior_row prior_col.
  + rewrite /matrix_visited in hvisited.
    rewrite /matrix_visited.
    smt().
  case: (hstream prior_row prior_col hvisited_before) =>
    prior_blocks prior_pairs hprior.
  move: hprior =>
    [hprior_blocks [hprior_pairs [hprior_size hprior_decoded]]].
  exists prior_blocks prior_pairs.
  split; first exact hprior_blocks.
  split; first exact hprior_pairs.
  split; first exact hprior_size.
  apply (uniform_decoded_prefix32768_before_frame
    before after (matrix_base_i cols prior_row prior_col)
    (caller_uniform_values seed
      (matrix_nonce_word prior_row prior_col) prior_blocks prior_pairs)
    (matrix_base_i cols row col)).
  + rewrite /matrix_base_i /poly_stride_i.
    rewrite /matrix_visited in hvisited.
    smt().
  + rewrite hprior_size.
    apply (matrix_prior_region cols row col prior_row prior_col);
      first exact hcols.
    - by rewrite /matrix_visited in hvisited; smt().
    - exact hcol.
    exact hbefore.
  + exact hcap.
  + exact hprior_decoded.
  exact hframe.
have hcurrent : prior_row = row /\ prior_col = col.
+ rewrite /matrix_visited in hvisited.
  smt().
case: hcurrent => -> ->.
exists blocks pairs.
split; first exact hblocks.
split; first exact hpairs.
split; first exact hsize.
exact hdecoded.
qed.

lemma uniform_matrix_stream_prefix32768_rollover
    a seed rows cols row :
  uniform_matrix_stream_prefix32768 a seed rows cols row cols =>
  uniform_matrix_stream_prefix32768 a seed rows cols (row + 1) 0.
proof.
rewrite /uniform_matrix_stream_prefix32768.
move=> hstream current_row current_col hvisited.
apply hstream.
rewrite /matrix_visited in hvisited.
rewrite /matrix_visited.
by smt().
qed.

lemma uniform_matrix_stream32768_range a seed rows cols :
  uniform_matrix_stream32768 a seed rows cols =>
  uniform_matrix_range32768 a rows cols.
proof.
rewrite /uniform_matrix_stream32768
        /uniform_matrix_stream_prefix32768
        /uniform_matrix_range32768.
move=> hstream row col hrow hcol.
have hvisited : matrix_visited rows cols rows 0 row col.
+ by rewrite /matrix_visited; smt().
case: (hstream row col hvisited) => blocks pairs hcell.
move: hcell => [hblocks [hpairs [hsize hdecoded]]].
rewrite /KeygenUniformXofLeafSpec.bounded_prefix32768.
move=> i hi.
have hi_values :
    0 <= i < size (caller_uniform_values
      seed (matrix_nonce_word row col) blocks pairs).
+ by rewrite hsize.
rewrite (hdecoded i hi_values).
exact (caller_uniform_values_lt
  seed (matrix_nonce_word row col) blocks pairs i hi_values).
qed.

lemma eta_vector_words_i_succ count :
  eta_vector_words_i (count + 1) =
  eta_vector_words_i count + KeygenEtaSamplerSpec.eta_poly_words_i.
proof. by rewrite /eta_vector_words_i; ring. qed.

lemma eta_vector_centered8192_empty a :
  eta_vector_centered8192 a 0.
proof.
rewrite /eta_vector_centered8192 /eta_vector_words_i.
exact (KeygenEtaSamplerSpec.centered_interval8192_empty a 0 0).
qed.

lemma eta_vector_frame8192_empty a : eta_vector_frame8192 a a 0.
proof.
rewrite /eta_vector_frame8192 /eta_vector_words_i.
exact (KeygenEtaSamplerSpec.word_frame8192_refl a 0 0).
qed.

lemma eta_vector_centered8192_extend before after count :
  0 <= count =>
  eta_vector_words_i (count + 1) <= BArray8192.size %/ 4 =>
  eta_vector_centered8192 before count =>
  KeygenEtaSamplerSpec.centered_interval8192
    after (eta_vector_words_i count) 0
    KeygenEtaSamplerSpec.eta_poly_words_i =>
  KeygenEtaSamplerSpec.poly_frame8192
    before after (eta_vector_words_i count) =>
  eta_vector_centered8192 after (count + 1).
proof.
rewrite /eta_vector_centered8192 /eta_vector_words_i
        /KeygenEtaSamplerSpec.eta_poly_words_i
        /KeygenEtaSamplerSpec.centered_interval8192
        /KeygenEtaSamplerSpec.poly_frame8192.
move=> hcount hcap hprefix hcurrent hframe i hi.
case (i < count * 256) => hprefix_i.
+ have heq := hframe i _ _.
  + smt().
  + smt().
  have hp := hprefix i _.
  + smt().
  smt().
+ have h := hcurrent (i - count * 256) _.
  + smt().
  by have := h; smt().
qed.

lemma eta_vector_frame8192_extend original before after count :
  0 <= count =>
  eta_vector_frame8192 original before count =>
  KeygenEtaSamplerSpec.poly_frame8192
    before after (eta_vector_words_i count) =>
  eta_vector_frame8192 original after (count + 1).
proof.
rewrite /eta_vector_frame8192 /eta_vector_words_i
        /KeygenEtaSamplerSpec.eta_poly_words_i
        /KeygenEtaSamplerSpec.word_frame8192
        /KeygenEtaSamplerSpec.poly_frame8192.
move=> hcount hprefix hcurrent i hi hout.
have hcurrent_i := hcurrent i hi _.
+ smt().
rewrite hcurrent_i.
apply hprefix; first exact hi.
by smt().
qed.

lemma eta_decoded_prefix8192_before_poly_frame
    before after prefix_base values current_base :
  0 <= prefix_base =>
  prefix_base + size values <= current_base =>
  current_base + KeygenEtaSamplerSpec.eta_poly_words_i <=
    BArray8192.size %/ 4 =>
  KeygenEtaSamplerSpec.eta_decoded_prefix8192
    before prefix_base values =>
  KeygenEtaSamplerSpec.poly_frame8192 before after current_base =>
  KeygenEtaSamplerSpec.eta_decoded_prefix8192
    after prefix_base values.
proof.
rewrite /KeygenEtaSamplerSpec.eta_decoded_prefix8192
        /KeygenEtaSamplerSpec.poly_frame8192.
move=> hbase hbefore hcap hprefix hframe i hi.
have hsame := hframe (prefix_base + i) _ _.
+ smt().
+ smt().
rewrite hsame.
exact (hprefix i hi).
qed.

lemma eta_vector_stream8192_empty a seed start :
  eta_vector_stream8192 a seed start 0.
proof. by rewrite /eta_vector_stream8192; smt(). qed.

lemma eta_vector_stream8192_extend
    before after seed start count blocks :
  0 <= count =>
  eta_vector_words_i (count + 1) <= BArray8192.size %/ 4 =>
  eta_vector_stream8192 before seed start count =>
  1 <= blocks =>
  size (caller_eta_values seed start count blocks) =
    KeygenEtaSamplerSpec.eta_poly_words_i =>
  KeygenEtaSamplerSpec.eta_decoded_prefix8192
    after (eta_vector_words_i count)
      (caller_eta_values seed start count blocks) =>
  KeygenEtaSamplerSpec.poly_frame8192
    before after (eta_vector_words_i count) =>
  eta_vector_stream8192 after seed start (count + 1).
proof.
move=> hcount hcap hstream hblocks hsize hdecoded hframe.
rewrite /eta_vector_stream8192 in hstream.
rewrite /eta_vector_stream8192.
move=> slot hslot.
case (slot < count) => hbefore.
+ have hslot_before : 0 <= slot < count by smt().
  case: (hstream slot hslot_before) => prior_blocks hprior.
  case: hprior => hprior_blocks hprior.
  case: hprior => hprior_size hprior_decoded.
  exists prior_blocks.
  split; first exact hprior_blocks.
  split; first exact hprior_size.
  apply (eta_decoded_prefix8192_before_poly_frame
    before after (eta_vector_words_i slot)
    (caller_eta_values seed start slot prior_blocks)
    (eta_vector_words_i count)).
  + rewrite /eta_vector_words_i /KeygenEtaSamplerSpec.eta_poly_words_i.
    smt().
  + rewrite hprior_size /eta_vector_words_i
            /KeygenEtaSamplerSpec.eta_poly_words_i.
    smt().
  + rewrite -eta_vector_words_i_succ.
    exact hcap.
  + exact hprior_decoded.
  exact hframe.
have -> : slot = count by smt().
exists blocks.
by do split.
qed.

lemma low16_lt_w64_modulus : 65536 < W64.modulus.
proof. by []. qed.

lemma w64_counter_guard i bound :
  0 <= i <= W64.to_uint bound =>
  (W64.of_int i \ult bound) = (i < W64.to_uint bound).
proof.
move=> hi.
rewrite W64.ultE W64.to_uint_small.
+ by smt(W64.to_uint_cmp).
by [].
qed.

lemma w64_counter_next i :
  W64.of_int i + W64.of_int 1 = W64.of_int (i + 1).
proof. by rewrite -W64.of_intD. qed.

lemma rowbase_word_next cols i :
  W64.of_int (i * W64.to_uint cols) + cols =
  W64.of_int ((i + 1) * W64.to_uint cols).
proof.
rewrite -(W64.to_uintK' cols) -W64.of_intD.
by congr; ring.
qed.

lemma matrix_nonce_wordE i j :
  matrix_nonce_word i j =
  (W64.of_int i `<<` (W8.of_int 8)) + W64.of_int j.
proof.
rewrite /matrix_nonce_word /matrix_nonce_i W64.shl_shlw 1:/#
        W64.shlMP 1:/# -W64.of_intD.
by congr; ring.
qed.

lemma matrix_base_wordE cols i j :
  matrix_base_word cols i j =
  (W64.of_int (i * cols) + W64.of_int j) * W64.of_int 256.
proof.
rewrite /matrix_base_word /matrix_base_i /poly_stride_i
        -W64.of_intD W64.of_intM.
by [].
qed.

lemma vector_nonce_wordE k m i :
  vector_nonce_word k m i =
  ((W64.of_int k `<<` (W8.of_int 8)) + W64.of_int m) + W64.of_int i.
proof.
rewrite /vector_nonce_word /vector_nonce_i W64.shl_shlw 1:/#
        W64.shlMP 1:/# -!W64.of_intD.
by congr; ring.
qed.

lemma linear_base_word_zero : linear_base_word 0 = W64.of_int 0.
proof. by rewrite /linear_base_word /linear_base_i /poly_stride_i. qed.

lemma linear_base_word_next i :
  linear_base_word (i + 1) = linear_base_word i + W64.of_int 256.
proof.
rewrite /linear_base_word /linear_base_i /poly_stride_i.
rewrite -W64.of_intD.
by congr; ring.
qed.

lemma vector_nonce_word_next k m i :
  vector_nonce_word k m (i + 1) =
  vector_nonce_word k m i + W64.of_int 1.
proof.
rewrite /vector_nonce_word /vector_nonce_i -W64.of_intD.
by congr; ring.
qed.

lemma vector_nonce_word_zero_words k m :
  vector_nonce_word (W64.to_uint k) (W64.to_uint m) 0 =
  (k `<<` (W8.of_int 8)) + m.
proof.
rewrite vector_nonce_wordE !W64.to_uintK'.
by rewrite W64.addr0_s.
qed.

lemma eta_nonce_word_zero start : eta_nonce_word start 0 = start.
proof. by rewrite /eta_nonce_word W64.addr0_s. qed.

lemma eta_nonce_word_next start i :
  eta_nonce_word start (i + 1) = eta_nonce_word start i + W64.of_int 1.
proof.
rewrite /eta_nonce_word W64.of_intD.
by ring.
qed.

lemma eta_nonce_word_shift start offset slot :
  eta_nonce_word (eta_nonce_word start offset) slot =
  eta_nonce_word start (offset + slot).
proof.
rewrite /eta_nonce_word W64.of_intD.
by ring.
qed.

lemma encoded_to_uint n :
  0 <= n < W64.modulus => W64.to_uint (W64.of_int n) = n.
proof. by apply W64.to_uint_small. qed.

lemma low16_encoded n :
  0 <= n < 65536 => nonce_low16 (W64.of_int n) = n.
proof.
move=> hn.
rewrite /nonce_low16 W64.to_uint_small 1:/#.
by rewrite modz_small.
qed.

lemma low16_encoded_mod n :
  0 <= n < W64.modulus =>
  nonce_low16 (W64.of_int n) = n %% 65536.
proof. by move=> hn; rewrite /nonce_low16 W64.to_uint_small. qed.

lemma mode2_matrix_nonce_bounds i j :
  0 <= i < mode2_k_i =>
  0 <= j < mode2_m_i =>
  0 <= matrix_nonce_i i j < 65536.
proof. by rewrite /matrix_nonce_i /mode2_k_i /mode2_m_i; smt(). qed.

lemma mode2_matrix_nonce_no_wrap i j :
  0 <= i < mode2_k_i =>
  0 <= j < mode2_m_i =>
  matrix_nonce_i i j < W64.modulus.
proof.
move=> hi hj.
have h := mode2_matrix_nonce_bounds i j hi hj.
by smt(low16_lt_w64_modulus).
qed.

lemma mode2_matrix_nonce_low16 i j :
  0 <= i < mode2_k_i =>
  0 <= j < mode2_m_i =>
  nonce_low16 (matrix_nonce_word i j) = matrix_nonce_i i j.
proof.
move=> hi hj.
rewrite /matrix_nonce_word.
by apply low16_encoded; apply mode2_matrix_nonce_bounds.
qed.

lemma mode2_matrix_address_bounds i j :
  0 <= i < mode2_k_i =>
  0 <= j < mode2_m_i =>
  0 <= matrix_base_i mode2_m_i i j /\
  matrix_base_i mode2_m_i i j + 256 <= 1536.
proof.
by rewrite /matrix_base_i /poly_stride_i /mode2_k_i /mode2_m_i; smt().
qed.

lemma mode2_matrix_regions_disjoint i j i' j' :
  0 <= i < mode2_k_i =>
  0 <= j < mode2_m_i =>
  0 <= i' < mode2_k_i =>
  0 <= j' < mode2_m_i =>
  (i <> i' \/ j <> j') =>
  matrix_base_i mode2_m_i i j + 256 <=
    matrix_base_i mode2_m_i i' j' \/
  matrix_base_i mode2_m_i i' j' + 256 <=
    matrix_base_i mode2_m_i i j.
proof.
rewrite /matrix_base_i /poly_stride_i /mode2_k_i /mode2_m_i.
by smt().
qed.

lemma mode2_vector_nonce_bounds i :
  0 <= i < mode2_k_i =>
  0 <= vector_nonce_i mode2_k_i mode2_m_i i < 65536.
proof.
by rewrite /vector_nonce_i /mode2_k_i /mode2_m_i; smt().
qed.

lemma mode2_vector_nonce_no_wrap i :
  0 <= i < mode2_k_i =>
  vector_nonce_i mode2_k_i mode2_m_i i < W64.modulus.
proof.
move=> hi.
have h := mode2_vector_nonce_bounds i hi.
by smt(low16_lt_w64_modulus).
qed.

lemma mode2_vector_nonce_low16 i :
  0 <= i < mode2_k_i =>
  nonce_low16 (vector_nonce_word mode2_k_i mode2_m_i i) =
    vector_nonce_i mode2_k_i mode2_m_i i.
proof.
move=> hi.
rewrite /vector_nonce_word.
by apply low16_encoded; apply mode2_vector_nonce_bounds.
qed.

lemma caller_uniform_seed_input_prefix seed nonce p :
  0 <= p < 32 =>
  nth 0
    (KeygenShakeStreamSpec.shake128_seed_nonce_input
      seed (W64.of_int uniform_seed_offset_i) nonce) p =
  W8.to_uint (BArray128.get8 seed p).
proof.
move=> hp.
rewrite /KeygenShakeStreamSpec.shake128_seed_nonce_input.
rewrite KeygenShakeStreamSpec.seed_nonce_input_nth 1:/# 1:/#.
rewrite (_ : p < 32) 1:/# /=.
by rewrite /uniform_seed_offset_i W64.to_uint_small 1:/# /=.
qed.

lemma mode2_matrix_uniform_nonce_input_tail seed row col :
  0 <= row < mode2_k_i =>
  0 <= col < mode2_m_i =>
  nth 0
    (KeygenShakeStreamSpec.shake128_seed_nonce_input
      seed (W64.of_int uniform_seed_offset_i)
        (matrix_nonce_word row col)) 32 = col /\
  nth 0
    (KeygenShakeStreamSpec.shake128_seed_nonce_input
      seed (W64.of_int uniform_seed_offset_i)
        (matrix_nonce_word row col)) 33 = row.
proof.
move=> hrow hcol.
have hnonce :
    W64.to_uint (matrix_nonce_word row col) = matrix_nonce_i row col.
+ rewrite /matrix_nonce_word.
  apply encoded_to_uint.
  have hb := mode2_matrix_nonce_bounds row col hrow hcol.
  by smt(low16_lt_w64_modulus).
split.
+ rewrite /KeygenShakeStreamSpec.shake128_seed_nonce_input.
  rewrite KeygenShakeStreamSpec.seed_nonce_input_nth 1:/# 1:/# /= hnonce.
  rewrite /matrix_nonce_i (mulzC 256 row) modzMDl modz_small 1:/#.
  by [].
+ rewrite /KeygenShakeStreamSpec.shake128_seed_nonce_input.
  rewrite KeygenShakeStreamSpec.seed_nonce_input_nth 1:/# 1:/# /= hnonce.
  rewrite /matrix_nonce_i (mulzC 256 row)
          divzMDl 1:/# divz_small 1:/#
          modz_small 1:/#.
  by [].
qed.

lemma mode2_vector_uniform_nonce_input_tail seed slot :
  0 <= slot < mode2_k_i =>
  nth 0
    (KeygenShakeStreamSpec.shake128_seed_nonce_input
      seed (W64.of_int uniform_seed_offset_i)
        (vector_nonce_word mode2_k_i mode2_m_i slot)) 32 =
    mode2_m_i + slot /\
  nth 0
    (KeygenShakeStreamSpec.shake128_seed_nonce_input
      seed (W64.of_int uniform_seed_offset_i)
        (vector_nonce_word mode2_k_i mode2_m_i slot)) 33 =
    mode2_k_i.
proof.
move=> hslot.
have hnonce :
    W64.to_uint (vector_nonce_word mode2_k_i mode2_m_i slot) =
    vector_nonce_i mode2_k_i mode2_m_i slot.
+ rewrite /vector_nonce_word.
  apply encoded_to_uint.
  have hb := mode2_vector_nonce_bounds slot hslot.
  by smt(low16_lt_w64_modulus).
have hnonce_shape :
    vector_nonce_i mode2_k_i mode2_m_i slot =
    2 * 256 + (3 + slot).
+ by rewrite /vector_nonce_i /mode2_k_i /mode2_m_i; ring.
split.
+ rewrite /KeygenShakeStreamSpec.shake128_seed_nonce_input.
  rewrite KeygenShakeStreamSpec.seed_nonce_input_nth 1:/# 1:/# /= hnonce.
  rewrite hnonce_shape modzMDl modz_small 1:/#.
  by [].
+ rewrite /KeygenShakeStreamSpec.shake128_seed_nonce_input.
  rewrite KeygenShakeStreamSpec.seed_nonce_input_nth 1:/# 1:/# /= hnonce.
  rewrite hnonce_shape divzMDl 1:/# divz_small 1:/# modz_small 1:/#.
  by [].
qed.

lemma mode2_linear_address_bounds i :
  0 <= i < mode2_m_i =>
  0 <= linear_base_i i /\ linear_base_i i + 256 <= 768.
proof. by rewrite /linear_base_i /poly_stride_i /mode2_m_i; smt(). qed.

lemma mode2_linear_regions_disjoint i j :
  0 <= i < mode2_m_i =>
  0 <= j < mode2_m_i =>
  i <> j =>
  linear_base_i i + 256 <= linear_base_i j \/
  linear_base_i j + 256 <= linear_base_i i.
proof. by rewrite /linear_base_i /poly_stride_i /mode2_m_i; smt(). qed.

lemma matrix_capacity rows cols i j :
  0 <= rows =>
  0 <= cols =>
  rows * cols <= 32 =>
  0 <= i < rows =>
  0 <= j < cols =>
  0 <= matrix_base_i cols i j /\
  matrix_base_i cols i j + 255 < 8192.
proof.
rewrite /matrix_base_i /poly_stride_i.
by smt().
qed.

lemma linear_capacity count i :
  0 <= count <= 8 =>
  0 <= i < count =>
  0 <= linear_base_i i /\ linear_base_i i + 255 < 2048.
proof. by rewrite /linear_base_i /poly_stride_i; smt(). qed.

lemma stride_regions_disjoint i j :
  0 <= i =>
  0 <= j =>
  i <> j =>
  linear_base_i i + 256 <= linear_base_i j \/
  linear_base_i j + 256 <= linear_base_i i.
proof. by rewrite /linear_base_i /poly_stride_i; smt(). qed.

lemma mode2_eta_nonce_bounds retry slot :
  0 <= retry =>
  0 <= slot < mode2_retry_span_i =>
  mode2_eta_nonce_i retry slot < 65536 =>
  0 <= mode2_eta_nonce_i retry slot < W64.modulus.
proof.
move=> hr hs hn.
split.
+ by rewrite /mode2_eta_nonce_i /mode2_retry_counter_i
             /mode2_retry_span_i /mode2_k_i /mode2_m_i; smt().
by smt(low16_lt_w64_modulus).
qed.

lemma mode2_eta_nonce_low16 retry slot :
  0 <= retry =>
  0 <= slot < mode2_retry_span_i =>
  mode2_eta_nonce_i retry slot < W64.modulus =>
  nonce_low16 (W64.of_int (mode2_eta_nonce_i retry slot)) =
    mode2_eta_nonce_i retry slot %% 65536.
proof.
move=> hr hs hn.
apply low16_encoded_mod.
rewrite /mode2_eta_nonce_i /mode2_retry_counter_i
        /mode2_retry_span_i /mode2_k_i /mode2_m_i.
by smt().
qed.

lemma mode2_matrix_nonce_schedule :
  matrix_nonce_i 0 0 = 0 /\ matrix_nonce_i 0 1 = 1 /\
  matrix_nonce_i 0 2 = 2 /\ matrix_nonce_i 1 0 = 256 /\
  matrix_nonce_i 1 1 = 257 /\ matrix_nonce_i 1 2 = 258.
proof. by []. qed.

lemma mode2_matrix_base_schedule :
  matrix_base_i 3 0 0 = 0 /\ matrix_base_i 3 0 1 = 256 /\
  matrix_base_i 3 0 2 = 512 /\ matrix_base_i 3 1 0 = 768 /\
  matrix_base_i 3 1 1 = 1024 /\ matrix_base_i 3 1 2 = 1280.
proof. by []. qed.

lemma mode2_vector_schedule :
  vector_nonce_i 2 3 0 = 515 /\ vector_nonce_i 2 3 1 = 516 /\
  linear_base_i 0 = 0 /\ linear_base_i 1 = 256.
proof. by []. qed.

lemma mode2_eta_retry_schedule retry :
  mode2_eta_nonce_i retry 0 = 5 * retry /\
  mode2_eta_nonce_i retry 1 = 5 * retry + 1 /\
  mode2_eta_nonce_i retry 2 = 5 * retry + 2 /\
  mode2_eta_nonce_i retry 3 = 5 * retry + 3 /\
  mode2_eta_nonce_i retry 4 = 5 * retry + 4.
proof.
rewrite /mode2_eta_nonce_i /mode2_retry_counter_i
        /mode2_retry_span_i /mode2_k_i /mode2_m_i.
split; first by ring.
split; first by ring.
split; first by ring.
split; first by ring.
by ring.
qed.

lemma mode2_eta_nonce_wordE retry slot :
  eta_nonce_word (W64.of_int (mode2_retry_counter_i retry)) slot =
  W64.of_int (mode2_eta_nonce_i retry slot).
proof.
rewrite /eta_nonce_word /mode2_eta_nonce_i -W64.of_intD.
by congr.
qed.

lemma mode2_eta_nonce_split start :
  eta_nonce_word (eta_nonce_word start mode2_m_i) mode2_k_i =
  eta_nonce_word start mode2_retry_span_i.
proof.
rewrite eta_nonce_word_shift
        /mode2_retry_span_i /mode2_k_i /mode2_m_i.
by congr.
qed.

module CallerSpec = {
  proc expand_matA (matp:BArray32768.t, seedp:BArray128.t,
                    rows:W64.t, cols:W64.t) : BArray32768.t = {
    var i:int;
    var j:int;

    i <- 0;
    while (i < W64.to_uint rows) {
      j <- 0;
      while (j < W64.to_uint cols) {
        matp <@ KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_8192
          (matp, matrix_base_word (W64.to_uint cols) i j, seedp,
           W64.of_int uniform_seed_offset_i, matrix_nonce_word i j);
        j <- j + 1;
      }
      i <- i + 1;
    }
    return matp;
  }

  proc expand_vecA (vp:BArray8192.t, seedp:BArray128.t,
                    k:W64.t, m:W64.t) : BArray8192.t = {
    var i:int;

    i <- 0;
    while (i < W64.to_uint k) {
      vp <@ KeygenSamplerCallersTarget.M._kp_poly_uniform_at_seedbuf_2048
        (vp, linear_base_word i, seedp, W64.of_int uniform_seed_offset_i,
         vector_nonce_word (W64.to_uint k) (W64.to_uint m) i);
      i <- i + 1;
    }
    return vp;
  }

  proc expand_eta (vp:BArray8192.t, seedp:BArray128.t,
                   nonce:W64.t, count:W64.t) : BArray8192.t = {
    var start:W64.t;
    var i:int;

    start <- nonce;
    i <- 0;
    while (i < W64.to_uint count) {
      vp <@ KeygenSamplerCallersTarget.M._kp_poly_uniform_eta_at_seedbuf_2048
        (vp, linear_base_word i, seedp, W64.of_int eta_seed_offset_i,
         eta_nonce_word start i);
      i <- i + 1;
    }
    return vp;
  }
}.

end KeygenSamplerCallersSpec.
