require import AllCore IntDiv Ring StdOrder Real.

from Jasmin require import JModel_x86.

import RField RealOrder.

require import BArray2048.
require import
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTBounds
  KeygenM23SingularFFTKPrefixBridge
  KeygenM23SingularFFTBlockPrefixBridge
  KeygenM23SingularFFTStageBridge.

import KeygenM23SingularFFTInitBridge.
import KeygenM23SingularFFTBounds.
import KeygenM23SingularFFTKPrefixBridge.
import KeygenM23SingularFFTBlockPrefixBridge.
import KeygenM23SingularFFTStageBridge.

theory KeygenM23SingularFFTStageBounds.

lemma fft_stage_schedule_prefix
    (m md2 stride : W64.t) (processed : int) :
  fft_stage_schedule m md2 stride =>
  0 <= processed <= KeygenM23SingularFFTSpec.fft_block_count m =>
  fft_blocks_schedule_wf m md2 stride processed.
proof.
rewrite /fft_stage_schedule /fft_blocks_schedule_wf.
rewrite /KeygenM23SingularFFTSpec.fft_block_count.
smt(W64.to_uint_cmp).
qed.

lemma fft_blocks_prefix_decode_at_pending
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (processed j : int) :
  fft_stage_schedule m md2 stride =>
  0 <= j < 256 =>
  0 <= processed <= fft_stage_owner_block m j =>
  fft_blocks_prefix_decode_at data roots m md2 stride processed j =
  fft_decode_at data j.
proof.
move=> hstage hj hprocessed.
have hgeneral :
  forall p, 0 <= p =>
    p <= fft_stage_owner_block m j =>
    fft_blocks_prefix_decode_at data roots m md2 stride p j =
    fft_decode_at data j.
+ apply intind.
  + move=> _.
    exact (fft_blocks_prefix_decode_at0 data roots m md2 stride j).
  + move=> p hp0 ih hpowner.
    have hproc_lt : p < KeygenM23SingularFFTSpec.fft_block_count m.
    + have [_ hownerlt] :=
        fft_stage_owner_block_range m md2 stride j hstage hj.
      smt().
    have houtside :
      ! fft_block_range m p j.
    + apply
        (fft_stage_owner_block_outside
          m md2 stride p j hstage hj).
      + split; smt().
      smt().
    rewrite
      (fft_blocks_prefix_decode_at_frameS
        data roots m md2 stride p j hp0 houtside).
    apply ih.
    smt().
move: hprocessed => [hprocessed0 hprocessed_owner].
exact (hgeneral processed hprocessed0 hprocessed_owner).
qed.

lemma fft_blocks_prefix_pending_decode
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (processed j : int) :
  fft_stage_schedule m md2 stride =>
  0 <= j < 256 =>
  0 <= processed <= fft_stage_owner_block m j =>
  fft_blocks_prefix_safe data roots m md2 stride processed =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride processed)
    j =
  fft_decode_at data j.
proof.
move=> hstage hj hprocessed hsafe.
have hwf :=
  fft_stage_schedule_prefix m md2 stride processed hstage _.
+ have [_ hownerlt] :=
    fft_stage_owner_block_range m md2 stride j hstage hj.
  smt().
rewrite
  (fft_blocks_prefix_decode
    data roots m md2 stride processed j
    hwf hj hsafe).
exact
  (fft_blocks_prefix_decode_at_pending
    data roots m md2 stride processed j
    hstage hj hprocessed).
qed.

lemma fft_stage_current_block_even_range
    (m md2 stride : W64.t) (block k : int) :
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  0 <= k < W64.to_uint md2 =>
  fft_block_range m block
    (fft_k_even_index (fft_block_start_word m block) k).
proof.
move=> hstage hblock hk.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
have [hstart0 hend] :=
  fft_block_start_bounds
    m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    block hwf hblock.
have hstartw :
  W64.to_uint (fft_block_start_word m block) = fft_block_start m block.
+ apply (fft_block_start_word_uint m block).
  smt().
rewrite /fft_block_range /fft_block_end /fft_k_even_index.
rewrite hstartw.
move: hwf.
rewrite /fft_blocks_schedule_wf.
smt(W64.to_uint_cmp).
qed.

lemma fft_stage_current_block_odd_range
    (m md2 stride : W64.t) (block k : int) :
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  0 <= k < W64.to_uint md2 =>
  fft_block_range m block
    (fft_k_odd_index (fft_block_start_word m block) md2 k).
proof.
move=> hstage hblock hk.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
have [hstart0 hend] :=
  fft_block_start_bounds
    m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    block hwf hblock.
have hstartw :
  W64.to_uint (fft_block_start_word m block) = fft_block_start m block.
+ apply (fft_block_start_word_uint m block).
  smt().
rewrite /fft_block_range /fft_block_end /fft_k_odd_index /fft_k_even_index.
rewrite hstartw.
move: hwf.
rewrite /fft_blocks_schedule_wf.
smt(W64.to_uint_cmp).
qed.

lemma fft_blocks_prefix_current_block_input_bound
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (block bound : int) :
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  0 <= bound =>
  fft_word_bound data bound =>
  fft_blocks_prefix_safe data roots m md2 stride block =>
  fft_k_input_word_bound
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    (fft_block_start_word m block)
    md2 stride
    (W64.to_uint md2)
    bound.
proof.
move=> hstage hblock hbound0 hdata hsafe.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
have hwfk :=
  fft_blocks_schedule_wf_local
    m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    block hwf hblock.
rewrite /fft_k_input_word_bound.
move=> k hk.
have heven_idx :=
  fft_k_even_index_bounds
    (fft_block_start_word m block) md2 stride
    (W64.to_uint md2) k hwfk hk.
have hodd_idx :=
  fft_k_odd_index_bounds
    (fft_block_start_word m block) md2 stride
    (W64.to_uint md2) k hwfk hk.
have heven_range :=
  fft_stage_current_block_even_range
    m md2 stride block k hstage hblock hk.
have hodd_range :=
  fft_stage_current_block_odd_range
    m md2 stride block k hstage hblock hk.
have heven_owner :
  fft_stage_owner_block
    m
    (fft_k_even_index (fft_block_start_word m block) k) = block.
+ apply eq_sym.
  apply
    (fft_stage_owner_block_unique
      m md2 stride
      block
      (fft_k_even_index (fft_block_start_word m block) k)
      hstage heven_idx hblock heven_range).
have hodd_owner :
  fft_stage_owner_block
    m
    (fft_k_odd_index (fft_block_start_word m block) md2 k) = block.
+ apply eq_sym.
  apply
    (fft_stage_owner_block_unique
      m md2 stride
      block
      (fft_k_odd_index (fft_block_start_word m block) md2 k)
      hstage hodd_idx hblock hodd_range).
have heven_decode :=
  fft_blocks_prefix_pending_decode
    data roots m md2 stride block
    (fft_k_even_index (fft_block_start_word m block) k)
    hstage heven_idx _ hsafe.
+ rewrite heven_owner; smt().
have hodd_decode :=
  fft_blocks_prefix_pending_decode
    data roots m md2 stride block
    (fft_k_odd_index (fft_block_start_word m block) md2 k)
    hstage hodd_idx _ hsafe.
+ rewrite hodd_owner; smt().
have [heven_r heven_i] :=
  fft_decode_at_eq_to_sint
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    data
    (fft_k_even_index (fft_block_start_word m block) k)
    heven_decode.
have [hodd_r hodd_i] :=
  fft_decode_at_eq_to_sint
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    data
    (fft_k_odd_index (fft_block_start_word m block) md2 k)
    hodd_decode.
have [hbase_even_r hbase_even_i] :=
  hdata _ heven_idx.
have [hbase_odd_r hbase_odd_i] :=
  hdata _ hodd_idx.
split.
+ rewrite /fft_word_bound_at heven_r heven_i.
  split; exact hbase_even_r || exact hbase_even_i.
rewrite /fft_word_bound_at hodd_r hodd_i.
split; exact hbase_odd_r || exact hbase_odd_i.
qed.

lemma fft_blocks_prefix_safe_bound
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (processed bound : int) :
  fft_stage_schedule m md2 stride =>
  0 <= processed <= KeygenM23SingularFFTSpec.fft_block_count m =>
  0 <= bound <= 286654464 =>
  fft_word_bound data bound =>
  fft_root_word_bound roots =>
  fft_blocks_prefix_safe data roots m md2 stride processed /\
  fft_word_bound
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride processed)
    (3 * bound).
proof.
move=> hstage hprocessed [hbound0 hboundmax] hdata hroots.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
have hbound_pair : 0 <= bound <= 286654464 by smt().
have hglobal0 :
  fft_word_bound data (3 * bound).
+ apply (fft_word_bound_mono data bound (3 * bound)).
  + smt().
  exact hdata.
have hgeneral :
  forall p, 0 <= p =>
    p <= KeygenM23SingularFFTSpec.fft_block_count m =>
    fft_blocks_prefix_safe data roots m md2 stride p /\
    fft_word_bound
      (KeygenM23SingularFFTSpec.fft_blocks_prefix
        data roots m md2 stride p)
      (3 * bound).
+ apply intind.
  + move=> _.
    split.
    + rewrite /fft_blocks_prefix_safe.
      move=> block hblock.
      smt().
    by rewrite KeygenM23SingularFFTSpec.fft_blocks_prefix0.
  + move=> p hp0 ih hpcountS.
    have hpcount : p < KeygenM23SingularFFTSpec.fft_block_count m by smt().
    have [hsafeP hboundP] := ih _.
    + smt().
    have hblock : 0 <= p < KeygenM23SingularFFTSpec.fft_block_count m by smt().
    have hlocal :=
      fft_blocks_prefix_current_block_input_bound
        data roots m md2 stride p bound
        hstage hblock hbound0 hdata hsafeP.
    have hwfk :=
      fft_blocks_schedule_wf_local
        m md2 stride
        (KeygenM23SingularFFTSpec.fft_block_count m)
        p hwf hblock.
    have hstep :=
      fft_k_prefix_safe_bound
        (KeygenM23SingularFFTSpec.fft_blocks_prefix
          data roots m md2 stride p)
        roots
        (fft_block_start_word m p)
        md2 stride
        (W64.to_uint md2)
        bound
        (3 * bound)
        hwfk hbound_pair _ hboundP hlocal hroots.
    + smt().
    move: hstep => [hsafeStep hboundStep].
    split.
    + rewrite /fft_blocks_prefix_safe.
      move=> block [hblock0 hblockS].
      case (block < p) => hlt.
      + have hblockP : 0 <= block < p by smt().
        exact (hsafeP block hblockP).
      have -> : block = p by smt().
      exact hsafeStep.
    rewrite KeygenM23SingularFFTSpec.fft_blocks_prefixS 1:hp0.
    rewrite fft_block_step_prefixE.
    exact hboundStep.
move: hprocessed => [hprocessed0 hprocessed_count].
exact (hgeneral processed hprocessed0 hprocessed_count).
qed.

lemma fft_stage_safe_bound
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (bound : int) :
  fft_stage_schedule m md2 stride =>
  0 <= bound <= 286654464 =>
  fft_word_bound data bound =>
  fft_root_word_bound roots =>
  fft_stage_safe data roots m md2 stride /\
  fft_word_bound
    (KeygenM23SingularFFTSpec.fft_stage data roots m md2 stride)
    (3 * bound).
proof.
move=> hstage hbound hdata hroots.
have [hsafe hbound_out] :=
  fft_blocks_prefix_safe_bound
    data roots m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    bound hstage _ hbound hdata hroots.
+ have [_ hmul] : fft_stage_schedule m md2 stride by exact hstage.
  smt().
split.
+ exact hsafe.
rewrite /KeygenM23SingularFFTSpec.fft_stage.
exact hbound_out.
qed.

lemma fft_stage_safe_bound_reachable
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (bound : int) :
  fft_stage_reachable_params m md2 stride =>
  0 <= bound <= 286654464 =>
  fft_word_bound data bound =>
  fft_root_word_bound roots =>
  fft_stage_safe data roots m md2 stride /\
  fft_word_bound
    (KeygenM23SingularFFTSpec.fft_stage data roots m md2 stride)
    (3 * bound).
proof.
move=> hreach hbound hdata hroots.
exact
  (fft_stage_safe_bound
    data roots m md2 stride bound
    (fft_stage_reachable_schedule m md2 stride hreach)
    hbound hdata hroots).
qed.

end KeygenM23SingularFFTStageBounds.
