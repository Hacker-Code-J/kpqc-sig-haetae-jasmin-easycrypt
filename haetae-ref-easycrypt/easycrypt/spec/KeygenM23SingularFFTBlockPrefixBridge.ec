require import AllCore IntDiv List Ring StdOrder Real.

from Jasmin require import JModel_x86.

import RField RealOrder.

require import BArray2048.
require import
  KeygenM23ComplexReal
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTKPrefixBridge.

import KeygenM23ComplexReal.
import KeygenM23SingularFFTInitBridge.
import KeygenM23SingularFFTKPrefixBridge.

theory KeygenM23SingularFFTBlockPrefixBridge.

op fft_block_start (m : W64.t) (block : int) : int =
  block * W64.to_uint m.

op fft_block_end (m : W64.t) (block : int) : int =
  fft_block_start m block + W64.to_uint m.

op fft_block_start_word (m : W64.t) (block : int) : W64.t =
  W64.of_int block * m.

op fft_block_range (m : W64.t) (block j : int) : bool =
  fft_block_start m block <= j < fft_block_end m block.

op fft_blocks_schedule_wf (m md2 stride : W64.t) (processed : int) : bool =
  0 <= processed /\
  0 < W64.to_uint m /\
  W64.to_uint m = 2 * W64.to_uint md2 /\
  processed * W64.to_uint m <= 256 /\
  (forall k, 0 <= k < W64.to_uint md2 =>
    k * W64.to_uint stride < 256).

op fft_blocks_prefix_safe
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (processed : int) : bool =
  forall block, 0 <= block < processed =>
    fft_k_prefix_safe
      (KeygenM23SingularFFTSpec.fft_blocks_prefix
        data roots m md2 stride block)
      roots
      (fft_block_start_word m block)
      md2 stride
      (W64.to_uint md2).

op fft_blocks_decode_step
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (j : int) (current : complex) (block : int) : complex =
  if fft_block_range m block j
  then
    fft_k_prefix_decode_at
      (KeygenM23SingularFFTSpec.fft_blocks_prefix
        data roots m md2 stride block)
      roots
      (fft_block_start_word m block)
      md2 stride
      (W64.to_uint md2)
      j
  else current.

op fft_blocks_prefix_decode_at
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (processed j : int) : complex =
  foldl (fft_blocks_decode_step data roots m md2 stride j)
    (fft_decode_at data j)
    (iota_ 0 processed).

lemma fft_block_start_wordE (m : W64.t) (block : int) :
  fft_block_start_word m block = W64.of_int (fft_block_start m block).
proof.
rewrite /fft_block_start_word /fft_block_start.
by rewrite -(W64.to_uintK' m) W64.of_intM'.
qed.

lemma fft_block_start_word_uint (m : W64.t) (block : int) :
  0 <= fft_block_start m block < W64.modulus =>
  W64.to_uint (fft_block_start_word m block) = fft_block_start m block.
proof.
move=> hstart.
rewrite fft_block_start_wordE.
by apply W64.to_uint_small.
qed.

lemma fft_blocks_schedule_wf_stage0 :
  fft_blocks_schedule_wf
    (W64.of_int 2) (W64.of_int 1) (W64.of_int 256) 128.
proof.
rewrite /fft_blocks_schedule_wf.
have hm : W64.to_uint (W64.of_int 2) = 2 by
  rewrite W64.to_uint_small 1:/#.
have hmd2 : W64.to_uint (W64.of_int 1) = 1 by
  rewrite W64.to_uint_small 1:/#.
have hstride : W64.to_uint (W64.of_int 256) = 256 by
  rewrite W64.to_uint_small 1:/#.
rewrite hm hmd2 hstride.
smt().
qed.

lemma fft_blocks_schedule_wf_prev
    (m md2 stride : W64.t) (processed : int) :
  0 <= processed =>
  fft_blocks_schedule_wf m md2 stride (processed + 1) =>
  fft_blocks_schedule_wf m md2 stride processed.
proof.
rewrite /fft_blocks_schedule_wf.
smt().
qed.

lemma fft_blocks_prefix_safe_prev
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (processed : int) :
  0 <= processed =>
  fft_blocks_prefix_safe data roots m md2 stride (processed + 1) =>
  fft_blocks_prefix_safe data roots m md2 stride processed.
proof.
rewrite /fft_blocks_prefix_safe.
smt().
qed.

lemma fft_block_start_bounds
    (m md2 stride : W64.t) (processed block : int) :
  fft_blocks_schedule_wf m md2 stride processed =>
  0 <= block < processed =>
  0 <= fft_block_start m block /\
  fft_block_end m block <= 256.
proof.
rewrite /fft_blocks_schedule_wf /fft_block_start /fft_block_end.
smt(W64.to_uint_cmp).
qed.

lemma fft_blocks_schedule_wf_local
    (m md2 stride : W64.t) (processed block : int) :
  fft_blocks_schedule_wf m md2 stride processed =>
  0 <= block < processed =>
  fft_k_schedule_wf
    (fft_block_start_word m block)
    md2 stride
    (W64.to_uint md2).
proof.
move=> hwf hblock.
have hwf0 := hwf.
have [hstart0 hend] :=
  fft_block_start_bounds m md2 stride processed block hwf0 hblock.
have hmpos : 0 < W64.to_uint m by
  move: hwf; rewrite /fft_blocks_schedule_wf; smt().
have hm : W64.to_uint m = 2 * W64.to_uint md2 by
  move: hwf; rewrite /fft_blocks_schedule_wf; smt().
have hfit : processed * W64.to_uint m <= 256 by
  move: hwf; rewrite /fft_blocks_schedule_wf; smt().
have htwid :
  forall k, 0 <= k < W64.to_uint md2 =>
    k * W64.to_uint stride < 256 by
  move: hwf; rewrite /fft_blocks_schedule_wf; smt().
have hstartw :
  W64.to_uint (fft_block_start_word m block) = fft_block_start m block.
+ apply (fft_block_start_word_uint m block).
  smt().
rewrite /fft_k_schedule_wf.
split.
+ smt(W64.to_uint_cmp).
split.
+ smt().
split.
+ rewrite hstartw.
  rewrite /fft_block_end /fft_block_start in hend.
  smt().
move=> k hk.
exact (htwid k hk).
qed.

lemma fft_k_prefix_decode_at_outside_block
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (block j : int) :
  W64.to_uint m = 2 * W64.to_uint md2 =>
  0 <= fft_block_start m block < W64.modulus =>
  ! fft_block_range m block j =>
  fft_k_prefix_decode_at
    data roots
    (fft_block_start_word m block)
    md2 stride
    (W64.to_uint md2)
    j =
  fft_decode_at data j.
proof.
move=> hm hstart houtside.
have hstartw :=
  fft_block_start_word_uint m block hstart.
rewrite /fft_k_prefix_decode_at /fft_block_range /fft_block_end /fft_block_start.
rewrite hstartw.
have heven :
  !(fft_block_start m block <= j <
      fft_block_start m block + W64.to_uint md2).
+ smt().
have hodd :
  !(fft_block_start m block + W64.to_uint md2 <= j /\
    j < fft_block_start m block + W64.to_uint md2 + W64.to_uint md2).
+ smt().
by smt().
qed.

lemma fft_block_step_prefixE
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (block : int) :
  KeygenM23SingularFFTSpec.fft_block_step
    roots m md2 stride data block =
  KeygenM23SingularFFTSpec.fft_k_prefix
    data roots (fft_block_start_word m block) md2 stride
    (W64.to_uint md2).
proof.
by rewrite /KeygenM23SingularFFTSpec.fft_block_step
           /fft_block_start_word.
qed.

lemma fft_block_step_decode
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (block j : int) :
  0 <= block =>
  fft_blocks_schedule_wf m md2 stride (block + 1) =>
  0 <= j < 256 =>
  fft_k_prefix_safe
    data roots
    (fft_block_start_word m block)
    md2 stride
    (W64.to_uint md2) =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_block_step
      roots m md2 stride data block)
    j =
  fft_k_prefix_decode_at
    data roots
    (fft_block_start_word m block)
    md2 stride
    (W64.to_uint md2)
    j.
proof.
move=> hblock hwf hj hsafe.
have hwfk :=
  fft_blocks_schedule_wf_local m md2 stride (block + 1) block hwf _.
+ split.
  + exact hblock.
  smt().
have hstep := fft_block_step_prefixE data roots m md2 stride block.
have hdecode := congr1 (fun a => fft_decode_at a j) _ _ hstep.
have hprefix :=
  fft_k_prefix_decode
    data roots
    (fft_block_start_word m block)
    md2 stride
    (W64.to_uint md2)
    j
    hwfk
    hj
    hsafe.
clear hstep.
smt().
qed.

lemma fft_block_step_decode_frame
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (block j : int) :
  0 <= block =>
  fft_blocks_schedule_wf m md2 stride (block + 1) =>
  0 <= j < 256 =>
  fft_k_prefix_safe
    data roots
    (fft_block_start_word m block)
    md2 stride
    (W64.to_uint md2) =>
  ! fft_block_range m block j =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_block_step
      roots m md2 stride data block)
    j =
  fft_decode_at data j.
proof.
move=> hblock hwf hj hsafe houtside.
rewrite
  (fft_block_step_decode
    data roots m md2 stride block j
    hblock hwf hj hsafe).
have [hstart0 hend] :=
  fft_block_start_bounds m md2 stride (block + 1) block hwf _.
+ split.
  + exact hblock.
  smt().
have hstart : 0 <= fft_block_start m block < W64.modulus by smt().
move: hwf => [_ [_ [hm _]]].
exact
  (fft_k_prefix_decode_at_outside_block
    data roots m md2 stride block j hm hstart houtside).
qed.

lemma fft_blocks_prefix_decode_at0
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (j : int) :
  fft_blocks_prefix_decode_at data roots m md2 stride 0 j =
  fft_decode_at data j.
proof.
by rewrite /fft_blocks_prefix_decode_at iota0.
qed.

lemma fft_blocks_prefix_decode_atS
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (processed j : int) :
  0 <= processed =>
  fft_blocks_prefix_decode_at
    data roots m md2 stride (processed + 1) j =
  fft_blocks_decode_step
    data roots m md2 stride j
    (fft_blocks_prefix_decode_at data roots m md2 stride processed j)
    processed.
proof.
move=> hprocessed.
rewrite /fft_blocks_prefix_decode_at.
by rewrite iotaSr 1:hprocessed foldl_rcons.
qed.

lemma fft_blocks_prefix_decode_at_hereS
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (processed j : int) :
  0 <= processed =>
  fft_block_range m processed j =>
  fft_blocks_prefix_decode_at
    data roots m md2 stride (processed + 1) j =
  fft_k_prefix_decode_at
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride processed)
    roots
    (fft_block_start_word m processed)
    md2 stride
    (W64.to_uint md2)
    j.
proof.
move=> hprocessed hrange.
rewrite
  (fft_blocks_prefix_decode_atS
    data roots m md2 stride processed j hprocessed).
rewrite /fft_blocks_decode_step.
by rewrite ifT.
qed.

lemma fft_blocks_prefix_decode_at_frameS
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (processed j : int) :
  0 <= processed =>
  ! fft_block_range m processed j =>
  fft_blocks_prefix_decode_at
    data roots m md2 stride (processed + 1) j =
  fft_blocks_prefix_decode_at
    data roots m md2 stride processed j.
proof.
move=> hprocessed houtside.
rewrite
  (fft_blocks_prefix_decode_atS
    data roots m md2 stride processed j hprocessed).
rewrite /fft_blocks_decode_step.
by rewrite ifF.
qed.

lemma fft_blocks_prefix_decode
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (processed j : int) :
  fft_blocks_schedule_wf m md2 stride processed =>
  0 <= j < 256 =>
  fft_blocks_prefix_safe data roots m md2 stride processed =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride processed)
    j =
  fft_blocks_prefix_decode_at
    data roots m md2 stride processed j.
proof.
move=> hwf hj.
have hgeneral :
  forall p,
    0 <= p =>
    fft_blocks_schedule_wf m md2 stride p =>
    fft_blocks_prefix_safe data roots m md2 stride p =>
    forall i, 0 <= i < 256 =>
      fft_decode_at
        (KeygenM23SingularFFTSpec.fft_blocks_prefix
          data roots m md2 stride p)
        i =
      fft_blocks_prefix_decode_at
        data roots m md2 stride p i.
+ apply intind.
  + move=> hwf0 _ i hi.
    by rewrite KeygenM23SingularFFTSpec.fft_blocks_prefix0
               fft_blocks_prefix_decode_at0.
  + move=> p hp0 ih hwfS hsafeS i hi.
    have hwfP := fft_blocks_schedule_wf_prev m md2 stride p hp0 hwfS.
    have hsafeP :=
      fft_blocks_prefix_safe_prev
        data roots m md2 stride p hp0 hsafeS.
    have hcur_safe :
      fft_k_prefix_safe
        (KeygenM23SingularFFTSpec.fft_blocks_prefix
          data roots m md2 stride p)
        roots
        (fft_block_start_word m p)
        md2 stride
        (W64.to_uint md2).
    + rewrite /fft_blocks_prefix_safe in hsafeS.
      have hp_range : 0 <= p < p + 1 by smt().
      exact (hsafeS p hp_range).
    rewrite KeygenM23SingularFFTSpec.fft_blocks_prefixS 1:hp0.
    case (fft_block_range m p i) => hirange.
    + rewrite
        (fft_block_step_decode
          (KeygenM23SingularFFTSpec.fft_blocks_prefix
            data roots m md2 stride p)
          roots m md2 stride p i
          hp0 hwfS hi hcur_safe).
      rewrite
        (fft_blocks_prefix_decode_at_hereS
          data roots m md2 stride p i hp0 hirange).
      done.
    + have hframe :=
        fft_block_step_decode_frame
          (KeygenM23SingularFFTSpec.fft_blocks_prefix
            data roots m md2 stride p)
          roots m md2 stride p i
          hp0 hwfS hi hcur_safe hirange.
      rewrite hframe.
      rewrite
        (fft_blocks_prefix_decode_at_frameS
          data roots m md2 stride p i hp0 hirange).
      exact (ih hwfP hsafeP i hi).
have hprocessed : 0 <= processed by
  move: hwf; rewrite /fft_blocks_schedule_wf; smt().
move=> hsafe.
exact (hgeneral processed hprocessed hwf hsafe j hj).
qed.

end KeygenM23SingularFFTBlockPrefixBridge.
