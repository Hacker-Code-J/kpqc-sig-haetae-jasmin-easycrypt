require import AllCore IntDiv List Ring StdOrder Real.

from Jasmin require import JModel_x86.

import RField RealOrder.

require import BArray2048.
require import
  KeygenM23ComplexReal
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTKPrefixBridge
  KeygenM23SingularFFTBlockPrefixBridge.

import KeygenM23ComplexReal.
import KeygenM23SingularFFTInitBridge.
import KeygenM23SingularFFTKPrefixBridge.
import KeygenM23SingularFFTBlockPrefixBridge.

theory KeygenM23SingularFFTStageBridge.

op fft_stage_reachable_params (m md2 stride : W64.t) : bool =
     (W64.to_uint m = 2   /\ W64.to_uint md2 = 1   /\ W64.to_uint stride = 256)
  \/ (W64.to_uint m = 4   /\ W64.to_uint md2 = 2   /\ W64.to_uint stride = 128)
  \/ (W64.to_uint m = 8   /\ W64.to_uint md2 = 4   /\ W64.to_uint stride = 64)
  \/ (W64.to_uint m = 16  /\ W64.to_uint md2 = 8   /\ W64.to_uint stride = 32)
  \/ (W64.to_uint m = 32  /\ W64.to_uint md2 = 16  /\ W64.to_uint stride = 16)
  \/ (W64.to_uint m = 64  /\ W64.to_uint md2 = 32  /\ W64.to_uint stride = 8)
  \/ (W64.to_uint m = 128 /\ W64.to_uint md2 = 64  /\ W64.to_uint stride = 4)
  \/ (W64.to_uint m = 256 /\ W64.to_uint md2 = 128 /\ W64.to_uint stride = 2).

op fft_stage_schedule (m md2 stride : W64.t) : bool =
  fft_blocks_schedule_wf m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m) /\
  KeygenM23SingularFFTSpec.fft_block_count m * W64.to_uint m = 256.

op fft_stage_owner_block (m : W64.t) (j : int) : int =
  j %/ W64.to_uint m.

op fft_stage_safe
    (data roots : BArray2048.t) (m md2 stride : W64.t) : bool =
  fft_blocks_prefix_safe data roots m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m).

op fft_stage_decode_at
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (j : int) : complex =
  let block = fft_stage_owner_block m j in
  fft_k_prefix_decode_at
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    roots
    (fft_block_start_word m block)
    md2 stride
    (W64.to_uint md2)
    j.

lemma fft_stage_schedule_r1 :
  fft_stage_schedule
    (W64.of_int 2) (W64.of_int 1) (W64.of_int 256).
proof.
rewrite /fft_stage_schedule /fft_blocks_schedule_wf.
rewrite /KeygenM23SingularFFTSpec.fft_block_count.
have hm : W64.to_uint (W64.of_int 2) = 2 by
  rewrite W64.to_uint_small 1:/#.
have hmd2 : W64.to_uint (W64.of_int 1) = 1 by
  rewrite W64.to_uint_small 1:/#.
have hstride : W64.to_uint (W64.of_int 256) = 256 by
  rewrite W64.to_uint_small 1:/#.
rewrite hm hmd2 hstride.
smt().
qed.

lemma fft_stage_schedule_r2 :
  fft_stage_schedule
    (W64.of_int 4) (W64.of_int 2) (W64.of_int 128).
proof.
rewrite /fft_stage_schedule /fft_blocks_schedule_wf.
rewrite /KeygenM23SingularFFTSpec.fft_block_count.
have hm : W64.to_uint (W64.of_int 4) = 4 by
  rewrite W64.to_uint_small 1:/#.
have hmd2 : W64.to_uint (W64.of_int 2) = 2 by
  rewrite W64.to_uint_small 1:/#.
have hstride : W64.to_uint (W64.of_int 128) = 128 by
  rewrite W64.to_uint_small 1:/#.
rewrite hm hmd2 hstride.
smt().
qed.

lemma fft_stage_schedule_r3 :
  fft_stage_schedule
    (W64.of_int 8) (W64.of_int 4) (W64.of_int 64).
proof.
rewrite /fft_stage_schedule /fft_blocks_schedule_wf.
rewrite /KeygenM23SingularFFTSpec.fft_block_count.
have hm : W64.to_uint (W64.of_int 8) = 8 by
  rewrite W64.to_uint_small 1:/#.
have hmd2 : W64.to_uint (W64.of_int 4) = 4 by
  rewrite W64.to_uint_small 1:/#.
have hstride : W64.to_uint (W64.of_int 64) = 64 by
  rewrite W64.to_uint_small 1:/#.
rewrite hm hmd2 hstride.
smt().
qed.

lemma fft_stage_schedule_r4 :
  fft_stage_schedule
    (W64.of_int 16) (W64.of_int 8) (W64.of_int 32).
proof.
rewrite /fft_stage_schedule /fft_blocks_schedule_wf.
rewrite /KeygenM23SingularFFTSpec.fft_block_count.
have hm : W64.to_uint (W64.of_int 16) = 16 by
  rewrite W64.to_uint_small 1:/#.
have hmd2 : W64.to_uint (W64.of_int 8) = 8 by
  rewrite W64.to_uint_small 1:/#.
have hstride : W64.to_uint (W64.of_int 32) = 32 by
  rewrite W64.to_uint_small 1:/#.
rewrite hm hmd2 hstride.
smt().
qed.

lemma fft_stage_schedule_r5 :
  fft_stage_schedule
    (W64.of_int 32) (W64.of_int 16) (W64.of_int 16).
proof.
rewrite /fft_stage_schedule /fft_blocks_schedule_wf.
rewrite /KeygenM23SingularFFTSpec.fft_block_count.
have hm : W64.to_uint (W64.of_int 32) = 32 by
  rewrite W64.to_uint_small 1:/#.
have hmd2 : W64.to_uint (W64.of_int 16) = 16 by
  rewrite W64.to_uint_small 1:/#.
have hstride : W64.to_uint (W64.of_int 16) = 16 by
  rewrite W64.to_uint_small 1:/#.
rewrite hm hmd2.
smt().
qed.

lemma fft_stage_schedule_r6 :
  fft_stage_schedule
    (W64.of_int 64) (W64.of_int 32) (W64.of_int 8).
proof.
rewrite /fft_stage_schedule /fft_blocks_schedule_wf.
rewrite /KeygenM23SingularFFTSpec.fft_block_count.
have hm : W64.to_uint (W64.of_int 64) = 64 by
  rewrite W64.to_uint_small 1:/#.
have hmd2 : W64.to_uint (W64.of_int 32) = 32 by
  rewrite W64.to_uint_small 1:/#.
have hstride : W64.to_uint (W64.of_int 8) = 8 by
  rewrite W64.to_uint_small 1:/#.
rewrite hm hmd2 hstride.
smt().
qed.

lemma fft_stage_schedule_r7 :
  fft_stage_schedule
    (W64.of_int 128) (W64.of_int 64) (W64.of_int 4).
proof.
rewrite /fft_stage_schedule /fft_blocks_schedule_wf.
rewrite /KeygenM23SingularFFTSpec.fft_block_count.
have hm : W64.to_uint (W64.of_int 128) = 128 by
  rewrite W64.to_uint_small 1:/#.
have hmd2 : W64.to_uint (W64.of_int 64) = 64 by
  rewrite W64.to_uint_small 1:/#.
have hstride : W64.to_uint (W64.of_int 4) = 4 by
  rewrite W64.to_uint_small 1:/#.
rewrite hm hmd2 hstride.
smt().
qed.

lemma fft_stage_schedule_r8 :
  fft_stage_schedule
    (W64.of_int 256) (W64.of_int 128) (W64.of_int 2).
proof.
rewrite /fft_stage_schedule /fft_blocks_schedule_wf.
rewrite /KeygenM23SingularFFTSpec.fft_block_count.
have hm : W64.to_uint (W64.of_int 256) = 256 by
  rewrite W64.to_uint_small 1:/#.
have hmd2 : W64.to_uint (W64.of_int 128) = 128 by
  rewrite W64.to_uint_small 1:/#.
have hstride : W64.to_uint (W64.of_int 2) = 2 by
  rewrite W64.to_uint_small 1:/#.
rewrite hm hmd2 hstride.
smt().
qed.

lemma fft_stage_reachable_schedule (m md2 stride : W64.t) :
  fft_stage_reachable_params m md2 stride =>
  fft_stage_schedule m md2 stride.
proof.
rewrite /fft_stage_reachable_params.
smt(fft_stage_schedule_r1 fft_stage_schedule_r2 fft_stage_schedule_r3
    fft_stage_schedule_r4 fft_stage_schedule_r5 fft_stage_schedule_r6
    fft_stage_schedule_r7 fft_stage_schedule_r8).
qed.

lemma fft_stage_owner_block_range
    (m md2 stride : W64.t) (j : int) :
  fft_stage_schedule m md2 stride =>
  0 <= j < 256 =>
  0 <= fft_stage_owner_block m j <
    KeygenM23SingularFFTSpec.fft_block_count m.
proof.
rewrite /fft_stage_owner_block /fft_stage_schedule.
rewrite /KeygenM23SingularFFTSpec.fft_block_count /fft_blocks_schedule_wf.
smt(W64.to_uint_cmp).
qed.

lemma fft_stage_owner_block_here
    (m md2 stride : W64.t) (j : int) :
  fft_stage_schedule m md2 stride =>
  0 <= j < 256 =>
  fft_block_range m (fft_stage_owner_block m j) j.
proof.
rewrite /fft_stage_owner_block /fft_stage_schedule.
rewrite /fft_block_range /fft_block_start /fft_block_end.
rewrite /KeygenM23SingularFFTSpec.fft_block_count /fft_blocks_schedule_wf.
smt(W64.to_uint_cmp).
qed.

lemma fft_stage_owner_block_unique
    (m md2 stride : W64.t) (block j : int) :
  fft_stage_schedule m md2 stride =>
  0 <= j < 256 =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  fft_block_range m block j =>
  block = fft_stage_owner_block m j.
proof.
rewrite /fft_stage_owner_block /fft_stage_schedule.
rewrite /fft_block_range /fft_block_start /fft_block_end.
rewrite /KeygenM23SingularFFTSpec.fft_block_count /fft_blocks_schedule_wf.
smt(W64.to_uint_cmp).
qed.

lemma fft_stage_owner_block_outside
    (m md2 stride : W64.t) (block j : int) :
  fft_stage_schedule m md2 stride =>
  0 <= j < 256 =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  block <> fft_stage_owner_block m j =>
  ! fft_block_range m block j.
proof.
move=> hstage hj hblock hneq.
case (fft_block_range m block j) => hrange.
+ have heq :=
     fft_stage_owner_block_unique
       m md2 stride block j hstage hj hblock hrange.
   smt().
done.
qed.

lemma fft_stage_decode_at_owner
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (j : int) :
  fft_stage_schedule m md2 stride =>
  0 <= j < 256 =>
  fft_blocks_prefix_decode_at
    data roots m md2 stride
    (fft_stage_owner_block m j + 1) j =
  fft_stage_decode_at data roots m md2 stride j.
proof.
move=> hstage hj.
have [howner0 hownerlt] :=
  fft_stage_owner_block_range m md2 stride j hstage hj.
have hhere :=
  fft_stage_owner_block_here m md2 stride j hstage hj.
rewrite /fft_stage_decode_at.
by rewrite
  (fft_blocks_prefix_decode_at_hereS
    data roots m md2 stride
    (fft_stage_owner_block m j) j howner0 hhere).
qed.

lemma fft_stage_decode_at_suffix
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (j processed : int) :
  fft_stage_schedule m md2 stride =>
  0 <= j < 256 =>
  fft_stage_owner_block m j + 1 <= processed <=
    KeygenM23SingularFFTSpec.fft_block_count m =>
  fft_blocks_prefix_decode_at
    data roots m md2 stride processed j =
  fft_stage_decode_at data roots m md2 stride j.
proof.
move=> hstage hj hprocessed.
have [howner0 hownerlt] :=
  fft_stage_owner_block_range m md2 stride j hstage hj.
have hgeneral :
  forall extra,
    0 <= extra =>
    fft_stage_owner_block m j + 1 + extra <=
      KeygenM23SingularFFTSpec.fft_block_count m =>
    fft_blocks_prefix_decode_at
      data roots m md2 stride
      (fft_stage_owner_block m j + 1 + extra) j =
    fft_stage_decode_at data roots m md2 stride j.
+ apply intind.
  + move=> hbound.
    have -> :
      fft_stage_owner_block m j + 1 + 0 =
      fft_stage_owner_block m j + 1 by ring.
    exact (fft_stage_decode_at_owner data roots m md2 stride j hstage hj).
  + move=> extra hextra0 ih hboundS.
    have hproc0 : 0 <= fft_stage_owner_block m j + 1 + extra by smt().
    have hproc_lt :
      fft_stage_owner_block m j + 1 + extra <
      KeygenM23SingularFFTSpec.fft_block_count m by smt().
    have houtside :
      ! fft_block_range m (fft_stage_owner_block m j + 1 + extra) j.
    + apply
        (fft_stage_owner_block_outside
          m md2 stride
          (fft_stage_owner_block m j + 1 + extra) j
          hstage hj).
      + split; smt().
      by smt().
    have -> :
      fft_stage_owner_block m j + 1 + (extra + 1) =
      (fft_stage_owner_block m j + 1 + extra) + 1 by ring.
    rewrite
      (fft_blocks_prefix_decode_at_frameS
        data roots m md2 stride
        (fft_stage_owner_block m j + 1 + extra)
        j hproc0 houtside).
    apply ih.
    smt().
have hextra0 :
  0 <= processed - (fft_stage_owner_block m j + 1) by smt().
have hbound :
  fft_stage_owner_block m j + 1 +
  (processed - (fft_stage_owner_block m j + 1)) <=
  KeygenM23SingularFFTSpec.fft_block_count m by smt().
have hsuffix :=
  hgeneral
    (processed - (fft_stage_owner_block m j + 1))
    hextra0 hbound.
have hprocE :
  fft_stage_owner_block m j + 1 +
  (processed - (fft_stage_owner_block m j + 1)) = processed by
  smt().
rewrite -hprocE.
exact hsuffix.
qed.

lemma fft_blocks_prefix_decode_at_stage
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (j : int) :
  fft_stage_schedule m md2 stride =>
  0 <= j < 256 =>
  fft_blocks_prefix_decode_at
    data roots m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m) j =
  fft_stage_decode_at data roots m md2 stride j.
proof.
move=> hstage hj.
apply
  (fft_stage_decode_at_suffix
    data roots m md2 stride j
    (KeygenM23SingularFFTSpec.fft_block_count m)
    hstage hj).
smt(fft_stage_owner_block_range).
qed.

lemma fft_stage_owner_block_reachable
    (m md2 stride : W64.t) (j : int) :
  fft_stage_reachable_params m md2 stride =>
  0 <= j < 256 =>
  0 <= fft_stage_owner_block m j <
    KeygenM23SingularFFTSpec.fft_block_count m /\
  fft_block_range m (fft_stage_owner_block m j) j.
proof.
move=> hreach hj.
have hstage := fft_stage_reachable_schedule m md2 stride hreach.
split.
+ exact (fft_stage_owner_block_range m md2 stride j hstage hj).
exact (fft_stage_owner_block_here m md2 stride j hstage hj).
qed.

lemma fft_stage_decode
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (j : int) :
  fft_stage_schedule m md2 stride =>
  0 <= j < 256 =>
  fft_stage_safe data roots m md2 stride =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_stage data roots m md2 stride)
    j =
  fft_stage_decode_at data roots m md2 stride j.
proof.
move=> hstage hj hsafe.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
rewrite /KeygenM23SingularFFTSpec.fft_stage.
rewrite
  (fft_blocks_prefix_decode
    data roots m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    j hwf hj hsafe).
exact (fft_blocks_prefix_decode_at_stage data roots m md2 stride j hstage hj).
qed.

lemma fft_stage_decode_reachable
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (j : int) :
  fft_stage_reachable_params m md2 stride =>
  0 <= j < 256 =>
  fft_stage_safe data roots m md2 stride =>
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_stage data roots m md2 stride)
    j =
  fft_stage_decode_at data roots m md2 stride j.
proof.
move=> hreach hj hsafe.
apply
  (fft_stage_decode
    data roots m md2 stride j
    (fft_stage_reachable_schedule m md2 stride hreach)
    hj hsafe).
qed.

end KeygenM23SingularFFTStageBridge.
