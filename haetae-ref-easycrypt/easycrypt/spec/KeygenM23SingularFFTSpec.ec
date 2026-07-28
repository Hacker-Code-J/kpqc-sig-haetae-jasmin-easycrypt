require import AllCore IntDiv List Ring.

from Jasmin require import JModel_x86.

require import
  BArray512 BArray1024 BArray2048 BArray8192 SBArray8192_1024.
require import KeygenM23SingularSpec.

theory KeygenM23SingularFFTSpec.

op fft_words_i : int = 256.
op fft_stages_i : int = 8.
op mode2_s1_count_i : int = 3.
op mode2_s2_count_i : int = 2.
op mode2_slice_count_i : int = 5.

op fft_init_step
    (xp : BArray1024.t) (roots : BArray2048.t) (brv : BArray512.t)
    (data : BArray2048.t) (i : int) : BArray2048.t =
  let ridx =
    (zeroextu64 (BArray512.get16 brv i)) `<<` W8.of_int 1 in
  let idx = (W64.of_int i) `<<` W8.of_int 1 in
  let c = BArray1024.get32 xp i in
  let data =
    BArray2048.set32 data (W64.to_uint ridx)
      (c * BArray2048.get32 roots (W64.to_uint idx)) in
  BArray2048.set32 data (W64.to_uint (ridx + W64.one))
    (c * BArray2048.get32 roots (W64.to_uint (idx + W64.one))).

op fft_init_prefix
    (data : BArray2048.t) (xp : BArray1024.t)
    (roots : BArray2048.t) (brv : BArray512.t) (processed : int)
    : BArray2048.t =
  foldl (fft_init_step xp roots brv) data (iota_ 0 processed).

op fft_init_and_bitrev
    (data : BArray2048.t) (xp : BArray1024.t)
    (roots : BArray2048.t) (brv : BArray512.t) : BArray2048.t =
  fft_init_prefix data xp roots brv fft_words_i.

op fft_butterfly
    (data roots : BArray2048.t) (even odd twid : W64.t)
    : BArray2048.t =
  let eidx = even `<<` W8.of_int 1 in
  let oidx = odd `<<` W8.of_int 1 in
  let tidx = twid `<<` W8.of_int 1 in
  let ureal = BArray2048.get32 data (W64.to_uint eidx) in
  let uimag =
    BArray2048.get32 data (W64.to_uint (eidx + W64.one)) in
  let oreal = BArray2048.get32 data (W64.to_uint oidx) in
  let oimag =
    BArray2048.get32 data (W64.to_uint (oidx + W64.one)) in
  let rreal = BArray2048.get32 roots (W64.to_uint tidx) in
  let rimag =
    BArray2048.get32 roots (W64.to_uint (tidx + W64.one)) in
  let treal =
    KeygenM23SingularSpec.mulrnd16_word rreal oreal -
      KeygenM23SingularSpec.mulrnd16_word rimag oimag in
  let timag =
    KeygenM23SingularSpec.mulrnd16_word rreal oimag +
      KeygenM23SingularSpec.mulrnd16_word rimag oreal in
  let data =
    BArray2048.set32 data (W64.to_uint eidx) (ureal + treal) in
  let data =
    BArray2048.set32 data (W64.to_uint (eidx + W64.one))
      (uimag + timag) in
  let data =
    BArray2048.set32 data (W64.to_uint oidx) (ureal - treal) in
  BArray2048.set32 data (W64.to_uint (oidx + W64.one))
    (uimag - timag).

op fft_k_step
    (roots : BArray2048.t) (n md2 stride : W64.t)
    (data : BArray2048.t) (ki : int) : BArray2048.t =
  let k = W64.of_int ki in
  let even = n + k in
  let odd = even + md2 in
  let twid = k * stride in
  fft_butterfly data roots even odd twid.

op fft_k_prefix
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (processed : int) : BArray2048.t =
  foldl (fft_k_step roots n md2 stride) data (iota_ 0 processed).

op fft_block_step
    (roots : BArray2048.t) (m md2 stride : W64.t)
    (data : BArray2048.t) (block : int) : BArray2048.t =
  let n = W64.of_int block * m in
  fft_k_prefix data roots n md2 stride (W64.to_uint md2).

op fft_blocks_prefix
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (processed : int) : BArray2048.t =
  foldl (fft_block_step roots m md2 stride) data (iota_ 0 processed).

op fft_block_count (m : W64.t) : int =
  fft_words_i %/ W64.to_uint m.

op fft_stage
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    : BArray2048.t =
  fft_blocks_prefix data roots m md2 stride (fft_block_count m).

type fft_schedule_state =
  BArray2048.t * W64.t * W64.t * W64.t.

op fft_round_step
    (roots : BArray2048.t) (st : fft_schedule_state) (_ : int)
    : fft_schedule_state =
  (fft_stage st.`1 roots st.`2 st.`3 st.`4,
   st.`2 `<<` W8.of_int 1,
   st.`3 `<<` W8.of_int 1,
   st.`4 `>>` W8.of_int 1).

op fft_schedule_prefix
    (data roots : BArray2048.t) (processed : int)
    : fft_schedule_state =
  foldl (fft_round_step roots)
    (data, W64.of_int 2, W64.of_int 1, W64.of_int 256)
    (iota_ 0 processed).

op fft_full
    (data roots : BArray2048.t) : BArray2048.t =
  (fft_schedule_prefix data roots fft_stages_i).`1.

op mode2_slice
    (s1 s2 : BArray8192.t) (slot : int) : BArray1024.t =
  if slot < mode2_s1_count_i
  then
    SBArray8192_1024.get_sub32 s1
      (slot * KeygenM23SingularSpec.singular_words_i)
  else
    SBArray8192_1024.get_sub32 s2
      ((slot - mode2_s1_count_i) *
        KeygenM23SingularSpec.singular_words_i).

op mode2_fft
    (data : BArray2048.t) (s1 s2 : BArray8192.t)
    (roots : BArray2048.t) (brv : BArray512.t) (slot : int)
    : BArray2048.t =
  fft_full
    (fft_init_and_bitrev data (mode2_slice s1 s2 slot) roots brv)
    roots.

type mode2_pipeline_state = BArray2048.t * BArray1024.t.

op mode2_accumulate_step
    (s1 s2 : BArray8192.t) (roots : BArray2048.t)
    (brv : BArray512.t) (st : mode2_pipeline_state) (slot : int)
    : mode2_pipeline_state =
  let data = mode2_fft st.`1 s1 s2 roots brv slot in
  (data,
   KeygenM23SingularSpec.accumulate_fft_sqabs st.`2 data).

op mode2_accumulate_prefix
    (s1 s2 : BArray8192.t) (roots : BArray2048.t)
    (brv : BArray512.t) (processed : int) : mode2_pipeline_state =
  foldl (mode2_accumulate_step s1 s2 roots brv)
    (witness, KeygenM23SingularSpec.clear_sum witness)
    (iota_ 0 processed).

op mode2_accumulate
    (s1 s2 : BArray8192.t) (roots : BArray2048.t)
    (brv : BArray512.t) : BArray1024.t =
  (mode2_accumulate_prefix
    s1 s2 roots brv mode2_slice_count_i).`2.

op mode2_singular_word
    (s1 s2 : BArray8192.t) (roots : BArray2048.t)
    (brv : BArray512.t) : W64.t =
  KeygenM23SingularSpec.finish_mode2
    (mode2_accumulate s1 s2 roots brv).

lemma fft_init_prefix0 data xp roots brv :
  fft_init_prefix data xp roots brv 0 = data.
proof. by rewrite /fft_init_prefix iota0. qed.

lemma fft_init_prefixS data xp roots brv processed :
  0 <= processed =>
  fft_init_prefix data xp roots brv (processed + 1) =
    fft_init_step xp roots brv
      (fft_init_prefix data xp roots brv processed) processed.
proof.
move=> hprocessed.
by rewrite /fft_init_prefix iotaSr 1:hprocessed foldl_rcons.
qed.

lemma fft_k_prefix0 data roots n md2 stride :
  fft_k_prefix data roots n md2 stride 0 = data.
proof. by rewrite /fft_k_prefix iota0. qed.

lemma fft_k_prefixS data roots n md2 stride processed :
  0 <= processed =>
  fft_k_prefix data roots n md2 stride (processed + 1) =
    fft_k_step roots n md2 stride
      (fft_k_prefix data roots n md2 stride processed) processed.
proof.
move=> hprocessed.
by rewrite /fft_k_prefix iotaSr 1:hprocessed foldl_rcons.
qed.

lemma fft_blocks_prefix0 data roots m md2 stride :
  fft_blocks_prefix data roots m md2 stride 0 = data.
proof. by rewrite /fft_blocks_prefix iota0. qed.

lemma fft_blocks_prefixS data roots m md2 stride processed :
  0 <= processed =>
  fft_blocks_prefix data roots m md2 stride (processed + 1) =
    fft_block_step roots m md2 stride
      (fft_blocks_prefix data roots m md2 stride processed) processed.
proof.
move=> hprocessed.
by rewrite /fft_blocks_prefix iotaSr 1:hprocessed foldl_rcons.
qed.

lemma fft_schedule_prefix0 data roots :
  fft_schedule_prefix data roots 0 =
    (data, W64.of_int 2, W64.of_int 1, W64.of_int 256).
proof. by rewrite /fft_schedule_prefix iota0. qed.

lemma fft_schedule_prefixS data roots processed :
  0 <= processed =>
  fft_schedule_prefix data roots (processed + 1) =
    fft_round_step roots
      (fft_schedule_prefix data roots processed) processed.
proof.
move=> hprocessed.
by rewrite /fft_schedule_prefix iotaSr 1:hprocessed foldl_rcons.
qed.

lemma mode2_accumulate_prefix0 s1 s2 roots brv :
  mode2_accumulate_prefix s1 s2 roots brv 0 =
    (witness, KeygenM23SingularSpec.clear_sum witness).
proof. by rewrite /mode2_accumulate_prefix iota0. qed.

lemma mode2_accumulate_prefixS s1 s2 roots brv processed :
  0 <= processed =>
  mode2_accumulate_prefix s1 s2 roots brv (processed + 1) =
    mode2_accumulate_step s1 s2 roots brv
      (mode2_accumulate_prefix s1 s2 roots brv processed) processed.
proof.
move=> hprocessed.
by rewrite /mode2_accumulate_prefix iotaSr 1:hprocessed foldl_rcons.
qed.

end KeygenM23SingularFFTSpec.
