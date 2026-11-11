require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import GaussianTraceSpec.

op gauss_chunk_prefix (buf : BArray8192.t) (partial : BArray26.t)
    (offset copied : int) : bool =
  forall j, 0 <= j < copied =>
    BArray26.get8 partial j = BArray8192.get8 buf (offset + j).

lemma gauss_chunk_get buf offset j : 0 <= j < 26 =>
  BArray26.get8 (gauss_chunk buf offset) j = BArray8192.get8 buf (offset + j).
proof. by move=> hj; rewrite /gauss_chunk BArray26.initiE. qed.

lemma gauss_chunk_prefix0 buf partial offset :
  gauss_chunk_prefix buf partial offset 0.
proof. by rewrite /gauss_chunk_prefix; smt(). qed.

lemma gauss_chunk_prefix_step buf partial offset k :
  0 <= k < 26 => gauss_chunk_prefix buf partial offset k =>
  gauss_chunk_prefix buf
    (BArray26.set8 partial k (BArray8192.get8 buf (offset + k))) offset (k + 1).
proof.
  move=> hk hp; rewrite /gauss_chunk_prefix => j hj.
  rewrite BArray26.get_set_if.
  smt().
qed.

lemma gauss_chunk_prefix_full buf partial offset :
  gauss_chunk_prefix buf partial offset 26 => partial = gauss_chunk buf offset.
proof.
  move=> hp; apply BArray26.ext_eq => j hj.
  rewrite gauss_chunk_get 1:hj.
  exact (hp j hj).
qed.

lemma gauss_chunk_word_index (offset k : int) :
  0 <= offset <= 8166 => 0 <= k < 26 =>
  W64.to_uint (W64.of_int offset + W64.of_int k) = offset + k.
proof.
  move=> ho hk; rewrite -W64.of_intD W64.of_uintK /=.
  apply modz_small; smt().
qed.

lemma gauss_complete_chunks (available attempts : int) :
  0 <= available - 26 * attempts < 26 =>
  available %/ 26 = attempts.
proof.
  move=> h; apply divz_eqP; smt().
qed.

lemma gauss_chunk_count_bound (available : int) :
  0 <= available <= 8192 => 0 <= available %/ 26 <= 315.
proof.
  move=> h.
  have hd := divz_eq available 26.
  have hm := modz_cmp available 26.
  smt().
qed.

lemma gauss_square_overwrite (s t : BArray16.t) (lo hi : W64.t) :
  BArray16.set64 (BArray16.set64 s 0 lo) 1 hi =
  BArray16.set64 (BArray16.set64 t 0 lo) 1 hi.
proof.
  apply BArray16.ext_eq64 => j hj.
  have hcases : j = 0 \/ j = 1 by smt().
  case hcases => ->; by rewrite !BArray16.get_set64E /=.
qed.
