require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import BArray8192 BArray32768 BArray4096.

(* Input offsets count bytes; output offsets count 64-bit cells.  Byte-array
   reads outside the source array yield zero, so unused view slots are padded
   without requiring a complete 512-cell window to fit in the larger array. *)
op gauss_input_window (buf : BArray8192.t) (bo : int) : BArray8192.t =
  BArray8192.init (fun j => BArray8192.get8 buf (bo + j)).

op gauss_output_window (big : BArray32768.t) (oo : int) : BArray4096.t =
  BArray4096.init (fun j => BArray32768.get8 big (8 * oo + j)).

op gauss_big_output_frame (before after : BArray32768.t) (oo n : int) : bool =
  forall j, 0 <= j < 4096 => !(oo <= j < oo + n) =>
    BArray32768.get64 after j = BArray32768.get64 before j.

op gauss_window_bounds (n b bo oo c limit pos bytes : int) : bool =
  0 <= n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
  0 <= oo /\ oo + n <= 4096 /\
  0 <= c <= limit /\ limit <= n /\
  0 <= pos /\ 0 <= bytes /\ pos + bytes = b.

lemma gauss_input_window_get (buf : BArray8192.t) (bo j : int) :
  0 <= j < 8192 =>
  BArray8192.get8 (gauss_input_window buf bo) j = BArray8192.get8 buf (bo + j).
proof. by move=> hj; rewrite /gauss_input_window BArray8192.initiE. qed.

lemma gauss_output_window_get (big : BArray32768.t) (oo j : int) :
  0 <= j < 512 =>
  BArray4096.get64 (gauss_output_window big oo) j = BArray32768.get64 big (oo + j).
proof.
move=> hj; apply W8u8.wordP => k hk.
rewrite /gauss_output_window BArray4096.get64d_byte 1:hk
  BArray4096.initiE 1:/# BArray32768.get64d_byte 1:hk.
rewrite /=; congr; ring.
qed.

lemma gauss_output_window_set (big : BArray32768.t) (oo c : int) (v : W64.t) :
  0 <= c < 512 => 0 <= oo + c < 4096 =>
  gauss_output_window (BArray32768.set64 big (oo + c) v) oo =
  BArray4096.set64 (gauss_output_window big oo) c v.
proof.
move=> hc hbig; apply BArray4096.ext_eq64 => j hj.
have hj' : 0 <= j < 512 by smt().
rewrite gauss_output_window_get 1:hj'
  BArray32768.get_set64E 1:/# 1:/#
  BArray4096.get_set64E 1:/# 1:/# gauss_output_window_get 1:hj'.
smt().
qed.

lemma gauss_big_output_frame_refl (big : BArray32768.t) (oo n : int) :
  gauss_big_output_frame big big oo n.
proof. by rewrite /gauss_big_output_frame. qed.

lemma gauss_big_output_frame_set
    (before after : BArray32768.t) (oo n c : int) (v : W64.t) :
  0 <= c < n => gauss_big_output_frame before after oo n =>
  gauss_big_output_frame before (BArray32768.set64 after (oo + c) v) oo n.
proof.
move=> hc hf; rewrite /gauss_big_output_frame => j hj hout.
rewrite BArray32768.get_set64E_neq 1:/#.
exact (hf j hj hout).
qed.

lemma gauss_window_offset_uint (off i : W64.t) (k : int) :
  0 <= W64.to_uint off <= 8192 => 0 <= W64.to_uint i <= 8192 =>
  0 <= k <= 26 =>
  W64.to_uint (off + i + W64.of_int k) = W64.to_uint off + W64.to_uint i + k.
proof.
move=> ho hi hk.
rewrite W64.to_uintD_small.
+ rewrite W64.to_uintD_small 1:/# W64.to_uint_small 1:/# /=; smt().
rewrite W64.to_uintD_small 1:/# W64.to_uint_small 1:/#.
trivial.
qed.

lemma gauss_window_index_uint (i : W64.t) (k : int) :
  0 <= W64.to_uint i <= 8192 => 0 <= k <= 26 =>
  W64.to_uint (i + W64.of_int k) = W64.to_uint i + k.
proof.
move=> hi hk; rewrite W64.to_uintD_small.
+ rewrite W64.to_uint_small 1:/# /=; smt().
by rewrite W64.to_uint_small 1:/#.
qed.

lemma gauss_window_output_uint (off c : W64.t) :
  0 <= W64.to_uint off <= 4096 => 0 <= W64.to_uint c <= 512 =>
  W64.to_uint (off + c) = W64.to_uint off + W64.to_uint c.
proof. move=> ho hc; by rewrite W64.to_uintD_small 1:/#. qed.

lemma gauss_window_bounds_short n b bo oo c limit pos bytes :
  gauss_window_bounds n b bo oo c limit pos bytes =>
  gauss_window_bounds n b bo oo c c pos bytes.
proof. rewrite /gauss_window_bounds; smt(). qed.

lemma gauss_window_bounds_step n b bo oo c limit pos bytes accepted :
  gauss_window_bounds n b bo oo c limit pos bytes =>
  c < limit => 26 <= bytes => 0 <= accepted <= 1 =>
  gauss_window_bounds n b bo oo (c + accepted) limit (pos + 26) (bytes - 26).
proof. rewrite /gauss_window_bounds; smt(). qed.

lemma gauss_input_window_read (buf : BArray8192.t) (off pos : W64.t) (k : int) :
  W64.to_uint off + W64.to_uint pos + 26 <= 8192 => 0 <= k < 26 =>
  BArray8192.get8 buf (W64.to_uint (off + pos + W64.of_int k)) =
  BArray8192.get8 (gauss_input_window buf (W64.to_uint off))
    (W64.to_uint (pos + W64.of_int k)).
proof.
move=> hb hk.
have ho := W64.to_uint_cmp off.
have hp := W64.to_uint_cmp pos.
rewrite gauss_window_offset_uint 1:/# 1:/# 1:/#
  gauss_window_index_uint 1:/# 1:/# gauss_input_window_get 1:/#.
congr; ring.
qed.
