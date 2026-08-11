require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import Mode2HbzCodecSpec Mode2RansByteStack
  Mode2RansNormalization Mode2RansEncodeRefinement
  Mode2HbzTableCertificate.

theory Mode2RansArrayListBridge.

import Mode2HbzCodecSpec Mode2RansByteStack
       Mode2RansNormalization Mode2RansEncodeRefinement
       Mode2HbzTableCertificate.

op symbol_list_of_array (a : BArray2048.t) : int list =
  map W8.to_uint (take mode2_hbz_count (BArray2048.to_list a)).

op symbol_suffix (a : BArray2048.t) (i : int) : int list =
  drop i (symbol_list_of_array a).

op segment_matches
    (a : BArray2048.t) (start : int) (bs : int list) : bool =
  0 <= start /\
  start + size bs <= mode2_hbz_capacity /\
  forall k, 0 <= k < size bs =>
    W8.to_uint (BArray2048.get8 a (start + k)) = nth 0 bs k.

op prefix_frame
    (before after : BArray2048.t) (end_ : int) : bool =
  forall k, 0 <= k < end_ =>
    BArray2048.get8 after k = BArray2048.get8 before k.

lemma symbol_list_of_array_size a :
  size (symbol_list_of_array a) = mode2_hbz_count.
proof.
rewrite /symbol_list_of_array size_map size_take 1:/#
        BArray2048.size_to_list.
rewrite /mode2_hbz_count; trivial.
qed.

lemma symbol_list_of_array_nth a i :
  0 <= i < mode2_hbz_count =>
  nth 0 (symbol_list_of_array a) i =
    W8.to_uint (BArray2048.get8 a i).
proof.
move=> hi.
have hbound : 0 <= i <
    size (take mode2_hbz_count (BArray2048.to_list a)).
+ rewrite size_take 1:/# BArray2048.size_to_list
          /mode2_hbz_count; smt().
have hmap := nth_map W8.zero 0 W8.to_uint i
  (take mode2_hbz_count (BArray2048.to_list a)) hbound.
rewrite /symbol_list_of_array hmap.
rewrite nth_take 1:/# 1:/#.
by rewrite BArray2048.get_to_list.
qed.

lemma symbol_suffix_at_end a :
  symbol_suffix a mode2_hbz_count = [].
proof.
have hs := symbol_list_of_array_size a.
rewrite /symbol_suffix drop_oversize 1:/#.
trivial.
qed.

lemma symbol_suffix_cons a i :
  0 <= i < mode2_hbz_count =>
  symbol_suffix a i =
    W8.to_uint (BArray2048.get8 a i) :: symbol_suffix a (i + 1).
proof.
move=> hi.
have hbound : 0 <= i < size (symbol_list_of_array a) by
  rewrite symbol_list_of_array_size.
have hdrop := drop_nth 0 i (symbol_list_of_array a) hbound.
rewrite /symbol_suffix hdrop.
rewrite symbol_list_of_array_nth 1:hi.
trivial.
qed.

lemma symbol_suffix_size a i :
  0 <= i <= mode2_hbz_count =>
  size (symbol_suffix a i) = mode2_hbz_count - i.
proof.
move=> hi.
rewrite /symbol_suffix size_drop 1:/# symbol_list_of_array_size.
smt().
qed.

lemma canonical_symbol_list_nth xs :
  canonical_symbol_list xs <=>
  forall i, 0 <= i < size xs =>
    0 <= nth 0 xs i < mode2_hbz_alphabet.
proof.
elim: xs => [|x xs ih].
+ split; smt().
rewrite /canonical_symbol_list /= ih.
split.
+ move=> [hx hxs] i hi.
  case (i = 0) => [->>|hne]; first trivial.
  have hpos : 0 < i by smt().
  rewrite /=.
  apply hxs; smt().
+ move=> hall.
  split.
  - have := hall 0 _; first smt().
    trivial.
  - move=> i hi.
    have hnext := hall (i + 1) _; first smt().
    rewrite /= in hnext.
    rewrite ifF 1:/# in hnext.
    exact hnext.
qed.

lemma mode2_stream_canonical_list a :
  mode2_hbz_symbol_stream a =>
  canonical_symbol_list (symbol_list_of_array a).
proof.
move=> hs.
rewrite canonical_symbol_list_nth => i hi.
rewrite symbol_list_of_array_size in hi.
rewrite symbol_list_of_array_nth 1:hi.
exact (hs i hi).
qed.

lemma canonical_symbol_suffix a i :
  mode2_hbz_symbol_stream a =>
  0 <= i <= mode2_hbz_count =>
  canonical_symbol_list (symbol_suffix a i).
proof.
move=> hs hi.
rewrite canonical_symbol_list_nth => k hk.
rewrite /symbol_suffix nth_drop 1:/# 1:/#.
have hfull := mode2_stream_canonical_list a hs.
rewrite canonical_symbol_list_nth in hfull.
apply hfull.
rewrite /symbol_suffix size_drop 1:/# symbol_list_of_array_size in hk.
smt().
qed.

lemma segment_matches_nil a start :
  0 <= start <= mode2_hbz_capacity =>
  segment_matches a start [].
proof. rewrite /segment_matches /=; smt(). qed.

lemma segment_matches_nth a start bs k :
  segment_matches a start bs =>
  0 <= k < size bs =>
  W8.to_uint (BArray2048.get8 a (start + k)) = nth 0 bs k.
proof.
move=> [_ [_ hm]] hk.
exact (hm k hk).
qed.

lemma segment_matches_prepend_set a start bs b :
  segment_matches a start bs =>
  0 < start =>
  0 <= b < 256 =>
  segment_matches
    (BArray2048.set8 a (start - 1) (W8.of_int b))
    (start - 1) (b :: bs).
proof.
move=> hm hstart hb.
rewrite /segment_matches in hm.
rewrite /segment_matches.
have [hbase [hcap hbytes]] := hm.
split.
+ smt().
split.
+ rewrite /=.
   smt().
move=> k hk.
case (k = 0) => [->>|hk0].
+ rewrite BArray2048.get_setE 1:/#.
   smt().
+ have hkm1 : 0 <= k - 1 < size bs by smt().
  have hidx : start - 1 + k = start + (k - 1) by ring.
  rewrite hidx.
  rewrite BArray2048.get_setE 1:/# ifF 1:/#.
  have hv := hbytes (k - 1) hkm1.
  smt().
qed.

lemma segment_matches_cat a start xs ys :
  segment_matches a start xs =>
  segment_matches a (start + size xs) ys =>
  segment_matches a start (xs ++ ys).
proof.
move=> hl hr.
rewrite /segment_matches in hl.
rewrite /segment_matches in hr.
rewrite /segment_matches.
have [hstart [hlcap hlbytes]] := hl.
have [hrstart [hrcap hrbytes]] := hr.
rewrite size_cat.
split; first exact hstart.
split.
+ have : start + size xs + size ys <= mode2_hbz_capacity by
     exact hrcap.
   smt().
move=> k hk.
rewrite nth_cat.
case (k < size xs) => hleft.
+ have hkleft : 0 <= k < size xs by smt().
  exact (hlbytes k hkleft).
+ have -> : start + k = start + size xs + (k - size xs) by ring.
  have hkright : 0 <= k - size xs < size ys by smt().
  exact (hrbytes (k - size xs) hkright).
qed.

lemma prefix_frame_refl a end_ :
  prefix_frame a a end_.
proof. rewrite /prefix_frame; trivial. qed.

lemma prefix_frame_shrink before after small large :
  small <= large =>
  prefix_frame before after large =>
  prefix_frame before after small.
proof. rewrite /prefix_frame => hle hf k hk; apply hf; smt(). qed.

lemma prefix_frame_set_at_end before after end_ value :
  0 <= end_ < mode2_hbz_capacity =>
  prefix_frame before after end_ =>
  prefix_frame before (BArray2048.set8 after end_ value) end_.
proof.
move=> hend hf.
rewrite /prefix_frame => k hk.
rewrite BArray2048.get_setE 1:/# ifF 1:/#.
exact (hf k hk).
qed.

lemma prefix_frame_prepend_write before after start value :
  0 < start <= mode2_hbz_capacity =>
  prefix_frame before after start =>
  prefix_frame before
    (BArray2048.set8 after (start - 1) value) (start - 1).
proof.
move=> hstart hf.
rewrite /prefix_frame => k hk.
rewrite BArray2048.get_setE 1:/# ifF 1:/#.
apply hf; smt().
qed.

lemma w64_index_decrement_no_wrap i :
  0 < i < W64.modulus =>
  W64.to_uint (W64.of_int i - W64.one) = i - 1.
proof.
move=> hi.
have hirange : 0 <= i < W64.modulus by smt().
have hsmall : W64.to_uint (W64.of_int i) = i.
+ exact (W64.to_uint_small i hirange).
have hpos : 0 < W64.to_uint (W64.of_int i).
+ smt().
have hdec := cursor_decrement_no_underflow (W64.of_int i) hpos.
rewrite hsmall in hdec.
exact hdec.
qed.

lemma encode_trace_cons_state s tail :
  (encode_trace (s :: tail)).`1 =
    hbz_fast_encode_step
      (mode2_normalized_state (encode_trace tail).`1 s) s.
proof. trivial. qed.

lemma encode_trace_cons_bytes s tail :
  (encode_trace (s :: tail)).`2 =
    mode2_normalization_bytes (encode_trace tail).`1 s ++
    (encode_trace tail).`2.
proof. trivial. qed.

lemma mode2_normalization_bytes_size s x :
  0 <= s < mode2_hbz_alphabet =>
  rans_initial_state <= x < 2147483648 =>
  size (mode2_normalization_bytes x s) =
    mode2_normalization_len x s /\
  0 <= size (mode2_normalization_bytes x s) <= 2.
proof.
move=> hs hx.
rewrite /mode2_normalization_bytes /mode2_normalization_len
        /renorm_bytes /renorm_len.
case (x < hbz_xmax s) => h0; first trivial.
case (x %/ byte_radix < hbz_xmax s) => h1; trivial.
qed.

lemma encode_trace_suffix_extension a i :
  mode2_hbz_symbol_stream a =>
  0 <= i < mode2_hbz_count =>
  let s = W8.to_uint (BArray2048.get8 a i) in
  let tail = symbol_suffix a (i + 1) in
  (encode_trace (symbol_suffix a i)).`1 =
    hbz_fast_encode_step
      (mode2_normalized_state (encode_trace tail).`1 s) s /\
  (encode_trace (symbol_suffix a i)).`2 =
    mode2_normalization_bytes (encode_trace tail).`1 s ++
    (encode_trace tail).`2.
proof.
move=> hs hi.
rewrite (symbol_suffix_cons a i hi) /=.
trivial.
qed.

lemma encode_trace_suffix_state_bound a i :
  mode2_hbz_symbol_stream a =>
  0 <= i <= mode2_hbz_count =>
  rans_initial_state <= (encode_trace (symbol_suffix a i)).`1 < 2147483648.
proof.
move=> hs hi.
apply encode_trace_state_bounds.
exact (canonical_symbol_suffix a i hs hi).
qed.

lemma trace_cursor_extension a i off :
  mode2_hbz_symbol_stream a =>
  0 <= i < mode2_hbz_count =>
  off + size (encode_trace (symbol_suffix a (i + 1))).`2 =
    mode2_hbz_count =>
  size (mode2_normalization_bytes
      (encode_trace (symbol_suffix a (i + 1))).`1
      (W8.to_uint (BArray2048.get8 a i))) <= off =>
  off - size (mode2_normalization_bytes
      (encode_trace (symbol_suffix a (i + 1))).`1
      (W8.to_uint (BArray2048.get8 a i))) +
    size (encode_trace (symbol_suffix a i)).`2 =
    mode2_hbz_count.
proof.
move=> hs hi hoff hfit.
have [hstate hext] := encode_trace_suffix_extension a i hs hi.
rewrite hext size_cat.
smt().
qed.

lemma array_list_bridge_satisfiable :
  exists a,
    size (symbol_list_of_array a) = mode2_hbz_count /\
    symbol_suffix a mode2_hbz_count = [].
proof.
exists witness.
split; first exact (symbol_list_of_array_size witness).
exact (symbol_suffix_at_end witness).
qed.

end Mode2RansArrayListBridge.
