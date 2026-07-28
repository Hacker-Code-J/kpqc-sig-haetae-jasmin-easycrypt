require import AllCore IntDiv List Ring StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenSamplerCallersTarget KeygenEtaSamplerSpec
               KeygenShakeStreamSpec HAETAE_Keccak1600
               KeygenKeccak1600Spec TargetKeygenShakeStream.

theory TargetKeygenEtaSampler.

op eta_processed (values bytes : int list) (count : int) : int list =
  KeygenEtaSamplerSpec.eta_fill values (take count bytes).

op eta_extend_digits
    (values : int list) (byte digits : int) : int list =
  take KeygenEtaSamplerSpec.eta_poly_words_i
    (values ++ mkseq (KeygenEtaSamplerSpec.eta_centered_digit byte) digits).

op eta_partial_progress
    (a : BArray8192.t) (base ctr pos buflen : W64.t)
    (bp : BArray1024.t) (t : W32.t)
    (values bytes : int list) (base_i count byte digits : int) : bool =
  0 <= count < KeygenEtaSamplerSpec.eta_block_bytes_i /\
  1 <= digits <= KeygenEtaSamplerSpec.eta_digits_per_byte_i /\
  W64.to_uint pos = count + 1 /\
  byte = nth 0 bytes count /\
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i /\
  W64.to_uint base = base_i /\
  base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
    BArray8192.size %/ 4 /\
  buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
  size bytes = KeygenEtaSamplerSpec.eta_block_bytes_i /\
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i /\
  W64.to_uint ctr =
    size (eta_extend_digits (eta_processed values bytes count) byte digits) /\
  0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
  KeygenEtaSamplerSpec.eta_decoded_prefix8192 a base_i
    (eta_extend_digits (eta_processed values bytes count) byte digits) /\
  (digits < KeygenEtaSamplerSpec.eta_digits_per_byte_i /\
   W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i =>
    t = W32.of_int (byte %/ (3 ^ (digits - 1)))).

lemma eta_extend_digits_size_le values byte digits :
  size (eta_extend_digits values byte digits) <=
    KeygenEtaSamplerSpec.eta_poly_words_i.
proof.
rewrite /eta_extend_digits.
apply size_take_le.
by rewrite /KeygenEtaSamplerSpec.eta_poly_words_i.
qed.

lemma eta_extend_digits_zero values byte :
  size values <= KeygenEtaSamplerSpec.eta_poly_words_i =>
  eta_extend_digits values byte 0 = values.
proof.
move=> hsize.
by rewrite /eta_extend_digits mkseq0 cats0 take_oversize.
qed.

lemma eta_extend_digits_succ_lt values byte digits :
  0 <= digits =>
  size (eta_extend_digits values byte digits) <
    KeygenEtaSamplerSpec.eta_poly_words_i =>
  eta_extend_digits values byte (digits + 1) =
    rcons (eta_extend_digits values byte digits)
      (KeygenEtaSamplerSpec.eta_centered_digit byte digits).
proof.
move=> hdigits hlt.
rewrite /eta_extend_digits in hlt.
rewrite /eta_extend_digits.
rewrite mkseqS 1:hdigits -rcons_cat.
have hsource :
    size (values ++
      mkseq (KeygenEtaSamplerSpec.eta_centered_digit byte) digits) <
      KeygenEtaSamplerSpec.eta_poly_words_i.
+ case (KeygenEtaSamplerSpec.eta_poly_words_i <=
          size (values ++
            mkseq (KeygenEtaSamplerSpec.eta_centered_digit byte) digits))
      => hfull.
  + have htake :
      size (take KeygenEtaSamplerSpec.eta_poly_words_i
        (values ++
          mkseq (KeygenEtaSamplerSpec.eta_centered_digit byte) digits)) =
      KeygenEtaSamplerSpec.eta_poly_words_i.
    + rewrite size_takel.
      + exact hfull.
      by rewrite /KeygenEtaSamplerSpec.eta_poly_words_i.
    smt().
  smt().
rewrite !take_oversize 1:/# 1:/#.
trivial.
qed.

lemma eta_extend_digits_succ_full values byte digits :
  0 <= digits =>
  size (eta_extend_digits values byte digits) =
    KeygenEtaSamplerSpec.eta_poly_words_i =>
  eta_extend_digits values byte (digits + 1) =
    eta_extend_digits values byte digits.
proof.
move=> hdigits hfull.
rewrite /eta_extend_digits in hfull.
rewrite /eta_extend_digits.
rewrite mkseqS 1:hdigits -rcons_cat -cats1.
have hsource :
    KeygenEtaSamplerSpec.eta_poly_words_i <=
      size (values ++
        mkseq (KeygenEtaSamplerSpec.eta_centered_digit byte) digits).
+ rewrite size_take_condle 1:/# in hfull.
  smt().
by rewrite (take_catl
  (values ++ mkseq (KeygenEtaSamplerSpec.eta_centered_digit byte) digits)
  [KeygenEtaSamplerSpec.eta_centered_digit byte digits]
  KeygenEtaSamplerSpec.eta_poly_words_i hsource).
qed.

lemma eta_extend_digits_complete values byte :
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  eta_extend_digits values byte
      KeygenEtaSamplerSpec.eta_digits_per_byte_i =
    KeygenEtaSamplerSpec.eta_fill values [byte].
proof.
move=> hbyte.
rewrite /eta_extend_digits /KeygenEtaSamplerSpec.eta_fill
        KeygenEtaSamplerSpec.eta_decode_bytes_singleton
        KeygenEtaSamplerSpec.eta_decode_byte_accepted 1:hbyte.
trivial.
qed.

lemma eta_processed_zero values bytes :
  size values <= KeygenEtaSamplerSpec.eta_poly_words_i =>
  eta_processed values bytes 0 = values.
proof.
move=> hsize.
by rewrite /eta_processed take0 KeygenEtaSamplerSpec.eta_fill_nil.
qed.

lemma eta_processed_succ_accepted values bytes count :
  0 <= count < size bytes =>
  0 <= nth 0 bytes count < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  eta_processed values bytes (count + 1) =
    eta_extend_digits (eta_processed values bytes count)
      (nth 0 bytes count) KeygenEtaSamplerSpec.eta_digits_per_byte_i.
proof.
move=> hcount hbyte.
rewrite /eta_processed (take_nth 0 count bytes hcount)
        KeygenEtaSamplerSpec.eta_fill_rcons.
by rewrite eta_extend_digits_complete.
qed.

lemma eta_processed_succ_rejected values bytes count :
  0 <= count < size bytes =>
  !(0 <= nth 0 bytes count < KeygenEtaSamplerSpec.eta_accept_bound_i) =>
  eta_processed values bytes (count + 1) =
    eta_processed values bytes count.
proof.
move=> hcount hbyte.
rewrite /eta_processed (take_nth 0 count bytes hcount)
        KeygenEtaSamplerSpec.eta_fill_rcons.
rewrite KeygenEtaSamplerSpec.eta_fill_extension
  1:(KeygenEtaSamplerSpec.eta_fill_size_le values (take count bytes)).
rewrite KeygenEtaSamplerSpec.eta_decode_bytes_singleton
        KeygenEtaSamplerSpec.eta_decode_byte_rejected 1:hbyte /=.
+ trivial.
rewrite cats0.
trivial.
qed.

lemma eta_processed_size_le values bytes count :
  size (eta_processed values bytes count) <=
    KeygenEtaSamplerSpec.eta_poly_words_i.
proof.
rewrite /eta_processed.
exact (KeygenEtaSamplerSpec.eta_fill_size_le values (take count bytes)).
qed.

lemma eta_processed_full_suffix values bytes count :
  size (eta_processed values bytes count) =
    KeygenEtaSamplerSpec.eta_poly_words_i =>
  eta_processed values bytes (size bytes) =
    eta_processed values bytes count.
proof.
move=> hfull.
rewrite /eta_processed in hfull.
rewrite /eta_processed take_size.
have hcat := KeygenEtaSamplerSpec.eta_fill_cat
  values (take count bytes) (drop count bytes).
rewrite cat_take_drop in hcat.
rewrite KeygenEtaSamplerSpec.eta_fill_full 1:// in hcat.
by rewrite -hcat.
qed.

lemma eta_processed_terminal values bytes count :
  size (eta_processed values bytes count) =
      KeygenEtaSamplerSpec.eta_poly_words_i \/
    count = size bytes =>
  eta_processed values bytes count =
    KeygenEtaSamplerSpec.eta_fill values bytes.
proof.
case=> hterminal.
+ have hsuffix := eta_processed_full_suffix
    values bytes count hterminal.
  rewrite -hsuffix /eta_processed take_size.
  trivial.
by rewrite hterminal /eta_processed take_size.
qed.

lemma eta_extend_digits_prefix_succ
    a base_i (base ctr : W64.t) values byte digits w :
  0 <= digits =>
  W64.to_uint base = base_i =>
  base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
    BArray8192.size %/ 4 =>
  W64.to_uint ctr = size (eta_extend_digits values byte digits) =>
  W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i =>
  KeygenEtaSamplerSpec.eta_decoded_prefix8192
    a base_i (eta_extend_digits values byte digits) =>
  W32.to_sint w = KeygenEtaSamplerSpec.eta_centered_digit byte digits =>
  KeygenEtaSamplerSpec.eta_decoded_prefix8192
    (BArray8192.set32 a (W64.to_uint (base + ctr)) w)
    base_i (eta_extend_digits values byte (digits + 1)).
proof.
move=> hdigits hbase hcap hctr hctrlt hprefix hword.
rewrite eta_extend_digits_succ_lt 1:hdigits 1:/#.
apply (KeygenEtaSamplerSpec.eta_decoded_prefix8192_set32_word
  a base_i base ctr (eta_extend_digits values byte digits) w
  (KeygenEtaSamplerSpec.eta_centered_digit byte digits)).
+ exact hbase.
+ exact hcap.
+ exact hctr.
+ exact hctrlt.
+ exact hprefix.
exact hword.
qed.

lemma eta_extend_digits_size_succ values byte digits :
  0 <= digits =>
  size (eta_extend_digits values byte digits) <
    KeygenEtaSamplerSpec.eta_poly_words_i =>
  size (eta_extend_digits values byte (digits + 1)) =
    size (eta_extend_digits values byte digits) + 1.
proof.
move=> hdigits hsize.
by rewrite eta_extend_digits_succ_lt 1:hdigits 1:hsize size_rcons.
qed.

lemma eta_ctr_succ_uint (ctr : W64.t) :
  W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i =>
  W64.to_uint (ctr + W64.one) = W64.to_uint ctr + 1.
proof.
rewrite /KeygenEtaSamplerSpec.eta_poly_words_i.
move=> hctr.
by rewrite W64.to_uintD_small 1:/#.
qed.

lemma eta_partial_progress_skip
    a base ctr pos buflen bp t values bytes base_i count byte digits :
  eta_partial_progress a base ctr pos buflen bp t values bytes
    base_i count byte digits =>
  digits < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  !(W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i) =>
  eta_partial_progress a base ctr pos buflen bp t values bytes
    base_i count byte (digits + 1).
proof.
move=> hpartial hdigitslt hnotfull.
rewrite /eta_partial_progress in hpartial.
have hdigits0 : 0 <= digits by smt().
have hfull :
  size (eta_extend_digits (eta_processed values bytes count) byte digits) =
    KeygenEtaSamplerSpec.eta_poly_words_i by smt().
have hext := eta_extend_digits_succ_full
  (eta_processed values bytes count) byte digits hdigits0 hfull.
rewrite /eta_partial_progress.
rewrite hext.
by smt().
qed.

lemma eta_partial_progress_store_succ
    a base ctr pos buflen bp t t_after values bytes
    base_i count byte digits w :
  eta_partial_progress a base ctr pos buflen bp t values bytes
    base_i count byte digits =>
  digits < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i =>
  (digits + 1 < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
    t_after = W32.of_int (byte %/ (3 ^ digits))) =>
  W32.to_sint w = KeygenEtaSamplerSpec.eta_centered_digit byte digits =>
  eta_partial_progress
    (BArray8192.set32 a (W64.to_uint (base + ctr)) w)
    base (ctr + W64.one) pos buflen bp t_after values bytes
    base_i count byte (digits + 1).
proof.
move=> hpartial hdigitslt hctrlt ht_after hword.
rewrite /eta_partial_progress in hpartial.
have hdigits0 : 0 <= digits by smt().
have hbase : W64.to_uint base = base_i by smt().
have hcap :
  base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
    BArray8192.size %/ 4 by smt().
have hctr :
  W64.to_uint ctr =
    size (eta_extend_digits (eta_processed values bytes count) byte digits)
  by smt().
have hdecoded :
  KeygenEtaSamplerSpec.eta_decoded_prefix8192 a base_i
    (eta_extend_digits (eta_processed values bytes count) byte digits)
  by smt().
have hdecoded_next := eta_extend_digits_prefix_succ
  a base_i base ctr (eta_processed values bytes count) byte digits w
  hdigits0 hbase hcap hctr hctrlt hdecoded hword.
have hsize_next := eta_extend_digits_size_succ
  (eta_processed values bytes count) byte digits hdigits0 _.
+ by rewrite -hctr.
have hctr_next := eta_ctr_succ_uint ctr hctrlt.
have ht_next :
  digits + 1 < KeygenEtaSamplerSpec.eta_digits_per_byte_i /\
  W64.to_uint (ctr + W64.one) <
    KeygenEtaSamplerSpec.eta_poly_words_i =>
  t_after = W32.of_int (byte %/ (3 ^ (digits + 1 - 1))).
+ move=> [hmore _].
  have ht_after' := ht_after hmore.
  rewrite ht_after'.
  congr.
  by ring.
rewrite /eta_partial_progress.
by smt().
qed.

lemma eta_zeroextu32_word (byte : W8.t) :
  zeroextu32 byte = W32.of_int (W8.to_uint byte).
proof.
apply W32.to_uint_eq.
rewrite W4u8.to_uint_zeroextu32 W32.of_uintK /=.
have hbyte := W8.to_uint_cmp byte.
by rewrite modz_small 1:/#.
qed.

lemma eta_fips_byte_value bp bytes count :
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i =>
  0 <= count < KeygenEtaSamplerSpec.eta_block_bytes_i =>
  W8.to_uint (BArray1024.get8 bp count) = nth 0 bytes count.
proof.
rewrite /KeygenShakeStreamSpec.fips_rate_prefix_matches.
move=> hprefix hcount.
have hbyte := hprefix count hcount.
rewrite (_ : 0 + count = count) 1:/# in hbyte.
exact hbyte.
qed.

lemma eta_fips_byte_range bp bytes count :
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i =>
  0 <= count < KeygenEtaSamplerSpec.eta_block_bytes_i =>
  0 <= nth 0 bytes count <= 255.
proof.
move=> hprefix hcount.
have hbyte := eta_fips_byte_value bp bytes count hprefix hcount.
have hrange := W8.to_uint_cmp (BArray1024.get8 bp count).
by smt().
qed.

lemma eta_fips_byte_word bp bytes count :
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i =>
  0 <= count < KeygenEtaSamplerSpec.eta_block_bytes_i =>
  zeroextu32 (BArray1024.get8 bp count) =
    W32.of_int (nth 0 bytes count).
proof.
move=> hprefix hcount.
rewrite eta_zeroextu32_word.
by rewrite (eta_fips_byte_value bp bytes count hprefix hcount).
qed.

lemma eta_fips_pos_count_bound pos :
  pos \ult W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i =>
  0 <= W64.to_uint pos < KeygenEtaSamplerSpec.eta_block_bytes_i.
proof.
move=> hpos.
rewrite W64.ultE W64.of_uintK /= in hpos.
smt(W64.to_uint_cmp).
qed.

lemma eta_fips_accepted_range bp bytes pos :
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i =>
  pos \ult W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i =>
  zeroextu32 (BArray1024.get8 bp (W64.to_uint pos)) \ult
    W32.of_int KeygenEtaSamplerSpec.eta_accept_bound_i =>
  0 <= nth 0 bytes (W64.to_uint pos) <
    KeygenEtaSamplerSpec.eta_accept_bound_i.
proof.
move=> hprefix hpos haccept.
rewrite W32.ultE W4u8.to_uint_zeroextu32 W32.of_uintK /= in haccept.
rewrite modz_small 1:/# in haccept.
rewrite -(eta_fips_byte_value
  bp bytes (W64.to_uint pos) hprefix
  (eta_fips_pos_count_bound pos hpos)).
rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i.
smt(W8.to_uint_cmp).
qed.

lemma eta_fips_rejected_range bp bytes pos :
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i =>
  pos \ult W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i =>
  !(zeroextu32 (BArray1024.get8 bp (W64.to_uint pos)) \ult
    W32.of_int KeygenEtaSamplerSpec.eta_accept_bound_i) =>
  !(0 <= nth 0 bytes (W64.to_uint pos) <
    KeygenEtaSamplerSpec.eta_accept_bound_i).
proof.
move=> hprefix hpos hrejected.
rewrite W32.ultE W4u8.to_uint_zeroextu32 W32.of_uintK /= in hrejected.
rewrite modz_small 1:/# in hrejected.
rewrite -(eta_fips_byte_value
  bp bytes (W64.to_uint pos) hprefix
  (eta_fips_pos_count_bound pos hpos)).
rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i.
smt(W8.to_uint_cmp).
qed.

lemma eta_fips_accepted_facts bp bytes pos :
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i =>
  pos \ult W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i =>
  zeroextu32 (BArray1024.get8 bp (W64.to_uint pos)) \ult
    W32.of_int KeygenEtaSamplerSpec.eta_accept_bound_i =>
  0 <= W64.to_uint pos < KeygenEtaSamplerSpec.eta_block_bytes_i /\
  zeroextu32 (BArray1024.get8 bp (W64.to_uint pos)) =
    W32.of_int (nth 0 bytes (W64.to_uint pos)) /\
  0 <= nth 0 bytes (W64.to_uint pos) <= 255 /\
  0 <= nth 0 bytes (W64.to_uint pos) <
    KeygenEtaSamplerSpec.eta_accept_bound_i /\
  W8.to_uint (BArray1024.get8 bp (W64.to_uint pos)) =
    nth 0 bytes (W64.to_uint pos).
proof.
move=> hprefix hpos haccept.
split.
+ exact (eta_fips_pos_count_bound pos hpos).
split.
+ apply (eta_fips_byte_word bp bytes (W64.to_uint pos)).
  + exact hprefix.
  exact (eta_fips_pos_count_bound pos hpos).
split.
+ apply (eta_fips_byte_range bp bytes (W64.to_uint pos)).
  + exact hprefix.
  exact (eta_fips_pos_count_bound pos hpos).
split.
+ exact (eta_fips_accepted_range bp bytes pos hprefix hpos haccept).
apply (eta_fips_byte_value bp bytes (W64.to_uint pos)).
+ exact hprefix.
exact (eta_fips_pos_count_bound pos hpos).
qed.

lemma eta_fips_rejected_facts bp bytes pos :
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i =>
  size bytes = KeygenEtaSamplerSpec.eta_block_bytes_i =>
  pos \ult W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i =>
  !(zeroextu32 (BArray1024.get8 bp (W64.to_uint pos)) \ult
    W32.of_int KeygenEtaSamplerSpec.eta_accept_bound_i) =>
  0 <= W64.to_uint pos < size bytes /\
  0 <= nth 0 bytes (W64.to_uint pos) <= 255 /\
  zeroextu32 (BArray1024.get8 bp (W64.to_uint pos)) =
    W32.of_int (nth 0 bytes (W64.to_uint pos)) /\
  !(0 <= nth 0 bytes (W64.to_uint pos) <
    KeygenEtaSamplerSpec.eta_accept_bound_i).
proof.
move=> hprefix hbytes hpos hrejected.
split.
+ rewrite hbytes.
  exact (eta_fips_pos_count_bound pos hpos).
split.
+ apply (eta_fips_byte_range bp bytes (W64.to_uint pos)).
  + exact hprefix.
  exact (eta_fips_pos_count_bound pos hpos).
split.
+ apply (eta_fips_byte_word bp bytes (W64.to_uint pos)).
  + exact hprefix.
  exact (eta_fips_pos_count_bound pos hpos).
exact (eta_fips_rejected_range bp bytes pos hprefix hpos hrejected).
qed.

lemma eta_partial_progress_first
    a base ctr pos0 buflen bp t values bytes base_i count byte w :
  0 <= count < KeygenEtaSamplerSpec.eta_block_bytes_i =>
  W64.to_uint pos0 = count =>
  byte = nth 0 bytes count =>
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  t = W32.of_int byte =>
  W64.to_uint base = base_i =>
  base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
    BArray8192.size %/ 4 =>
  W64.to_uint ctr = size (eta_processed values bytes count) =>
  W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i =>
  KeygenEtaSamplerSpec.eta_decoded_prefix8192
    a base_i (eta_processed values bytes count) =>
  buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i =>
  size bytes = KeygenEtaSamplerSpec.eta_block_bytes_i =>
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i =>
  W32.to_sint w = KeygenEtaSamplerSpec.eta_centered_digit byte 0 =>
  eta_partial_progress
    (BArray8192.set32 a (W64.to_uint (base + ctr)) w)
    base (ctr + W64.one) (pos0 + W64.one) buflen bp t values bytes
    base_i count byte 1.
proof.
move=> hcount hpos hbyte hbyteok ht hbase hcap hctr hctrlt
        hdecoded hbuflen hbytes hprefix hword.
have hcurrentle := eta_processed_size_le values bytes count.
have hext0 := eta_extend_digits_zero
  (eta_processed values bytes count) byte hcurrentle.
have hdecoded_next := eta_extend_digits_prefix_succ
  a base_i base ctr (eta_processed values bytes count) byte 0 w
  _ hbase hcap _ hctrlt _ hword.
+ trivial.
+ by rewrite hext0.
+ by rewrite hext0.
have hsize_next := eta_extend_digits_size_succ
  (eta_processed values bytes count) byte 0 _ _.
+ trivial.
+ by rewrite hext0 -hctr.
have hctr_next := eta_ctr_succ_uint ctr hctrlt.
have hpos_next : W64.to_uint (pos0 + W64.one) = count + 1.
+ by rewrite W64.to_uintD_small 1:/# hpos.
have hctr_size_next :
  W64.to_uint (ctr + W64.one) =
    size (eta_extend_digits (eta_processed values bytes count) byte 1).
+ by rewrite hctr_next hsize_next hext0 hctr.
have ht_next :
  1 < KeygenEtaSamplerSpec.eta_digits_per_byte_i /\
  W64.to_uint (ctr + W64.one) <
    KeygenEtaSamplerSpec.eta_poly_words_i =>
  t = W32.of_int (byte %/ (3 ^ (1 - 1))).
+ move=> _.
  by rewrite ht /=.
rewrite /eta_partial_progress.
by smt().
qed.

lemma w32_shr_word (w : W32.t) i :
  0 <= i < 32 =>
  w `>>` W8.of_int i = W32.of_int (W32.to_uint w %/ 2 ^ i).
proof.
move=> hi.
rewrite -(W32.to_uintK' (w `>>` W8.of_int i)).
by rewrite W32.shr_div_le.
qed.

lemma w32_and3_word (w : W32.t) :
  w `&` W32.of_int 3 = W32.of_int (W32.to_uint w %% 4).
proof.
have h :
  w `&` W32.of_int (2 ^ 2 - 1) =
  W32.of_int (W32.to_uint w %% 2 ^ 2).
+ by apply W32.and_mod; smt().
by move: h => /=.
qed.

lemma w32_and15_word (w : W32.t) :
  w `&` W32.of_int 15 = W32.of_int (W32.to_uint w %% 16).
proof.
have h :
  w `&` W32.of_int (2 ^ 4 - 1) =
  W32.of_int (W32.to_uint w %% 2 ^ 4).
+ by apply W32.and_mod; smt().
by move: h => /=.
qed.

lemma div3_step_word (w : W32.t) :
  W32.to_uint w <= 242 =>
  (w * W32.of_int 171) `>>` W8.of_int 9 =
  W32.of_int (W32.to_uint w %/ 3).
proof.
move=> hw.
rewrite w32_shr_word 1:/# W32.to_uintM W32.of_uintK /=.
rewrite modz_small 1:/#.
congr.
by apply KeygenEtaSamplerSpec.div3_via_171; smt(W32.to_uint_cmp).
qed.

lemma eta_div3_digit_step_word (w : W32.t) byte digit :
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i =>
  0 <= digit =>
  w = W32.of_int (byte %/ (3 ^ digit)) =>
  (w * W32.of_int 171) `>>` W8.of_int 9 =
    W32.of_int (byte %/ (3 ^ (digit + 1))).
proof.
move=> hbyte hdigit ->.
rewrite div3_step_word.
+ rewrite KeygenEtaSamplerSpec.eta_accepted_quotient_word 1:hbyte 1:hdigit.
  have hrange :=
    KeygenEtaSamplerSpec.eta_accepted_quotient_range
      byte digit hbyte hdigit.
  smt().
rewrite KeygenEtaSamplerSpec.eta_accepted_quotient_word 1:hbyte 1:hdigit.
by rewrite KeygenEtaSamplerSpec.eta_div3_digit_succ.
qed.

lemma eta_centered_digit_word (w : W32.t) byte digit :
  W32.to_uint w = byte %/ (3 ^ digit) =>
  W32.to_sint (KeygenEtaSamplerSpec.centered_trit w) =
    KeygenEtaSamplerSpec.eta_centered_digit byte digit.
proof.
move=> hword.
rewrite -(W32.to_uintK' w) hword.
exact (KeygenEtaSamplerSpec.eta_centered_digit_to_sint byte digit).
qed.

lemma eta_partial_progress_div3_store
    a base ctr pos buflen bp t values bytes base_i count byte digits :
  eta_partial_progress a base ctr pos buflen bp t values bytes
    base_i count byte digits =>
  digits < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i =>
  eta_partial_progress
    (BArray8192.set32 a (W64.to_uint (base + ctr))
      (KeygenEtaSamplerSpec.centered_trit
        ((t * W32.of_int 171) `>>` W8.of_int 9)))
    base (ctr + W64.one) pos buflen bp
    ((t * W32.of_int 171) `>>` W8.of_int 9)
    values bytes base_i count byte (digits + 1).
proof.
move=> hpartial hdigitslt hctrlt.
have hinfo := hpartial.
rewrite /eta_partial_progress
        /KeygenEtaSamplerSpec.eta_digits_per_byte_i in hinfo.
have hbyte :
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i by smt().
have hdigit0 : 0 <= digits - 1 by smt().
have ht : t = W32.of_int (byte %/ (3 ^ (digits - 1))) by smt().
have hq0 := eta_div3_digit_step_word
  t byte (digits - 1) hbyte hdigit0 ht.
have hq :
  (t * W32.of_int 171) `>>` W8.of_int 9 =
    W32.of_int (byte %/ (3 ^ digits)).
+ rewrite hq0.
  congr.
  by ring.
have hword :
  W32.to_sint
    (KeygenEtaSamplerSpec.centered_trit
      ((t * W32.of_int 171) `>>` W8.of_int 9)) =
    KeygenEtaSamplerSpec.eta_centered_digit byte digits.
+ apply eta_centered_digit_word.
  rewrite hq.
  apply KeygenEtaSamplerSpec.eta_accepted_quotient_word.
  + exact hbyte.
  smt().
apply (eta_partial_progress_store_succ
  a base ctr pos buflen bp t
  ((t * W32.of_int 171) `>>` W8.of_int 9)
  values bytes base_i count byte digits
  (KeygenEtaSamplerSpec.centered_trit
    ((t * W32.of_int 171) `>>` W8.of_int 9))).
+ exact hpartial.
+ exact hdigitslt.
+ exact hctrlt.
+ move=> _.
  exact hq.
exact hword.
qed.

lemma eta_partial_progress_active_t_uint
    a base ctr pos buflen bp t values bytes base_i count byte digits :
  eta_partial_progress a base ctr pos buflen bp t values bytes
    base_i count byte digits =>
  digits < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i =>
  W32.to_uint t = byte %/ (3 ^ (digits - 1)).
proof.
move=> hpartial hdigitslt hctrlt.
have hinfo := hpartial.
rewrite /eta_partial_progress
        /KeygenEtaSamplerSpec.eta_digits_per_byte_i in hinfo.
have hbyte :
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i by smt().
have hdigit0 : 0 <= digits - 1 by smt().
have ht : t = W32.of_int (byte %/ (3 ^ (digits - 1))) by smt().
rewrite ht.
exact (KeygenEtaSamplerSpec.eta_accepted_quotient_word
  byte (digits - 1) hbyte hdigit0).
qed.

lemma div3_step_uint (w : W32.t) :
  W32.to_uint w <= 242 =>
  W32.to_uint ((w * W32.of_int 171) `>>` W8.of_int 9) =
    W32.to_uint w %/ 3.
proof.
move=> hw.
rewrite div3_step_word 1:hw W32.of_uintK.
rewrite modz_small.
+ smt(W32.to_uint_cmp divz_ge0).
smt(W32.to_uint_cmp divz_ge0).
qed.

lemma div3_step_leq80 (w : W32.t) :
  W32.to_uint w <= 242 =>
  W32.to_uint ((w * W32.of_int 171) `>>` W8.of_int 9) <= 80.
proof.
move=> hw.
rewrite div3_step_uint 1:hw.
smt(W32.to_uint_cmp divz_cmp).
qed.

lemma div3_step_leq26 (w : W32.t) :
  W32.to_uint w <= 80 =>
  W32.to_uint ((w * W32.of_int 171) `>>` W8.of_int 9) <= 26.
proof.
move=> hw.
rewrite div3_step_uint 1:/#.
smt(W32.to_uint_cmp divz_cmp).
qed.

lemma div3_step_leq8 (w : W32.t) :
  W32.to_uint w <= 26 =>
  W32.to_uint ((w * W32.of_int 171) `>>` W8.of_int 9) <= 8.
proof.
move=> hw.
rewrite div3_step_uint 1:/#.
smt(W32.to_uint_cmp divz_cmp).
qed.

lemma eta_digits_stage1_lt :
  1 < KeygenEtaSamplerSpec.eta_digits_per_byte_i.
proof. by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i. qed.

lemma eta_digits_stage2_lt :
  2 < KeygenEtaSamplerSpec.eta_digits_per_byte_i.
proof. by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i. qed.

lemma eta_digits_stage3_lt :
  3 < KeygenEtaSamplerSpec.eta_digits_per_byte_i.
proof. by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i. qed.

lemma eta_partial_progress_digit1_bound
    a base ctr pos buflen bp t values bytes base_i count byte :
  eta_partial_progress a base ctr pos buflen bp t values bytes
    base_i count byte 1 =>
  W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i =>
  W32.to_uint ((t * W32.of_int 171) `>>` W8.of_int 9) <= 80.
proof.
move=> hpartial hctrlt.
move: (eta_partial_progress_active_t_uint
  a base ctr pos buflen bp t values bytes base_i count byte 1
  hpartial eta_digits_stage1_lt hctrlt) => htuint.
rewrite /eta_partial_progress in hpartial.
apply div3_step_leq80.
move: htuint => /= htuint.
rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i in hpartial.
smt().
qed.

lemma eta_partial_progress_digit2_bound
    a base ctr pos buflen bp t values bytes base_i count byte :
  eta_partial_progress a base ctr pos buflen bp t values bytes
    base_i count byte 2 =>
  W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i =>
  W32.to_uint ((t * W32.of_int 171) `>>` W8.of_int 9) <= 26.
proof.
move=> hpartial hctrlt.
move: (eta_partial_progress_active_t_uint
  a base ctr pos buflen bp t values bytes base_i count byte 2
  hpartial eta_digits_stage2_lt hctrlt) => htuint.
rewrite /eta_partial_progress in hpartial.
apply div3_step_leq26.
move: htuint => /= htuint.
rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i in hpartial.
smt(divz_cmp).
qed.

lemma eta_partial_progress_digit3_bound
    a base ctr pos buflen bp t values bytes base_i count byte :
  eta_partial_progress a base ctr pos buflen bp t values bytes
    base_i count byte 3 =>
  W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i =>
  W32.to_uint ((t * W32.of_int 171) `>>` W8.of_int 9) <= 8.
proof.
move=> hpartial hctrlt.
move: (eta_partial_progress_active_t_uint
  a base ctr pos buflen bp t values bytes base_i count byte 3
  hpartial eta_digits_stage3_lt hctrlt) => htuint.
rewrite /eta_partial_progress in hpartial.
apply div3_step_leq8.
move: htuint => /= htuint.
rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i in hpartial.
smt(divz_cmp).
qed.

lemma div3_step_leq2 (w : W32.t) :
  W32.to_uint w <= 8 =>
  W32.to_uint ((w * W32.of_int 171) `>>` W8.of_int 9) <= 2.
proof.
move=> hw.
rewrite div3_step_uint 1:/#.
smt(W32.to_uint_cmp divz_cmp).
qed.

lemma last_trit_word (w : W32.t) :
  W32.to_uint w <= 2 =>
  w - (w `>>` W8.of_int 1) * W32.of_int 3 =
  KeygenEtaSamplerSpec.centered_trit w.
proof.
move=> hw.
rewrite -(W32.to_uintK' w).
rewrite w32_shr_word 1:/#.
rewrite !W32.of_intM' !W32.of_intS'.
rewrite /KeygenEtaSamplerSpec.centered_trit
        /KeygenEtaSamplerSpec.centered_trit_value
        /KeygenEtaSamplerSpec.base3_residue.
rewrite !W32.of_uintK.
congr.
smt(W32.to_uint_cmp modz_cmp).
qed.

lemma eta_partial_progress_last_store
    a base ctr pos buflen bp t values bytes base_i count byte :
  eta_partial_progress a base ctr pos buflen bp t values bytes
    base_i count byte 4 =>
  W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i =>
  let q = (t * W32.of_int 171) `>>` W8.of_int 9 in
  let w = q - (q `>>` W8.of_int 1) * W32.of_int 3 in
  eta_partial_progress
    (BArray8192.set32 a (W64.to_uint (base + ctr)) w)
    base (ctr + W64.one) pos buflen bp w values bytes
    base_i count byte KeygenEtaSamplerSpec.eta_digits_per_byte_i.
proof.
move=> hpartial hctrlt /=.
have hinfo := hpartial.
rewrite /eta_partial_progress
        /KeygenEtaSamplerSpec.eta_digits_per_byte_i in hinfo.
have hbyte :
  0 <= byte < KeygenEtaSamplerSpec.eta_accept_bound_i by smt().
move: hinfo =>
  [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ htail]]]]]]]]]]]]].
have ht := htail _.
+ split; first trivial.
  exact hctrlt.
move: ht => /= ht.
have hq := eta_div3_digit_step_word t byte 3 hbyte _ ht.
+ smt().
have htuint : W32.to_uint t = byte %/ 27.
+ rewrite ht /=.
  have hw := KeygenEtaSamplerSpec.eta_accepted_quotient_word
    byte 3 hbyte _.
  + smt().
  by move: hw => /=.
have ht8 : W32.to_uint t <= 8.
+ rewrite htuint.
  rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i in hbyte.
  smt(divz_cmp).
have hqle := div3_step_leq2 t ht8.
have hlast := last_trit_word
  ((t * W32.of_int 171) `>>` W8.of_int 9) hqle.
have hword :
  W32.to_sint
    (((t * W32.of_int 171) `>>` W8.of_int 9) -
      (((t * W32.of_int 171) `>>` W8.of_int 9) `>>` W8.of_int 1) *
        W32.of_int 3) =
    KeygenEtaSamplerSpec.eta_centered_digit byte 4.
+ rewrite hlast.
  apply eta_centered_digit_word.
  rewrite hq.
  apply KeygenEtaSamplerSpec.eta_accepted_quotient_word.
  + exact hbyte.
  smt().
apply (eta_partial_progress_store_succ
  a base ctr pos buflen bp t
  (((t * W32.of_int 171) `>>` W8.of_int 9) -
    (((t * W32.of_int 171) `>>` W8.of_int 9) `>>` W8.of_int 1) *
      W32.of_int 3)
  values bytes base_i count byte 4
  (((t * W32.of_int 171) `>>` W8.of_int 9) -
    (((t * W32.of_int 171) `>>` W8.of_int 9) `>>` W8.of_int 1) *
      W32.of_int 3)).
+ exact hpartial.
+ rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
  smt().
+ exact hctrlt.
+ rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
  smt().
exact hword.
qed.

lemma eta_partial_progress_complete_processed
    a base ctr pos buflen bp t values bytes base_i count byte :
  eta_partial_progress a base ctr pos buflen bp t values bytes
    base_i count byte KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  eta_processed values bytes (W64.to_uint pos) =
    eta_extend_digits (eta_processed values bytes count) byte
      KeygenEtaSamplerSpec.eta_digits_per_byte_i.
proof.
move=> hpartial.
rewrite /eta_partial_progress in hpartial.
have hpos : W64.to_uint pos = count + 1 by smt().
have hbyteeq : byte = nth 0 bytes count by smt().
have hsucc := eta_processed_succ_accepted values bytes count _ _.
+ smt().
+ smt().
rewrite hpos hbyteeq.
exact hsucc.
qed.

lemma mod3_full_correct (input : W32.t) :
  hoare [KeygenSamplerCallersTarget.M.__poly_sample_mod3 :
    t = input /\ W32.to_uint input <= 242 ==>
    res = KeygenEtaSamplerSpec.centered_trit input].
proof.
proc.
wp.
skip => &hr hbound /=.
move: hbound => [-> hbound].
rewrite /KeygenEtaSamplerSpec.centered_trit.
rewrite !w32_shr_word 1..5:/#.
rewrite !w32_and15_word.
rewrite !w32_and3_word.
rewrite !W32.of_intD' !W32.of_intM' !W32.of_intS'.
congr.
rewrite /KeygenEtaSamplerSpec.centered_trit_value
        /KeygenEtaSamplerSpec.base3_residue.
rewrite !W32.of_uintK.
smt(W32.to_uint_cmp modz_cmp divz_ge0).
qed.

lemma mod3_leq26_correct (input : W32.t) :
  hoare [KeygenSamplerCallersTarget.M.__poly_sample_mod3_leq26 :
    t = input /\ W32.to_uint input <= 26 ==>
    res = KeygenEtaSamplerSpec.centered_trit input].
proof.
proc.
wp.
skip => &hr hbound /=.
move: hbound => [-> hbound].
rewrite /KeygenEtaSamplerSpec.centered_trit.
rewrite !w32_shr_word 1..4:/#.
rewrite !w32_and15_word !w32_and3_word.
rewrite !W32.of_intD' !W32.of_intM' !W32.of_intS'.
congr.
rewrite /KeygenEtaSamplerSpec.centered_trit_value
        /KeygenEtaSamplerSpec.base3_residue.
rewrite !W32.of_uintK.
smt(W32.to_uint_cmp modz_cmp divz_ge0).
qed.

lemma mod3_leq8_correct (input : W32.t) :
  hoare [KeygenSamplerCallersTarget.M.__poly_sample_mod3_leq8 :
    t = input /\ W32.to_uint input <= 8 ==>
    res = KeygenEtaSamplerSpec.centered_trit input].
proof.
proc.
wp.
skip => &hr hbound /=.
move: hbound => [-> hbound].
rewrite /KeygenEtaSamplerSpec.centered_trit.
rewrite !w32_shr_word 1..3:/#.
rewrite !w32_and3_word.
rewrite !W32.of_intD' !W32.of_intM' !W32.of_intS'.
congr.
rewrite /KeygenEtaSamplerSpec.centered_trit_value
        /KeygenEtaSamplerSpec.base3_residue.
rewrite !W32.of_uintK.
smt(W32.to_uint_cmp modz_cmp divz_ge0).
qed.

lemma eta_consume2048_block136 bytes values0 base_i :
  hoare [KeygenSamplerCallersTarget.M.__kp_poly_uniform_eta_consume_2048 :
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4 /\
    W64.to_uint ctr = size values0 /\
    0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
    KeygenEtaSamplerSpec.eta_decoded_prefix8192 ap base_i values0 /\
    buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
    size bytes = KeygenEtaSamplerSpec.eta_block_bytes_i /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i
    ==>
    W64.to_uint res.`2 =
      size (KeygenEtaSamplerSpec.eta_fill values0 bytes) /\
    0 <= W64.to_uint res.`2 <= KeygenEtaSamplerSpec.eta_poly_words_i /\
    KeygenEtaSamplerSpec.eta_decoded_prefix8192
      res.`1 base_i (KeygenEtaSamplerSpec.eta_fill values0 bytes)].
proof.
proc.
while (
    0 <= W64.to_uint pos <= KeygenEtaSamplerSpec.eta_block_bytes_i /\
    W64.to_uint ctr =
      size (eta_processed values0 bytes (W64.to_uint pos)) /\
    KeygenEtaSamplerSpec.eta_decoded_prefix8192 ap base_i
      (eta_processed values0 bytes (W64.to_uint pos)) /\
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4 /\
    buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
    size bytes = KeygenEtaSamplerSpec.eta_block_bytes_i /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i /\
    0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
    (live = W64.zero =>
      W64.to_uint ctr = KeygenEtaSamplerSpec.eta_poly_words_i \/
      W64.to_uint pos = KeygenEtaSamplerSpec.eta_block_bytes_i)).
+ if.
  + auto => />.
    move=> &hr hpos0 hposle hctr hdecoded hcap hbytes hprefix
            hctr0 hctrle hstop hlive hfull.
    rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
            W64.uleE W64.of_uintK /= in hfull.
    left; smt(W64.to_uint_cmp).
  if.
  + sp 5.
    if.
    + seq 5 :
        (exists count bytev,
          eta_partial_progress ap base ctr pos buflen bp t values0 bytes
            base_i count bytev 1 /\
          live <> W64.zero).
      + wp.
        exlim t => t0.
        call (mod3_full_correct t0).
        + auto => />.
        + auto => />.
          move=> &hr pos0 hpos0 hposle hctr hdecoded hcap hbytes hprefix
                  hctr0 hctrle hstop hlive hnotfull hposguard haccept.
          rewrite /protect_32 in haccept.
          rewrite /protect_32.
          move: (eta_fips_accepted_facts
            bp{hr} bytes pos0 hprefix hposguard haccept) =>
            [hcount [htword [hbr [hbyteok hbyteval]]]].
          split.
          + rewrite htword W32.of_uintK /= modz_small 1:/#.
            rewrite /KeygenEtaSamplerSpec.eta_accept_bound_i in hbyteok.
            smt().
          move=> _.
          exists (W64.to_uint pos0) (nth 0 bytes (W64.to_uint pos0)).
          apply (eta_partial_progress_first
            ap{hr} base{hr} ctr{hr} pos0
            (W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i) bp{hr}
            (zeroextu32
              (BArray1024.get8 bp{hr} (W64.to_uint pos0)))
            values0 bytes (W64.to_uint base{hr}) (W64.to_uint pos0)
            (nth 0 bytes (W64.to_uint pos0))
            (KeygenEtaSamplerSpec.centered_trit
              (zeroextu32
                (BArray1024.get8 bp{hr} (W64.to_uint pos0))))).
          + exact hcount.
          + trivial.
          + trivial.
          + exact hbyteok.
          + exact htword.
          + trivial.
          + exact hcap.
          + exact hctr.
          + rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                    W64.uleE W64.of_uintK /= in hnotfull.
            smt().
          + exact hdecoded.
          + trivial.
          + exact hbytes.
          + exact hprefix.
          + apply eta_centered_digit_word.
            rewrite W4u8.to_uint_zeroextu32 /=
              hbyteval.
            trivial.
      seq 1 :
        (exists count bytev,
          eta_partial_progress ap base ctr pos buflen bp t values0 bytes
            base_i count bytev 2 /\
          live <> W64.zero).
      + if.
        + wp.
          exlim t => t1.
          call (mod3_full_correct
            ((t1 * W32.of_int 171) `>>` W8.of_int 9)).
          + auto.
          + auto => &hr [ht1 [[count bytev [hpartial hlive]] hguard]].
            subst t1.
            rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                    W64.ultE W64.of_uintK /= in hguard.
            move: (eta_partial_progress_digit1_bound
              ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
              values0 bytes base_i count bytev
              hpartial hguard) => hq80.
            split.
            + smt().
            move=> _ out hout.
            subst out.
            exists count bytev.
            split.
            + exact (eta_partial_progress_div3_store
                ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
                values0 bytes base_i count bytev 1
                hpartial eta_digits_stage1_lt hguard).
            exact hlive.
        + auto => &hr [[count bytev [hpartial hlive]] hguard].
          rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                  W64.ultE W64.of_uintK /= in hguard.
          exists count bytev.
          split.
          + exact (eta_partial_progress_skip
              ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
              values0 bytes base_i count bytev 1
              hpartial eta_digits_stage1_lt hguard).
          exact hlive.
      seq 1 :
        (exists count bytev,
          eta_partial_progress ap base ctr pos buflen bp t values0 bytes
            base_i count bytev 3 /\
          live <> W64.zero).
      + if.
        + wp.
          exlim t => t2.
          call (mod3_leq26_correct
            ((t2 * W32.of_int 171) `>>` W8.of_int 9)).
          + auto.
          + auto => &hr [ht2 [[count bytev [hpartial hlive]] hguard]].
            subst t2.
            rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                    W64.ultE W64.of_uintK /= in hguard.
            move: (eta_partial_progress_digit2_bound
              ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
              values0 bytes base_i count bytev
              hpartial hguard) => hq26.
            split.
            + smt().
            move=> _ out hout.
            subst out.
            exists count bytev.
            split.
            + exact (eta_partial_progress_div3_store
                ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
                values0 bytes base_i count bytev 2
                hpartial eta_digits_stage2_lt hguard).
            exact hlive.
        + auto => &hr [[count bytev [hpartial hlive]] hguard].
          rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                  W64.ultE W64.of_uintK /= in hguard.
          exists count bytev.
          split.
          + exact (eta_partial_progress_skip
              ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
              values0 bytes base_i count bytev 2
              hpartial eta_digits_stage2_lt hguard).
          exact hlive.
      seq 1 :
        (exists count bytev,
          eta_partial_progress ap base ctr pos buflen bp t values0 bytes
            base_i count bytev 4 /\
          live <> W64.zero).
      + if.
        + wp.
          exlim t => t3.
          call (mod3_leq8_correct
            ((t3 * W32.of_int 171) `>>` W8.of_int 9)).
          + auto.
          + auto => &hr [ht3 [[count bytev [hpartial hlive]] hguard]].
            subst t3.
            rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                    W64.ultE W64.of_uintK /= in hguard.
            move: (eta_partial_progress_digit3_bound
              ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
              values0 bytes base_i count bytev
              hpartial hguard) => hq8.
            split.
            + smt().
            move=> _ out hout.
            subst out.
            exists count bytev.
            split.
            + exact (eta_partial_progress_div3_store
                ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
                values0 bytes base_i count bytev 3
                hpartial eta_digits_stage3_lt hguard).
            exact hlive.
        + auto => &hr [[count bytev [hpartial hlive]] hguard].
          rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                  W64.ultE W64.of_uintK /= in hguard.
          exists count bytev.
          split.
          + exact (eta_partial_progress_skip
              ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
              values0 bytes base_i count bytev 3
              hpartial eta_digits_stage3_lt hguard).
          exact hlive.
      seq 1 :
        (exists count bytev,
          eta_partial_progress ap base ctr pos buflen bp t values0 bytes
            base_i count bytev
              KeygenEtaSamplerSpec.eta_digits_per_byte_i /\
          live <> W64.zero).
      + if.
        + auto => &hr [[count bytev [hpartial hlive]] hguard].
          rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                  W64.ultE W64.of_uintK /= in hguard.
          exists count bytev.
          split.
          + exact (eta_partial_progress_last_store
              ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
              values0 bytes base_i count bytev hpartial hguard).
          exact hlive.
        + auto => &hr [[count bytev [hpartial hlive]] hguard].
          rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                  W64.ultE W64.of_uintK /= in hguard.
          exists count bytev.
          split.
          + have hdigits4 :
              4 < KeygenEtaSamplerSpec.eta_digits_per_byte_i
                by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
            exact (eta_partial_progress_skip
              ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
              values0 bytes base_i count bytev 4
              hpartial hdigits4 hguard).
          exact hlive.
      skip.
      move=> &hr [count bytev [hpartial hlive]].
      rewrite (eta_partial_progress_complete_processed
        ap{hr} base{hr} ctr{hr} pos{hr} buflen{hr} bp{hr} t{hr}
        values0 bytes base_i count bytev) 1:hpartial.
      rewrite /eta_partial_progress in hpartial.
      by smt().
    + auto => />.
      move=> &hr pos0 hpos0 hposle hctr hdecoded hcap hbytes hprefix
              hctr0 hctrle hstop hlive hnotfull hposguard hrejected.
      rewrite /protect_32 in hrejected.
      move: (eta_fips_rejected_facts
        bp{hr} bytes pos0 hprefix hbytes hposguard hrejected) =>
        [hcount_size [hbr [htword hbad]]].
      rewrite W64.to_uintD_small 1:/#.
      rewrite (eta_processed_succ_rejected
        values0 bytes (W64.to_uint pos0) hcount_size hbad).
      by smt().
  + auto => />.
    move=> &hr hpos0 hposle hctr hdecoded hcap hbytes hprefix
            hctr0 hctrle hstop hlive hnotfull hposguard.
    rewrite /KeygenEtaSamplerSpec.eta_block_bytes_i
            W64.ultE W64.of_uintK /= in hposguard.
    right; smt().
wp.
skip => &hr
  [hbase [hcap [hctr [[hctr0 hctrle]
    [hdecoded [hbuflen [hbytes hprefix]]]]]]].
split.
+ rewrite /= eta_processed_zero 1:/#.
  by smt().
move=> apf ctrf livef posf hdone hinv.
have hlive0 : livef = W64.zero by exact hdone.
move: hinv =>
  [_ [hctrf [hdecodedf [_ [_ [_ [hbytesf
    [_ [[hctrf0 hctrfle] hstop]]]]]]]]].
suff <- :
  eta_processed values0 bytes (W64.to_uint posf) =
    KeygenEtaSamplerSpec.eta_fill values0 bytes.
+ split; first exact hctrf.
  split; first smt().
  exact hdecodedf.
apply eta_processed_terminal.
case: (hstop hlive0) => hstopf.
+ left.
  rewrite -hctrf.
  exact hstopf.
+ right.
  rewrite hbytesf.
  exact hstopf.
qed.

lemma eta_consume2048_counter ctr0 :
  hoare [KeygenSamplerCallersTarget.M.__kp_poly_uniform_eta_consume_2048 :
    ctr = ctr0 /\
    W64.to_uint ctr0 <= KeygenEtaSamplerSpec.eta_poly_words_i
    ==>
    W64.to_uint ctr0 <= W64.to_uint res.`2 <=
      KeygenEtaSamplerSpec.eta_poly_words_i].
proof.
proc.
inline KeygenSamplerCallersTarget.M.__poly_sample_mod3
       KeygenSamplerCallersTarget.M.__poly_sample_mod3_leq26
       KeygenSamplerCallersTarget.M.__poly_sample_mod3_leq8.
while (W64.to_uint ctr0 <= W64.to_uint ctr <=
         KeygenEtaSamplerSpec.eta_poly_words_i).
+ auto => /> &hr hlow hhigh.
  rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
          !W64.uleE !W64.ultE.
  do 5! (rewrite W64.to_uintD_small 1:/#).
  smt(W64.to_uint_cmp).
wp.
by skip => />.
qed.

lemma eta_consume2048_centered base_i :
  hoare [KeygenSamplerCallersTarget.M.__kp_poly_uniform_eta_consume_2048 :
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4 /\
    0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
    KeygenEtaSamplerSpec.centered_interval8192
      ap base_i 0 (W64.to_uint ctr)
    ==>
    0 <= W64.to_uint res.`2 <= KeygenEtaSamplerSpec.eta_poly_words_i /\
    KeygenEtaSamplerSpec.centered_interval8192
      res.`1 base_i 0 (W64.to_uint res.`2)].
proof.
proc.
while (KeygenEtaSamplerSpec.centered_interval8192
         ap base_i 0 (W64.to_uint ctr) /\
       W64.to_uint base = base_i /\
       base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
         BArray8192.size %/ 4 /\
       0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i).
+ if.
  + by auto.
  if.
  + sp 5.
    if.
      + seq 5 :
        (KeygenEtaSamplerSpec.centered_interval8192
           ap base_i 0 (W64.to_uint ctr) /\
         W64.to_uint base = base_i /\
         base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
           BArray8192.size %/ 4 /\
         0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
         W32.to_uint t <= 242).
      + wp.
        exlim t => t0.
        call (mod3_full_correct t0).
        + auto => />.
          move=> &hr pos0 hrange hcap hctr0 hctrle
                  hlive hnotfull hpos haccept.
          split.
          + rewrite W32.ultE W32.of_uintK /= in haccept.
            smt().
          move=> _.
          have hctrlt :
            W64.to_uint ctr{hr} <
              KeygenEtaSamplerSpec.eta_poly_words_i.
          + rewrite /KeygenEtaSamplerSpec.eta_poly_words_i.
            rewrite W64.uleE W64.of_uintK /= in hnotfull.
            smt().
          have hctr_succ :
            W64.to_uint (ctr{hr} + W64.one) =
              W64.to_uint ctr{hr} + 1
            by rewrite W64.to_uintD_small 1:/#.
          split.
          + rewrite hctr_succ.
            apply (KeygenEtaSamplerSpec.centered_interval8192_set32_word
                     ap{hr} (W64.to_uint base{hr})
                     base{hr} ctr{hr} _).
            + trivial.
            + exact hcap.
            + exact hctrlt.
            + exact hrange.
            exact (KeygenEtaSamplerSpec.centered_trit_range _).
          rewrite hctr_succ
                  /KeygenEtaSamplerSpec.eta_poly_words_i.
          smt(W64.to_uint_cmp).
      seq 1 :
        (KeygenEtaSamplerSpec.centered_interval8192
           ap base_i 0 (W64.to_uint ctr) /\
         W64.to_uint base = base_i /\
         base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
           BArray8192.size %/ 4 /\
         0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
         (ctr \ult W64.of_int 256 => W32.to_uint t <= 80)).
      + if.
        + wp.
          exlim t => t1.
          call (mod3_full_correct
                  ((t1 * W32.of_int 171) `>>` W8.of_int 9)).
          + auto => />.
          + auto => />.
            move=> &hr hrange hcap hctr0 hctrle ht hguard.
            have hq80 := div3_step_leq80 t1 ht.
            split.
            + smt().
            move=> _.
            have hctrlt :
              W64.to_uint ctr{hr} <
                KeygenEtaSamplerSpec.eta_poly_words_i.
            + rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                      W64.ultE W64.of_uintK /= in hguard.
              exact hguard.
            have hctr_succ :
              W64.to_uint (ctr{hr} + W64.one) =
                W64.to_uint ctr{hr} + 1
              by rewrite W64.to_uintD_small 1:/#.
            split.
            + rewrite hctr_succ.
              apply (KeygenEtaSamplerSpec.centered_interval8192_set32_word
                       ap{hr} (W64.to_uint base{hr})
                       base{hr} ctr{hr} _).
              + trivial.
              + exact hcap.
              + exact hctrlt.
              + exact hrange.
              exact (KeygenEtaSamplerSpec.centered_trit_range _).
            split.
            + rewrite hctr_succ
                      /KeygenEtaSamplerSpec.eta_poly_words_i.
              smt(W64.to_uint_cmp).
            move=> _.
            exact hq80.
        + by auto => />.
      seq 1 :
        (KeygenEtaSamplerSpec.centered_interval8192
           ap base_i 0 (W64.to_uint ctr) /\
         W64.to_uint base = base_i /\
         base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
           BArray8192.size %/ 4 /\
         0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
         (ctr \ult W64.of_int 256 => W32.to_uint t <= 26)).
      + if.
        + wp.
          exlim t => t2.
          call (mod3_leq26_correct
                  ((t2 * W32.of_int 171) `>>` W8.of_int 9)).
          + auto => />.
            move=> &hr hrange hcap hctr0 hctrle ht80 hguard.
            have hq26 := div3_step_leq26 t2 (ht80 hguard).
            split.
            + exact hq26.
            move=> _.
            have hctrlt :
              W64.to_uint ctr{hr} <
                KeygenEtaSamplerSpec.eta_poly_words_i.
            + rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                      W64.ultE W64.of_uintK /= in hguard.
              exact hguard.
            have hctr_succ :
              W64.to_uint (ctr{hr} + W64.one) =
                W64.to_uint ctr{hr} + 1
              by rewrite W64.to_uintD_small 1:/#.
            split.
            + rewrite hctr_succ.
              apply (KeygenEtaSamplerSpec.centered_interval8192_set32_word
                       ap{hr} (W64.to_uint base{hr})
                       base{hr} ctr{hr} _).
              + trivial.
              + exact hcap.
              + exact hctrlt.
              + exact hrange.
              exact (KeygenEtaSamplerSpec.centered_trit_range _).
            rewrite hctr_succ
                    /KeygenEtaSamplerSpec.eta_poly_words_i.
            smt(W64.to_uint_cmp).
          + by auto => />.
      seq 1 :
        (KeygenEtaSamplerSpec.centered_interval8192
           ap base_i 0 (W64.to_uint ctr) /\
         W64.to_uint base = base_i /\
         base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
           BArray8192.size %/ 4 /\
         0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
         (ctr \ult W64.of_int 256 => W32.to_uint t <= 8)).
      + if.
        + wp.
          exlim t => t3.
          call (mod3_leq8_correct
                  ((t3 * W32.of_int 171) `>>` W8.of_int 9)).
          + auto => />.
            move=> &hr hrange hcap hctr0 hctrle ht26 hguard.
            have hq8 := div3_step_leq8 t3 (ht26 hguard).
            split.
            + exact hq8.
            move=> _.
            have hctrlt :
              W64.to_uint ctr{hr} <
                KeygenEtaSamplerSpec.eta_poly_words_i.
            + rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                      W64.ultE W64.of_uintK /= in hguard.
              exact hguard.
            have hctr_succ :
              W64.to_uint (ctr{hr} + W64.one) =
                W64.to_uint ctr{hr} + 1
              by rewrite W64.to_uintD_small 1:/#.
            split.
            + rewrite hctr_succ.
              apply (KeygenEtaSamplerSpec.centered_interval8192_set32_word
                       ap{hr} (W64.to_uint base{hr})
                       base{hr} ctr{hr} _).
              + trivial.
              + exact hcap.
              + exact hctrlt.
              + exact hrange.
              exact (KeygenEtaSamplerSpec.centered_trit_range _).
            rewrite hctr_succ
                    /KeygenEtaSamplerSpec.eta_poly_words_i.
            smt(W64.to_uint_cmp).
          + by auto => />.
      if.
      + auto => />.
        move=> &hr hrange hcap hctr0 hctrle ht8 hguard.
        have ht2 :
          W32.to_uint
            ((t{hr} * W32.of_int 171) `>>` W8.of_int 9) <= 2.
        + exact (div3_step_leq2 t{hr} (ht8 hguard)).
        have hctr_succ :
          W64.to_uint (ctr{hr} + W64.of_int 1) =
          W64.to_uint ctr{hr} + 1
          by rewrite W64.to_uintD_small 1:/#.
        split.
        + rewrite hctr_succ.
          apply (KeygenEtaSamplerSpec.centered_interval8192_set32_word
                   ap{hr} (W64.to_uint base{hr})
                   base{hr} ctr{hr}
                   ((t{hr} * W32.of_int 171 `>>` W8.of_int 9) -
                    (t{hr} * W32.of_int 171 `>>` W8.of_int 9 `>>` W8.one) *
                      W32.of_int 3)).
          + trivial.
          + exact hcap.
          + rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                    W64.ultE W64.of_uintK /= in hguard.
            exact hguard.
          + exact hrange.
          rewrite (last_trit_word
                     ((t{hr} * W32.of_int 171) `>>` W8.of_int 9) ht2).
          exact (KeygenEtaSamplerSpec.centered_trit_range
                   ((t{hr} * W32.of_int 171) `>>` W8.of_int 9)).
        rewrite hctr_succ.
        rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                W64.ultE W64.of_uintK /= in hguard.
        smt().
      by auto.
    by auto.
  by auto.
wp.
skip => />.
qed.

lemma eta_consume2048_frame ap0 base_i :
  hoare [KeygenSamplerCallersTarget.M.__kp_poly_uniform_eta_consume_2048 :
    KeygenEtaSamplerSpec.poly_frame8192 ap0 ap base_i /\
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4 /\
    0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i
    ==>
    KeygenEtaSamplerSpec.poly_frame8192 ap0 res.`1 base_i /\
    0 <= W64.to_uint res.`2 <= KeygenEtaSamplerSpec.eta_poly_words_i].
proof.
proc.
while (KeygenEtaSamplerSpec.poly_frame8192 ap0 ap base_i /\
       W64.to_uint base = base_i /\
       base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
         BArray8192.size %/ 4 /\
       0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i).
+ if.
  + by auto.
  if.
  + sp 5.
    if.
      + seq 5 :
        (KeygenEtaSamplerSpec.poly_frame8192
           ap0 ap base_i /\
         W64.to_uint base = base_i /\
         base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
           BArray8192.size %/ 4 /\
         0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i).
      + wp.
        call (_: true).
        + by auto.
        auto => />.
        move=> &hr pos0 hframe hcap hctr0 hctrle
                hlive hnotfull hpos haccept result.
        split.
        + apply (KeygenEtaSamplerSpec.poly_frame8192_set32_word
                   ap0 ap{hr} (W64.to_uint base{hr})
                   base{hr} ctr{hr} result).
          + exact hframe.
          + trivial.
          + exact hcap.
          rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                  W64.uleE W64.of_uintK /= in hnotfull.
          smt().
        rewrite W64.to_uintD_small 1:/#.
        rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                W64.uleE W64.of_uintK /= in hnotfull.
        smt().
      seq 1 :
        (KeygenEtaSamplerSpec.poly_frame8192
           ap0 ap base_i /\
         W64.to_uint base = base_i /\
         base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
           BArray8192.size %/ 4 /\
         0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i).
      + if.
        + wp.
          call (_: true).
          + by auto.
          auto => />.
          move=> &hr hframe hcap hctr0 hctrle hguard result.
          split.
          + apply (KeygenEtaSamplerSpec.poly_frame8192_set32_word
                     ap0 ap{hr} (W64.to_uint base{hr})
                     base{hr} ctr{hr} result).
            + exact hframe.
            + trivial.
            + exact hcap.
            rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                    W64.ultE W64.of_uintK /= in hguard.
            exact hguard.
          rewrite W64.to_uintD_small 1:/#.
          rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                  W64.ultE W64.of_uintK /= in hguard.
          smt().
        by auto.
      seq 1 :
        (KeygenEtaSamplerSpec.poly_frame8192
           ap0 ap base_i /\
         W64.to_uint base = base_i /\
         base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
           BArray8192.size %/ 4 /\
         0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i).
      + if.
        + wp.
          call (_: true).
          + by auto.
          auto => />.
          move=> &hr hframe hcap hctr0 hctrle hguard result.
          split.
          + apply (KeygenEtaSamplerSpec.poly_frame8192_set32_word
                     ap0 ap{hr} (W64.to_uint base{hr})
                     base{hr} ctr{hr} result).
            + exact hframe.
            + trivial.
            + exact hcap.
            rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                    W64.ultE W64.of_uintK /= in hguard.
            exact hguard.
          rewrite W64.to_uintD_small 1:/#.
          rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                  W64.ultE W64.of_uintK /= in hguard.
          smt().
        by auto.
      seq 1 :
        (KeygenEtaSamplerSpec.poly_frame8192
           ap0 ap base_i /\
         W64.to_uint base = base_i /\
         base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
           BArray8192.size %/ 4 /\
         0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i).
      + if.
        + wp.
          call (_: true).
          + by auto.
          auto => />.
          move=> &hr hframe hcap hctr0 hctrle hguard result.
          split.
          + apply (KeygenEtaSamplerSpec.poly_frame8192_set32_word
                     ap0 ap{hr} (W64.to_uint base{hr})
                     base{hr} ctr{hr} result).
            + exact hframe.
            + trivial.
            + exact hcap.
            rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                    W64.ultE W64.of_uintK /= in hguard.
            exact hguard.
          rewrite W64.to_uintD_small 1:/#.
          rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                  W64.ultE W64.of_uintK /= in hguard.
          smt().
        by auto.
      if.
      + auto => />.
        move=> &hr hframe hcap hctr0 hctrle hguard.
        split.
        + apply (KeygenEtaSamplerSpec.poly_frame8192_set32_word
                   ap0 ap{hr} (W64.to_uint base{hr})
                   base{hr} ctr{hr}
                   ((t{hr} * W32.of_int 171 `>>` W8.of_int 9) -
                    (t{hr} * W32.of_int 171 `>>` W8.of_int 9 `>>` W8.one) *
                      W32.of_int 3)).
          + exact hframe.
          + trivial.
          + exact hcap.
          rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                  W64.ultE W64.of_uintK /= in hguard.
          exact hguard.
        rewrite W64.to_uintD_small 1:/#.
        rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                W64.ultE W64.of_uintK /= in hguard.
        smt().
      by auto.
    by auto.
  by auto.
wp.
skip => />.
qed.

lemma eta_consume2048_ll :
  islossless
    KeygenSamplerCallersTarget.M.__kp_poly_uniform_eta_consume_2048.
proof.
proc.
inline KeygenSamplerCallersTarget.M.__poly_sample_mod3
       KeygenSamplerCallersTarget.M.__poly_sample_mod3_leq26
       KeygenSamplerCallersTarget.M.__poly_sample_mod3_leq8.
while (W64.to_uint pos <= W64.to_uint buflen)
      (if live = W64.zero then 0
       else W64.to_uint buflen - W64.to_uint pos + 1).
+ move=> z.
  if.
  + auto => /> &hr hpos hguard hfull.
    smt().
  if.
  + auto => />; smt(W64.to_uint_cmp).
  by auto => />; smt().
auto => />; smt().
qed.


lemma eta_consume2048_block136_pll bytes values0 base_i :
  phoare [KeygenSamplerCallersTarget.M.__kp_poly_uniform_eta_consume_2048 :
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4 /\
    W64.to_uint ctr = size values0 /\
    0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
    KeygenEtaSamplerSpec.eta_decoded_prefix8192 ap base_i values0 /\
    buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
    size bytes = KeygenEtaSamplerSpec.eta_block_bytes_i /\
    KeygenShakeStreamSpec.fips_rate_prefix_matches
      bp 0 bytes KeygenEtaSamplerSpec.eta_block_bytes_i
    ==>
    W64.to_uint res.`2 =
      size (KeygenEtaSamplerSpec.eta_fill values0 bytes) /\
    0 <= W64.to_uint res.`2 <= KeygenEtaSamplerSpec.eta_poly_words_i /\
    KeygenEtaSamplerSpec.eta_decoded_prefix8192
      res.`1 base_i (KeygenEtaSamplerSpec.eta_fill values0 bytes)] = 1%r.
proof.
by conseq eta_consume2048_ll
          (eta_consume2048_block136 bytes values0 base_i).
qed.

lemma eta_rank_exit (ctr0 : W64.t) :
  0 <= W64.to_uint ctr0 <= KeygenEtaSamplerSpec.eta_poly_words_i =>
  KeygenEtaSamplerSpec.eta_poly_words_i - W64.to_uint ctr0 <= 0 =>
  ! (ctr0 \ult W64.of_int 256).
proof.
move=> hctr hrank.
rewrite W64.ultE /KeygenEtaSamplerSpec.eta_poly_words_i /=.
smt(W64.to_uint_cmp).
qed.

lemma eta_fill_shake256_succ state blocks :
  0 <= blocks =>
  KeygenEtaSamplerSpec.eta_fill
      (KeygenEtaSamplerSpec.eta_fill []
        (KeygenShakeStreamSpec.shake256_squeeze_bytes state blocks))
      (KeygenShakeStreamSpec.shake256_squeeze_block state blocks) =
    KeygenEtaSamplerSpec.eta_fill []
      (KeygenShakeStreamSpec.shake256_squeeze_bytes state (blocks + 1)).
proof.
move=> hblocks.
rewrite KeygenShakeStreamSpec.shake256_squeeze_bytes_succ 1://.
by rewrite KeygenEtaSamplerSpec.eta_fill_cat.
qed.

lemma eta_fill_shake256_one state :
  KeygenEtaSamplerSpec.eta_fill []
      (KeygenShakeStreamSpec.shake256_squeeze_block state 0) =
    KeygenEtaSamplerSpec.eta_fill []
      (KeygenShakeStreamSpec.shake256_squeeze_bytes state 1).
proof.
have h := eta_fill_shake256_succ state 0 _.
+ smt().
rewrite /KeygenShakeStreamSpec.shake256_squeeze_bytes
        KeygenShakeStreamSpec.squeeze_bytes_iter0
        KeygenEtaSamplerSpec.eta_fill_nil 1:/# in h.
exact h.
qed.

lemma shake256_squeeze_overwrite_step
    (initial : int list)
    (before_state after_state : BArray200.t)
    (after_out : BArray1024.t)
    (blocks : int) :
  0 <= blocks =>
  KeygenShakeStreamSpec.state_bytes_le before_state =
    KeygenShakeStreamSpec.squeeze_state_iter initial blocks =>
  KeygenShakeStreamSpec.rate_block_matches
    after_out 0 after_state KeygenEtaSamplerSpec.eta_block_bytes_i =>
  KeygenKeccak1600Spec.state_of_barray after_state =
    HAETAE_Keccak1600.keccak_f1600_lanes
      (KeygenKeccak1600Spec.state_of_barray before_state) =>
  KeygenShakeStreamSpec.state_bytes_le after_state =
      KeygenShakeStreamSpec.squeeze_state_iter initial (blocks + 1) /\
  KeygenShakeStreamSpec.fips_rate_prefix_matches
    after_out 0
    (KeygenShakeStreamSpec.shake256_squeeze_block initial blocks)
    KeygenEtaSamplerSpec.eta_block_bytes_i.
proof.
move=> hblocks hstate hblock hperm.
have hstate_next :=
  KeygenShakeStreamSpec.squeeze_state_iter_barray_step
    initial before_state after_state blocks hblocks hstate hperm.
have hprefix :=
  KeygenShakeStreamSpec.rate_block_matches_fips_prefix
    after_out 0 after_state
    (KeygenShakeStreamSpec.squeeze_state_iter initial (blocks + 1)) 136
    _ hstate_next _.
+ smt().
+ rewrite /KeygenEtaSamplerSpec.eta_block_bytes_i in hblock.
  exact hblock.
split; first exact hstate_next.
rewrite /KeygenEtaSamplerSpec.eta_block_bytes_i.
exact (KeygenShakeStreamSpec.fips_rate_prefix_matches_shake256_block
  after_out 0 initial blocks hprefix).
qed.

lemma eta2048_leaf_stream
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_eta_at_seedbuf_2048 :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4 /\
    W64.to_uint seedoff0 + 64 <= BArray128.size
    ==>
    exists blocks,
      1 <= blocks /\
      size (KeygenEtaSamplerSpec.eta_fill []
        (KeygenShakeStreamSpec.shake256_squeeze_bytes
          (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
            seed0 seedoff0 nonce0) blocks)) =
        KeygenEtaSamplerSpec.eta_poly_words_i /\
      KeygenEtaSamplerSpec.eta_decoded_prefix8192
        res base_i
        (KeygenEtaSamplerSpec.eta_fill []
          (KeygenShakeStreamSpec.shake256_squeeze_bytes
            (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
              seed0 seedoff0 nonce0) blocks))].
proof.
proc.
seq 17 :
  (W64.to_uint base = base_i /\
   base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
     BArray8192.size %/ 4 /\
   off = W64.of_int 0 /\
   buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
   KeygenShakeStreamSpec.state_bytes_le sp_0 =
     KeygenShakeStreamSpec.squeeze_state_iter
       (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
         seed0 seedoff0 nonce0) 1 /\
   W64.to_uint ctr =
     size (KeygenEtaSamplerSpec.eta_fill []
       (KeygenShakeStreamSpec.shake256_squeeze_bytes
         (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 1)) /\
   KeygenEtaSamplerSpec.eta_decoded_prefix8192
     ap base_i
     (KeygenEtaSamplerSpec.eta_fill []
       (KeygenShakeStreamSpec.shake256_squeeze_bytes
         (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 1))).
+ seq 11 :
    (W64.to_uint base = base_i /\
     base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
       BArray8192.size %/ 4 /\
     off = W64.of_int 0 /\
     ctr = W64.of_int 0 /\
     buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 1 /\
     KeygenShakeStreamSpec.fips_rate_prefix_matches
       bufp 0
       (KeygenShakeStreamSpec.shake256_squeeze_block
         (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 0)
       KeygenEtaSamplerSpec.eta_block_bytes_i).
  + seq 6 :
      (sp_0 = state /\ bufp = buf /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 64 <= BArray128.size).
    + by auto.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 0 /\
       off = W64.of_int 0 /\
       bufp = buf /\
       W64.to_uint base = base_i /\
       base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 64 <= BArray128.size).
    + wp.
      call (TargetKeygenShakeStream.shake256_init_seedbuf_padded_state
        seed0 seedoff0 nonce0).
      auto => /> &hr hcap result hstate.
      by rewrite KeygenShakeStreamSpec.squeeze_state_iter0.
    seq 1 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 1 /\
       KeygenShakeStreamSpec.fips_rate_prefix_matches
         bufp 0
         (KeygenShakeStreamSpec.shake256_squeeze_block
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 0)
         KeygenEtaSamplerSpec.eta_block_bytes_i /\
       off = W64.of_int 0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
         BArray8192.size %/ 4).
    + exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze256_rate_block
        before_out (W64.of_int 0) before_state).
      auto => /> &hr hstate hbase hcap hseedcap
        result hblock hframe hperm.
      have [hstate1 hprefix] :=
        shake256_squeeze_overwrite_step
          (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          before_state result.`2 result.`1 0 _ hstate _ hperm.
      + smt().
      + rewrite /KeygenEtaSamplerSpec.eta_block_bytes_i.
        exact hblock.
      do split; try assumption.
    by auto.
  wp.
  call (eta_consume2048_block136
    (KeygenShakeStreamSpec.shake256_squeeze_block
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 0) [] base_i).
  + auto => />.
    move=> &hr hcap hstate hprefix.
    split.
    + have hsize := KeygenShakeStreamSpec.shake256_squeeze_block_size
        (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
          seed0 seedoff0 nonce0) 0.
      rewrite /KeygenEtaSamplerSpec.eta_block_bytes_i.
      smt().
    move=> _ hprefix0 hblocksize callresult.
    have hfill := eta_fill_shake256_one
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0).
    rewrite /protect_64 /protect_ptr.
    move=> hresultctr _ _ hresultdecoded.
    split.
    + by rewrite hresultctr -hfill.
    + by rewrite -hfill.

while
  (W64.to_uint base = base_i /\
   base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
     BArray8192.size %/ 4 /\
   off = W64.of_int 0 /\
   buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
   exists blocks,
     1 <= blocks /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
           seed0 seedoff0 nonce0) blocks /\
     W64.to_uint ctr =
       size (KeygenEtaSamplerSpec.eta_fill []
         (KeygenShakeStreamSpec.shake256_squeeze_bytes
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)) /\
     KeygenEtaSamplerSpec.eta_decoded_prefix8192
       ap base_i
       (KeygenEtaSamplerSpec.eta_fill []
         (KeygenShakeStreamSpec.shake256_squeeze_bytes
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks))).
+
  elim* => blocks.
  seq 7 :
    (W64.to_uint base = base_i /\
     base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
       BArray8192.size %/ 4 /\
     off = W64.of_int 0 /\
     buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
     1 <= blocks /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
           seed0 seedoff0 nonce0) (blocks + 1) /\
     W64.to_uint ctr =
       size (KeygenEtaSamplerSpec.eta_fill []
         (KeygenShakeStreamSpec.shake256_squeeze_bytes
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)) /\
     KeygenEtaSamplerSpec.eta_decoded_prefix8192
       ap base_i
       (KeygenEtaSamplerSpec.eta_fill []
         (KeygenShakeStreamSpec.shake256_squeeze_bytes
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)) /\
     KeygenShakeStreamSpec.fips_rate_prefix_matches
       bufp 0
       (KeygenShakeStreamSpec.shake256_squeeze_block
         (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
           seed0 seedoff0 nonce0) blocks)
       KeygenEtaSamplerSpec.eta_block_bytes_i).
  + wp.
    exlim bufp => before_out.
    exlim sp_0 => before_state.
    call (TargetKeygenShakeStream.squeeze256_rate_block
      before_out (W64.of_int 0) before_state).
    auto => />.
    move=> &hr hcap hblocks hstate hctr hdecoded hguard.
    move=> _ result hblock _ hperm.
    have [hstate_next hprefix] :=
      shake256_squeeze_overwrite_step
        (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
          seed0 seedoff0 nonce0)
        before_state result.`2 result.`1 blocks _ hstate _ hperm.
    + smt().
    + rewrite /KeygenEtaSamplerSpec.eta_block_bytes_i.
      exact hblock.
    rewrite /protect_64 /protect_ptr.
    do split; try assumption; smt().
  wp.
  call (eta_consume2048_block136
    (KeygenShakeStreamSpec.shake256_squeeze_block
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0) blocks)
    (KeygenEtaSamplerSpec.eta_fill []
      (KeygenShakeStreamSpec.shake256_squeeze_bytes
        (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
          seed0 seedoff0 nonce0) blocks)) base_i).
  auto => />.
  move=> &hr hcap hblocks hstate hctr hdecoded hprefix.
  split.
  + have hle := KeygenEtaSamplerSpec.eta_fill_size_le []
      (KeygenShakeStreamSpec.shake256_squeeze_bytes
        (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
          seed0 seedoff0 nonce0) blocks).
    rewrite KeygenShakeStreamSpec.shake256_squeeze_block_size
            /KeygenEtaSamplerSpec.eta_block_bytes_i.
    smt(W64.to_uint_cmp).
  move=> _ hprefix0 result.
  have hfill := eta_fill_shake256_succ
    (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
      seed0 seedoff0 nonce0) blocks _.
  + smt().
  rewrite /protect_64 /protect_ptr.
  move=> apresult hresultctr _ _ hresultdecoded.
  exists (blocks + 1).
  do split.
  + smt().
  + exact hstate.
  + rewrite -hfill.
    exact hresultctr.
  + rewrite -hfill.
    exact hresultdecoded.

wp.
skip => />.
move=> &hr hcap hstate hctr hdecoded.
split.
exists 1.
by auto.
move=> ap0 base0 ctr0 sp_00 hguard hcap0 blocks0 hblocks0 hstate0
  hctr0eq.
have hctrle : W64.to_uint ctr0 <=
    KeygenEtaSamplerSpec.eta_poly_words_i.
+ rewrite hctr0eq.
  exact (KeygenEtaSamplerSpec.eta_fill_size_le []
    (KeygenShakeStreamSpec.shake256_squeeze_bytes
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0) blocks0)).
have hfull : W64.to_uint ctr0 =
    KeygenEtaSamplerSpec.eta_poly_words_i.
+ move: hguard.
  rewrite W64.ultE W64.of_uintK
          /KeygenEtaSamplerSpec.eta_poly_words_i /=.
  smt(W64.to_uint_cmp).
by smt().
qed.

lemma eta2048_leaf_progress_ll
    (seed0 : BArray128.t) (seedoff0 nonce0 : W64.t) base_i limit :
  phoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_eta_at_seedbuf_2048 :
    seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4 /\
    W64.to_uint seedoff0 + 64 <= BArray128.size /\
    KeygenEtaSamplerSpec.eta_progress_prefix
      seed0 seedoff0 nonce0 limit
    ==> true] = 1%r.
proof.
proc.
while
  (W64.to_uint base = base_i /\
   base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
     BArray8192.size %/ 4 /\
   off = W64.of_int 0 /\
   buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
   KeygenEtaSamplerSpec.eta_progress_prefix
     seed0 seedoff0 nonce0 limit /\
   0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
   exists blocks,
     1 <= blocks <= limit /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
           seed0 seedoff0 nonce0) blocks /\
     W64.to_uint ctr =
       size (KeygenEtaSamplerSpec.eta_fill []
         (KeygenShakeStreamSpec.shake256_squeeze_bytes
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)) /\
     KeygenEtaSamplerSpec.eta_decoded_prefix8192
       ap base_i
       (KeygenEtaSamplerSpec.eta_fill []
         (KeygenShakeStreamSpec.shake256_squeeze_bytes
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)))
  (KeygenEtaSamplerSpec.eta_poly_words_i - W64.to_uint ctr).
+ move=> z.
  conseq (_ : _ ==> true : = 1%r)
    (_ : _ ==>
    (W64.to_uint base = base_i /\
     base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
       BArray8192.size %/ 4 /\
     off = W64.of_int 0 /\
     buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
     KeygenEtaSamplerSpec.eta_progress_prefix
       seed0 seedoff0 nonce0 limit /\
     0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
     (exists blocks,
       1 <= blocks <= limit /\
       KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks /\
       W64.to_uint ctr =
         size (KeygenEtaSamplerSpec.eta_fill []
           (KeygenShakeStreamSpec.shake256_squeeze_bytes
             (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
               seed0 seedoff0 nonce0) blocks)) /\
       KeygenEtaSamplerSpec.eta_decoded_prefix8192
         ap base_i
         (KeygenEtaSamplerSpec.eta_fill []
           (KeygenShakeStreamSpec.shake256_squeeze_bytes
             (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
               seed0 seedoff0 nonce0) blocks))) /\
     KeygenEtaSamplerSpec.eta_poly_words_i - W64.to_uint ctr < z)) => //.
  + smt().
  + smt().
  + elim* => blocks.
    exlim ap => iteration_ap.
    seq 7 :
      (ap = iteration_ap /\
       W64.to_uint base = base_i /\
       base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
         BArray8192.size %/ 4 /\
       off = W64.of_int 0 /\
       buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
       KeygenEtaSamplerSpec.eta_progress_prefix
         seed0 seedoff0 nonce0 limit /\
       0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
       1 <= blocks < limit /\
       KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) (blocks + 1) /\
       W64.to_uint ctr =
         KeygenEtaSamplerSpec.eta_prefix_count
           seed0 seedoff0 nonce0 blocks /\
       KeygenEtaSamplerSpec.eta_decoded_prefix8192
         ap base_i
         (KeygenEtaSamplerSpec.eta_fill []
           (KeygenShakeStreamSpec.shake256_squeeze_bytes
             (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
               seed0 seedoff0 nonce0) blocks)) /\
       KeygenShakeStreamSpec.fips_rate_prefix_matches
         bufp 0
         (KeygenShakeStreamSpec.shake256_squeeze_block
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) blocks)
         KeygenEtaSamplerSpec.eta_block_bytes_i /\
       W64.to_uint ctr < KeygenEtaSamplerSpec.eta_poly_words_i /\
       KeygenEtaSamplerSpec.eta_poly_words_i - W64.to_uint ctr = z).
    + wp.
      exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze256_rate_block
        before_out (W64.of_int 0) before_state).
      auto => />.
      move=> &hr hbase hlimit hendpoint hprogress hctr0 hctrle
        hblocks0 hblocksle hstate hctreq hdecoded hguard hcallcap
        result hblock hframe hperm.
      have hctrlt :
        W64.to_uint ctr{hr} < KeygenEtaSamplerSpec.eta_poly_words_i.
      + rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
                W64.ultE W64.of_uintK /= in hguard.
        smt(W64.to_uint_cmp).
      have hcert :
        KeygenEtaSamplerSpec.eta_progress_prefix
          seed0 seedoff0 nonce0 limit.
      + rewrite /KeygenEtaSamplerSpec.eta_progress_prefix
                  /KeygenEtaSamplerSpec.eta_sufficient_prefix.
        smt().
      have hcount :
        W64.to_uint ctr{hr} =
          KeygenEtaSamplerSpec.eta_prefix_count
            seed0 seedoff0 nonce0 blocks.
      + rewrite /KeygenEtaSamplerSpec.eta_prefix_count.
        exact hctreq.
      have hblocklt :=
        KeygenEtaSamplerSpec.eta_progress_prefix_before_limit
          seed0 seedoff0 nonce0 limit blocks hcert hblocks0 _.
      + by rewrite -hcount.
      have [hstate_next hprefix] :=
        shake256_squeeze_overwrite_step
          (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          before_state result.`2 result.`1 blocks
          _ hstate _ hperm.
      + smt().
      + rewrite /KeygenEtaSamplerSpec.eta_block_bytes_i.
        exact hblock.
      rewrite /protect_64 /protect_ptr.
      do split; try assumption.
    wp.
    call (eta_consume2048_block136
      (KeygenShakeStreamSpec.shake256_squeeze_block
        (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
          seed0 seedoff0 nonce0) blocks)
      (KeygenEtaSamplerSpec.eta_fill []
        (KeygenShakeStreamSpec.shake256_squeeze_bytes
          (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
            seed0 seedoff0 nonce0) blocks)) base_i).
    auto => />.
    move=> &hr hbase hlimit hendpoint hprogress hctr0 hctrle
      hblocks hblocklt hstate hctr hdecoded hprefix hctrlt.
    split.
    + have hsize := KeygenShakeStreamSpec.shake256_squeeze_block_size
        (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
          seed0 seedoff0 nonce0) blocks.
      rewrite /KeygenEtaSamplerSpec.eta_block_bytes_i.
      smt().
    move=> _ _ result hresultctr hresultctr0 hresultctrle hresultdecoded.
    have hfill := eta_fill_shake256_succ
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0) blocks _.
    + smt().
    have hcert :
      KeygenEtaSamplerSpec.eta_progress_prefix
        seed0 seedoff0 nonce0 limit.
    + rewrite /KeygenEtaSamplerSpec.eta_progress_prefix
                /KeygenEtaSamplerSpec.eta_sufficient_prefix.
      smt().
    have hstep :=
      KeygenEtaSamplerSpec.eta_progress_prefix_step
        seed0 seedoff0 nonce0 limit blocks hcert _ _.
    + smt().
    + by rewrite -hctr.
    have hnext :
      W64.to_uint result.`2 =
        KeygenEtaSamplerSpec.eta_prefix_count
          seed0 seedoff0 nonce0 (blocks + 1).
    + rewrite /KeygenEtaSamplerSpec.eta_prefix_count -hfill.
      exact hresultctr.
    rewrite /protect_64 /protect_ptr.
    split.
    + exists (blocks + 1).
      do split.
      + smt().
      + smt().
      + exact hstate.
      + rewrite -hfill.
        exact hresultctr.
      + rewrite -hfill.
        exact hresultdecoded.
    + smt().
  wp.
  call eta_consume2048_ll.
  wp.
  call TargetKeygenShakeStream.squeeze256_ll.
  by auto.
conseq (_ : _ ==> true : = 1%r)
       (_ :
        seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
        W64.to_uint base = base_i /\
        base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
          BArray8192.size %/ 4 /\
        W64.to_uint seedoff0 + 64 <= BArray128.size /\
        KeygenEtaSamplerSpec.eta_progress_prefix
          seed0 seedoff0 nonce0 limit
        ==>
        (W64.to_uint base = base_i /\
         base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
           BArray8192.size %/ 4 /\
         off = W64.of_int 0 /\
         buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
         KeygenEtaSamplerSpec.eta_progress_prefix
           seed0 seedoff0 nonce0 limit /\
         0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i /\
         exists blocks,
           1 <= blocks <= limit /\
           KeygenShakeStreamSpec.state_bytes_le sp_0 =
             KeygenShakeStreamSpec.squeeze_state_iter
               (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
                 seed0 seedoff0 nonce0) blocks /\
           W64.to_uint ctr =
             size (KeygenEtaSamplerSpec.eta_fill []
               (KeygenShakeStreamSpec.shake256_squeeze_bytes
                 (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
                   seed0 seedoff0 nonce0) blocks)) /\
           KeygenEtaSamplerSpec.eta_decoded_prefix8192
             ap base_i
             (KeygenEtaSamplerSpec.eta_fill []
               (KeygenShakeStreamSpec.shake256_squeeze_bytes
                 (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
                   seed0 seedoff0 nonce0) blocks)))) => //.
+ smt(eta_rank_exit).
+ seq 11 :
    (W64.to_uint base = base_i /\
     base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
       BArray8192.size %/ 4 /\
     off = W64.of_int 0 /\
     ctr = W64.of_int 0 /\
     buflen = W64.of_int KeygenEtaSamplerSpec.eta_block_bytes_i /\
     KeygenEtaSamplerSpec.eta_progress_prefix
       seed0 seedoff0 nonce0 limit /\
     KeygenShakeStreamSpec.state_bytes_le sp_0 =
       KeygenShakeStreamSpec.squeeze_state_iter
         (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 1 /\
     KeygenShakeStreamSpec.fips_rate_prefix_matches
       bufp 0
       (KeygenShakeStreamSpec.shake256_squeeze_block
         (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
           seed0 seedoff0 nonce0) 0)
       KeygenEtaSamplerSpec.eta_block_bytes_i).
  + seq 6 :
      (sp_0 = state /\ bufp = buf /\
       seedp = seed0 /\ seedoff = seedoff0 /\ nonce = nonce0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 64 <= BArray128.size /\
       KeygenEtaSamplerSpec.eta_progress_prefix
         seed0 seedoff0 nonce0 limit).
    + by auto.
    seq 2 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 0 /\
       off = W64.of_int 0 /\
       bufp = buf /\
       W64.to_uint base = base_i /\
       base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
         BArray8192.size %/ 4 /\
       W64.to_uint seedoff0 + 64 <= BArray128.size /\
       KeygenEtaSamplerSpec.eta_progress_prefix
         seed0 seedoff0 nonce0 limit).
    + wp.
      call (TargetKeygenShakeStream.shake256_init_seedbuf_padded_state
        seed0 seedoff0 nonce0).
      auto => /> &hr hcap hseedcap hcert result hstate.
      by rewrite KeygenShakeStreamSpec.squeeze_state_iter0.
    seq 1 :
      (KeygenShakeStreamSpec.state_bytes_le sp_0 =
         KeygenShakeStreamSpec.squeeze_state_iter
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 1 /\
       KeygenShakeStreamSpec.fips_rate_prefix_matches
         bufp 0
         (KeygenShakeStreamSpec.shake256_squeeze_block
           (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
             seed0 seedoff0 nonce0) 0)
         KeygenEtaSamplerSpec.eta_block_bytes_i /\
       off = W64.of_int 0 /\
       W64.to_uint base = base_i /\
       base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
         BArray8192.size %/ 4 /\
       KeygenEtaSamplerSpec.eta_progress_prefix
         seed0 seedoff0 nonce0 limit).
    + exlim bufp => before_out.
      exlim sp_0 => before_state.
      call (TargetKeygenShakeStream.squeeze256_rate_block
        before_out (W64.of_int 0) before_state).
      auto => /> &hr hstate hcap hseedcap hlimit hendpoint hprogress
        hcallcap result hblock hframe hperm.
      have [hstate1 hprefix] :=
        shake256_squeeze_overwrite_step
          (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
            seed0 seedoff0 nonce0)
          before_state result.`2 result.`1 0 _ hstate _ hperm.
      + smt().
      + rewrite /KeygenEtaSamplerSpec.eta_block_bytes_i.
        exact hblock.
      do split; try assumption.
    by auto.
  wp.
  call (eta_consume2048_block136
    (KeygenShakeStreamSpec.shake256_squeeze_block
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 0) [] base_i).
  auto => />.
  move=> &hr hcap hlimit hendpoint hprogress hstate hprefix.
  split.
  + have hsize := KeygenShakeStreamSpec.shake256_squeeze_block_size
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed0 seedoff0 nonce0) 0.
    rewrite /KeygenEtaSamplerSpec.eta_block_bytes_i.
    smt().
  move=> _ hprefix0 hblocksize result hresultctr hresultctr0
    hresultctrle hresultdecoded.
  have hfill := eta_fill_shake256_one
    (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
      seed0 seedoff0 nonce0).
  rewrite /protect_64 /protect_ptr.
  exists 1.
  do split.
  + smt().
  + exact hstate.
  + rewrite -hfill.
    exact hresultctr.
  + rewrite -hfill.
    exact hresultdecoded.
+ wp.
  call eta_consume2048_ll.
  wp.
  call TargetKeygenShakeStream.squeeze256_ll.
  wp.
  call TargetKeygenShakeStream.shake256_init_seedbuf_ll.
  by auto.
qed.

lemma eta2048_leaf_centered base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_eta_at_seedbuf_2048 :
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4
    ==>
    KeygenEtaSamplerSpec.centered_interval8192
      res base_i 0 KeygenEtaSamplerSpec.eta_poly_words_i].
proof.
proc.
while (KeygenEtaSamplerSpec.centered_interval8192
         ap base_i 0 (W64.to_uint ctr) /\
       W64.to_uint base = base_i /\
       base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
         BArray8192.size %/ 4 /\
       0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i).
+ wp.
  call (eta_consume2048_centered base_i).
  wp.
  call (_: true).
  + by auto.
  by auto.
wp.
call (eta_consume2048_centered base_i).
wp.
call (_: true).
+ by auto.
wp.
call (_: true).
+ by auto.
auto => /> &hr hcap.
split.
+ exact (KeygenEtaSamplerSpec.centered_interval8192_empty
           ap{hr} (W64.to_uint base{hr}) 0).
move=> _ _ result hres0 hresle hprefix
        ap0 base0 ctr0 hdone hprefix0 hbase0 hctr0 hctrle.
have hfull : W64.to_uint ctr0 =
    KeygenEtaSamplerSpec.eta_poly_words_i.
+ rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
          W64.ultE W64.of_uintK /= in hdone.
  smt(W64.to_uint_cmp).
by rewrite -hfull.
qed.

lemma eta2048_leaf_frame ap0 base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_eta_at_seedbuf_2048 :
    ap = ap0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4
    ==>
    KeygenEtaSamplerSpec.poly_frame8192 ap0 res base_i].
proof.
proc.
while (KeygenEtaSamplerSpec.poly_frame8192 ap0 ap base_i /\
       W64.to_uint base = base_i /\
       base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
         BArray8192.size %/ 4 /\
       0 <= W64.to_uint ctr <= KeygenEtaSamplerSpec.eta_poly_words_i).
+ wp.
  call (eta_consume2048_frame ap0 base_i).
  wp.
  call (_: true).
  + by auto.
  by auto.
wp.
call (eta_consume2048_frame ap0 base_i).
wp.
call (_: true).
+ by auto.
wp.
call (_: true).
+ by auto.
auto => /> &hr hcap.
qed.

lemma eta2048_leaf_correct ap0 base_i :
  hoare [KeygenSamplerCallersTarget.M._kp_poly_uniform_eta_at_seedbuf_2048 :
    ap = ap0 /\
    W64.to_uint base = base_i /\
    base_i + KeygenEtaSamplerSpec.eta_poly_words_i <=
      BArray8192.size %/ 4
    ==>
    KeygenEtaSamplerSpec.centered_interval8192
      res base_i 0 KeygenEtaSamplerSpec.eta_poly_words_i /\
    KeygenEtaSamplerSpec.poly_frame8192 ap0 res base_i].
proof.
conseq (eta2048_leaf_centered base_i)
       (eta2048_leaf_frame ap0 base_i) => />.
qed.

end TargetKeygenEtaSampler.
