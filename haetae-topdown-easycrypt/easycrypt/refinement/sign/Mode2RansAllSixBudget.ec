require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  HbzPrepareTarget
  HbzFullEncodeTarget
  Mode2HbzCodecSpec
  Mode2HbzTableCertificate
  Mode2HbzPrepare
  Mode2RansByteStack
  Mode2RansArrayListBridge
  Mode2RansEncodeRefinement.

theory Mode2RansAllSixBudget.

import Mode2HbzCodecSpec
       Mode2HbzTableCertificate
       Mode2HbzPrepare
       Mode2RansByteStack
       Mode2RansArrayListBridge
       Mode2RansEncodeRefinement.

module Prepare = HbzPrepareTarget.M.
module Focus = HbzFullEncodeTarget.M.

op zero_hbz : BArray8192.t =
  BArray8192.init (fun _ => W8.zero).

op all_six_symbols : BArray2048.t =
  BArray2048.init (fun _ => W8.of_int 6).

op all_six_symbol_list : int list =
  symbol_list_of_array all_six_symbols.

op all_six_list (symbols : int list) : bool =
  forall i, 0 <= i < size symbols => nth 0 symbols i = 6.

op all_six_prefix (symbols : BArray2048.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray2048.get8 symbols i = W8.of_int 6.

lemma zero_hbz_get32 i :
  0 <= i < mode2_hbz_count =>
  BArray8192.get32 zero_hbz i = W32.zero.
proof.
move=> hi.
apply W32.ext_eq => bit hbit.
rewrite W4u8.get_bits8 1:hbit.
rewrite /zero_hbz BArray8192.get32d_byte 1:/#.
rewrite BArray8192.initiE 1:/# W8.zerowE W32.zerowE.
trivial.
qed.

lemma hbz_symbol_word_zero :
  hbz_symbol_word W32.zero = W8.of_int 6.
proof.
apply W8.to_uint_eq.
rewrite /hbz_symbol_word W32.to_sintE W32.to_uint0 /mode2_hbz_offset /=.
trivial.
qed.

lemma zero_hbz_canonical :
  canonical_hbz_mode2 zero_hbz.
proof.
rewrite /canonical_hbz_mode2 => i hi.
rewrite zero_hbz_get32 1:hi W32.to_sintE W32.to_uint0
        /mode2_hbz_offset /mode2_hbz_alphabet /=.
smt().
qed.

lemma all_six_symbol_listE :
  all_six_symbol_list = nseq mode2_hbz_count 6.
proof.
apply (eq_from_nth 0).
+ rewrite /all_six_symbol_list symbol_list_of_array_size size_nseq /mode2_hbz_count.
  trivial.
move=> i hi.
rewrite /all_six_symbol_list.
rewrite symbol_list_of_array_size in hi.
have -> :
    nth 0 (symbol_list_of_array all_six_symbols) i =
    W8.to_uint (BArray2048.get8 all_six_symbols i).
+ exact (symbol_list_of_array_nth all_six_symbols i hi).
rewrite /all_six_symbols.
have hset :
    BArray2048.get8 (BArray2048.init (fun _ => W8.of_int 6)) i = W8.of_int 6.
+ rewrite BArray2048.initiE 1:/#.
  trivial.
rewrite hset W8.of_uintK /=.
rewrite (nth_nseq 0 i mode2_hbz_count 6).
+ trivial.
rewrite /mode2_hbz_count in hi.
smt().
qed.

lemma all_six_symbol_list_size :
  size all_six_symbol_list = mode2_hbz_count.
proof.
rewrite all_six_symbol_listE size_nseq /mode2_hbz_count.
trivial.
qed.

lemma all_six_symbol_list_nth i :
  0 <= i < mode2_hbz_count =>
  nth 0 all_six_symbol_list i = 6.
proof.
move=> hi.
rewrite all_six_symbol_listE.
exact (nth_nseq 0 i mode2_hbz_count 6 hi).
qed.

lemma all_six_symbol_list_canonical :
  canonical_symbol_list all_six_symbol_list.
proof.
rewrite canonical_symbol_list_nth => i hi.
rewrite all_six_symbol_list_size in hi.
rewrite all_six_symbol_list_nth 1:hi /mode2_hbz_alphabet.
smt().
qed.

lemma all_six_list_eq_nseq symbols :
  all_six_list symbols => symbols = nseq (size symbols) 6.
proof.
move=> hallsix.
apply (eq_from_nth 0).
+ rewrite size_nseq.
  have := size_ge0 symbols.
  smt().
move=> i hi.
rewrite (hallsix i hi).
rewrite (nth_nseq 0 i (size symbols) 6 hi).
trivial.
qed.

lemma all_six_symbols_stream :
  mode2_hbz_symbol_stream all_six_symbols.
proof.
move=> i hi.
rewrite /all_six_symbols BArray2048.initiE 1:/# W8.of_uintK /mode2_hbz_alphabet /=.
smt().
qed.

lemma prepared_zero_hbz_is_all_six symbols :
  prepared_hbz_prefix symbols zero_hbz mode2_hbz_count =>
  all_six_prefix symbols mode2_hbz_count.
proof.
move=> hprepared.
rewrite /all_six_prefix => i hi.
rewrite /prepared_hbz_prefix in hprepared.
rewrite (hprepared i hi) zero_hbz_get32 1:hi hbz_symbol_word_zero.
trivial.
qed.

lemma all_six_prefix_symbol_list symbols :
  all_six_prefix symbols mode2_hbz_count =>
  symbol_list_of_array symbols = nseq mode2_hbz_count 6.
proof.
move=> hprefix.
apply (eq_from_nth 0).
+ rewrite symbol_list_of_array_size size_nseq /mode2_hbz_count.
  trivial.
move=> i hi.
rewrite symbol_list_of_array_size in hi.
have -> :
    nth 0 (symbol_list_of_array symbols) i =
    W8.to_uint (BArray2048.get8 symbols i).
+ exact (symbol_list_of_array_nth symbols i hi).
rewrite /all_six_prefix in hprefix.
rewrite (hprefix i hi) W8.of_uintK /=.
rewrite (nth_nseq 0 i mode2_hbz_count 6).
+ trivial.
rewrite /mode2_hbz_count in hi.
smt().
qed.

lemma full_encode_prepare_exact_focused :
  equiv [Focus._encode_hb_z1_prepare ~ Prepare._encode_hb_z1_prepare :
    ={symsp, badp, hp, count, mhb, offset}
    ==>
    ={res}].
proof.
proc; sim.
qed.

lemma prepared_zero_hbz_all_six_post
    (symbols : BArray2048.t)
    (bad : BArray8.t)
    (symbols0 : BArray2048.t) :
  BArray8.get64 bad 0 = W64.zero /\
  prepared_hbz_prefix symbols zero_hbz mode2_hbz_count /\
  byte_tail_frame symbols0 symbols mode2_hbz_count =>
  BArray8.get64 bad 0 = W64.zero /\
  prepared_hbz_prefix symbols zero_hbz mode2_hbz_count /\
  all_six_prefix symbols mode2_hbz_count /\
  byte_tail_frame symbols0 symbols mode2_hbz_count.
proof.
move=> [hbad [hprepared hframe]].
split; first exact hbad.
split; first exact hprepared.
split; first exact (prepared_zero_hbz_is_all_six _ hprepared).
exact hframe.
qed.

lemma actual_focused_encode_hb_z1_prepare_zero_hbz_core
    (symbols0 : BArray2048.t)
    (bad0 : BArray8.t) :
  hoare [Focus._encode_hb_z1_prepare :
    symsp = symbols0 /\ badp = bad0 /\ hp = zero_hbz /\
    count = W64.of_int mode2_hbz_count /\
    mhb = W64.of_int mode2_hbz_alphabet /\
    offset = W64.of_int mode2_hbz_offset
    ==>
    BArray8.get64 res.`2 0 = W64.zero /\
    prepared_hbz_prefix res.`1 zero_hbz mode2_hbz_count /\
    byte_tail_frame symbols0 res.`1 mode2_hbz_count].
proof.
conseq full_encode_prepare_exact_focused
  (encode_hb_z1_prepare_core_mode2_correct symbols0 bad0 zero_hbz) => //=.
move=> &1 hpre.
exists (symsp{1}, badp{1}, hp{1}, count{1}, mhb{1}, offset{1}) => /=.
smt(zero_hbz_canonical).
qed.

lemma actual_focused_encode_hb_z1_prepare_zero_hbz
    (symbols0 : BArray2048.t)
    (bad0 : BArray8.t) :
  hoare [Focus._encode_hb_z1_prepare :
    symsp = symbols0 /\ badp = bad0 /\ hp = zero_hbz /\
    count = W64.of_int mode2_hbz_count /\
    mhb = W64.of_int mode2_hbz_alphabet /\
    offset = W64.of_int mode2_hbz_offset
    ==>
    BArray8.get64 res.`2 0 = W64.zero /\
    prepared_hbz_prefix res.`1 zero_hbz mode2_hbz_count /\
    all_six_prefix res.`1 mode2_hbz_count /\
    byte_tail_frame symbols0 res.`1 mode2_hbz_count].
proof.
conseq (actual_focused_encode_hb_z1_prepare_zero_hbz_core symbols0 bad0)
  => //=.
move=> &m _ result hpost.
move: hpost => [hbad [hprepared hframe]].
split; first exact hbad.
split; first exact hprepared.
split; first exact (prepared_zero_hbz_is_all_six _ hprepared).
exact hframe.
qed.

lemma actual_prepare_zero_hbz_all_six
    (symbols0 : BArray2048.t)
    (bad0 : BArray8.t) :
  hoare [Focus._encode_hb_z1_prepare :
    symsp = symbols0 /\ badp = bad0 /\ hp = zero_hbz /\
    count = W64.of_int mode2_hbz_count /\
    mhb = W64.of_int mode2_hbz_alphabet /\
    offset = W64.of_int mode2_hbz_offset
    ==>
    BArray8.get64 res.`2 0 = W64.zero /\
    prepared_hbz_prefix res.`1 zero_hbz mode2_hbz_count /\
    all_six_prefix res.`1 mode2_hbz_count /\
    byte_tail_frame symbols0 res.`1 mode2_hbz_count].
proof.
exact (actual_focused_encode_hb_z1_prepare_zero_hbz symbols0 bad0).
qed.

lemma hbz_freq_symbol6 :
  hbz_freq 6 = 398.
proof. by rewrite /hbz_freq. qed.

lemma hbz_start_symbol6 :
  hbz_start 6 = 312.
proof. by rewrite /hbz_start. qed.

lemma hbz_xmax_symbol6 :
  hbz_xmax 6 = 834666496.
proof.
rewrite /hbz_xmax hbz_freq_symbol6.
trivial.
qed.

lemma hbz_xmax_symbol6_product :
  hbz_xmax 6 = 2097152 * 398 /\
  2097152 * 398 = 834666496.
proof.
rewrite /hbz_xmax hbz_freq_symbol6.
trivial.
qed.

lemma hbz_xmax_symbol6_gt_shift :
  8388608 < hbz_xmax 6.
proof.
rewrite hbz_xmax_symbol6.
trivial.
qed.

lemma symbol6_div256_below_xmax x :
  x < 2147483648 => x %/ 256 < hbz_xmax 6.
proof.
move=> hx.
have hdiv : x %/ 256 < 8388608.
+ rewrite ltz_divLR 1:/#.
  smt().
rewrite hbz_xmax_symbol6.
smt().
qed.

lemma symbol6_normalization_len_le1 x :
  rans_initial_state <= x < 2147483648 =>
  0 <= mode2_normalization_len x 6 <= 1.
proof.
move=> [hxlo hxhi].
rewrite /mode2_normalization_len /renorm_len hbz_xmax_symbol6.
case (x < 834666496) => // _.
have hsmall := symbol6_div256_below_xmax x hxhi.
rewrite hbz_xmax_symbol6 in hsmall.
smt().
qed.

lemma all_six_initial_state :
  rans_initial_state = 8388608.
proof. by rewrite /rans_initial_state. qed.

lemma all_six_state_1 :
  (encode_trace (nseq 1 6)).`1 = 21582496.
proof.
rewrite nseq1 /encode_trace /= /mode2_normalized_state /renorm_reduced
        /hbz_xmax hbz_freq_symbol6 /rans_initial_state /byte_radix
        /hbz_fast_encode_step /hbz_bias hbz_freq_symbol6
        hbz_start_symbol6 /hbz_required_quotient /hbz_complement
        /rans_scale.
trivial.
qed.

lemma all_six_state_2 :
  (encode_trace (nseq 2 6)).`1 = 55528910.
proof.
rewrite (nseqS 1 6) 1:/# /= all_six_state_1.
rewrite /encode_trace /= /mode2_normalized_state /renorm_reduced
        hbz_xmax_symbol6 /byte_radix
        /hbz_fast_encode_step /hbz_bias hbz_freq_symbol6
        hbz_start_symbol6 /hbz_required_quotient /hbz_complement
        /rans_scale.
trivial.
qed.

lemma all_six_state_3 :
  (encode_trace (nseq 3 6)).`1 = 142868116.
proof.
rewrite (nseqS 2 6) 1:/# /=.
rewrite /encode_trace /= all_six_state_2 /mode2_normalized_state
        /renorm_reduced hbz_xmax_symbol6 /byte_radix
        /hbz_fast_encode_step /hbz_bias hbz_freq_symbol6
        hbz_start_symbol6 /hbz_required_quotient /hbz_complement
        /rans_scale.
trivial.
qed.

lemma all_six_state_4 :
  (encode_trace (nseq 4 6)).`1 = 367580518.
proof.
rewrite (nseqS 3 6) 1:/# /=.
rewrite /encode_trace /= all_six_state_3 /mode2_normalized_state
        /renorm_reduced hbz_xmax_symbol6 /byte_radix
        /hbz_fast_encode_step /hbz_bias hbz_freq_symbol6
        hbz_start_symbol6 /hbz_required_quotient /hbz_complement
        /rans_scale.
trivial.
qed.

lemma all_six_len1_zero_emission :
  size (encode_trace (nseq 1 6)).`2 = 0.
proof.
rewrite nseq1 /encode_trace /= /mode2_normalization_bytes /renorm_bytes
        /hbz_xmax hbz_freq_symbol6 /rans_initial_state /byte_radix.
trivial.
qed.

lemma all_six_len2_zero_emission :
  size (encode_trace (nseq 2 6)).`2 = 0.
proof.
rewrite (nseqS 1 6) 1:/# /= all_six_state_1 all_six_len1_zero_emission.
rewrite /mode2_normalization_bytes /renorm_bytes /hbz_xmax /hbz_freq
        /byte_radix.
trivial.
qed.

lemma all_six_len3_zero_emission :
  size (encode_trace (nseq 3 6)).`2 = 0.
proof.
rewrite (nseqS 2 6) 1:/# /= all_six_state_2 all_six_len2_zero_emission.
rewrite /mode2_normalization_bytes /renorm_bytes /hbz_xmax /hbz_freq
        /byte_radix.
trivial.
qed.

lemma all_six_len4_zero_emission :
  size (encode_trace (nseq 4 6)).`2 = 0.
proof.
rewrite (nseqS 3 6) 1:/# /= all_six_state_3 all_six_len3_zero_emission.
rewrite /mode2_normalization_bytes /renorm_bytes /hbz_xmax /hbz_freq
        /byte_radix.
trivial.
qed.

lemma all_six_first_four_no_normalization :
  size (encode_trace (nseq 1 6)).`2 = 0 /\
  size (encode_trace (nseq 2 6)).`2 = 0 /\
  size (encode_trace (nseq 3 6)).`2 = 0 /\
  size (encode_trace (nseq 4 6)).`2 = 0.
proof.
split; first exact all_six_len1_zero_emission.
split; first exact all_six_len2_zero_emission.
split; first exact all_six_len3_zero_emission.
exact all_six_len4_zero_emission.
qed.

lemma all_six_normalization_budget n :
  0 <= n <= mode2_hbz_count =>
  size (encode_trace (nseq n 6)).`2 <= max 0 (n - 4).
proof.
elim/natind: n => [n hnneg|n hn ih].
+ move=> _.
   smt().
+ move=> hnle.
   have hcase : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ 4 <= n by smt().
   elim: hcase.
   - move=> ->.
     rewrite all_six_len1_zero_emission.
     smt().
   move=> hcase1.
   elim: hcase1.
   - move=> ->.
     rewrite all_six_len2_zero_emission.
     smt().
   move=> hcase2.
   elim: hcase2.
   - move=> ->.
     rewrite all_six_len3_zero_emission.
     smt().
   move=> hcase3.
   elim: hcase3.
   - move=> ->.
     rewrite all_six_len4_zero_emission.
     smt().
   move=> hge4.
   rewrite nseqS 1:hn /=.
   have hcanon : canonical_symbol_list (nseq n 6).
   + rewrite canonical_symbol_list_nth => i hi.
     rewrite size_nseq in hi.
     have hi_n : 0 <= i < n by smt().
     rewrite (nth_nseq 0 i n 6 hi_n) /mode2_hbz_alphabet.
     smt().
   have hstate := encode_trace_state_bounds (nseq n 6) hcanon.
   have hstep : size (mode2_normalization_bytes (encode_trace (nseq n 6)).`1 6) <= 1.
   + have [hsize hbound] := mode2_normalization_bytes_size 6 (encode_trace (nseq n 6)).`1 _ hstate.
     * rewrite /mode2_hbz_alphabet.
       smt().
     rewrite hsize.
     have [_ hle1] := symbol6_normalization_len_le1 _ hstate.
     exact hle1.
   rewrite /encode_trace /= size_cat.
   have hmax0 : max 0 (n - 4) = n - 4 by smt().
   have hmax1 : max 0 (n + 1 - 4) = n + 1 - 4 by smt().
   have hnbound : 0 <= n <= mode2_hbz_count by smt().
   have hih := ih hnbound.
   smt().
qed.

lemma all_six_list_normalization_budget symbols :
  all_six_list symbols /\ size symbols <= mode2_hbz_count =>
  size (encode_trace symbols).`2 <= max 0 (size symbols - 4).
proof.
move=> [hallsix hsize].
have hnonneg := size_ge0 symbols.
have heq := all_six_list_eq_nseq symbols hallsix.
have hbudget := all_six_normalization_budget (size symbols) _.
+ rewrite /mode2_hbz_count.
  rewrite /mode2_hbz_count in hsize.
  smt().
rewrite -heq in hbudget.
exact hbudget.
qed.

lemma all_six_trace_fits_mode2 symbols :
  all_six_prefix symbols mode2_hbz_count =>
  size (encode_trace (symbol_list_of_array symbols)).`2 <= 1020 /\
  4 <= size (trace_bytes (symbol_list_of_array symbols)) <= mode2_hbz_count.
proof.
move=> hprefix.
have hnorm :
    size (encode_trace (symbol_list_of_array symbols)).`2 <= 1020.
+ rewrite (all_six_prefix_symbol_list symbols hprefix).
  have hbudget := all_six_normalization_budget mode2_hbz_count _.
  * rewrite /mode2_hbz_count.
    smt().
  rewrite /mode2_hbz_count in hbudget.
  exact hbudget.
split; first exact hnorm.
rewrite (all_six_prefix_symbol_list symbols hprefix).
rewrite /trace_bytes.
rewrite size_cat /= -encode_trace_bytes_segments.
have hbudget := all_six_normalization_budget mode2_hbz_count _.
+ rewrite /mode2_hbz_count.
   smt().
have hnonneg : 0 <= size (encode_trace (nseq mode2_hbz_count 6)).`2 by
  exact (size_ge0 (encode_trace (nseq mode2_hbz_count 6)).`2).
rewrite /mode2_hbz_count in hbudget.
rewrite /mode2_hbz_count.
smt().
qed.

lemma all_six_mode2_trace_total_bounds :
  4 <= size (trace_bytes all_six_symbol_list) <= mode2_hbz_count.
proof.
have hprefix : all_six_prefix all_six_symbols mode2_hbz_count.
+ rewrite /all_six_prefix /all_six_symbols => i hi.
  rewrite BArray2048.initiE 1:/#.
  trivial.
rewrite /all_six_symbol_list.
have [_ hbound] := all_six_trace_fits_mode2 all_six_symbols hprefix.
exact hbound.
qed.

end Mode2RansAllSixBudget.
