require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  RansEncodeTarget SignaturePackMode2Target
  Mode2HbzCodecSpec Mode2HbzTableCertificate Mode2RansArrayListBridge
  Mode2RansByteStack Mode2RansNormalization
  Mode2RansEncodeRefinement Mode2RansEncoderTrace
  Mode2RansEncoderTailInvariant Mode2RansEncoderWordStep
  Mode2RansEncoderGeneratedWordStep
  Mode2RansEncoderSerializationComposition Mode2RansEncoderFinalization
  Mode2RansEncoderGeneratedFinalization.

theory Mode2RansEncoderActualTraceClosure.

import Mode2HbzCodecSpec Mode2HbzTableCertificate
       Mode2RansArrayListBridge Mode2RansByteStack
       Mode2RansNormalization
       Mode2RansEncodeRefinement
       Mode2RansEncoderTrace Mode2RansEncoderTailInvariant
       Mode2RansEncoderWordStep
       Mode2RansEncoderGeneratedWordStep
       Mode2RansEncoderSerializationComposition Mode2RansEncoderFinalization
       Mode2RansEncoderGeneratedFinalization.

module Encode = RansEncodeTarget.M.

op encoder_trace_post
    (enc0 symbols0 : BArray2048.t)
    (result : BArray2048.t * BArray16.t) : bool =
  BArray16.get64 result.`2 1 <> W64.zero \/
  (BArray16.get64 result.`2 1 = W64.zero /\
   0 <= W64.to_uint (BArray16.get64 result.`2 0) <= 1020 /\
   4 <= mode2_hbz_count -
     W64.to_uint (BArray16.get64 result.`2 0) <= mode2_hbz_count /\
   segment_matches result.`1
     (W64.to_uint (BArray16.get64 result.`2 0))
     (trace_bytes (symbol_list_of_array symbols0)) /\
   W64.to_uint (BArray16.get64 result.`2 0) +
     size (trace_bytes (symbol_list_of_array symbols0)) =
     mode2_hbz_count /\
   prefix_frame enc0 result.`1
     (W64.to_uint (BArray16.get64 result.`2 0))).

op encoder_after_inner_ready
    (enc0 symbols0 encp : BArray2048.t)
    (i : W64.t) (s : W8.t) (x : W32.t) (off : W64.t)
    (x_max rcp bias packed complement shift : W32.t) : bool =
  0 <= W64.to_uint i < mode2_hbz_count /\
  s = BArray2048.get8 symbols0 (W64.to_uint i) /\
  x_max = hbz_xmax_word (W8.to_uint s) /\
  rcp = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 1) /\
  bias = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 2) /\
  packed = BArray528.get32
    SignaturePackMode2Target.jmode2_hb_z1_esyms
    (4 * W8.to_uint s + 3) /\
  complement = packed `&` W32.of_int 65535 /\
  shift = protect_32 (packed `>>` W8.of_int 16) init_msf /\
  !(x_max \ule x) /\
  encoder_inner_tail_live enc0
    (symbol_suffix symbols0 (W64.to_uint i + 1))
    (W8.to_uint s) x off encp.

op encoder_after_shift_ready
    (enc0 symbols0 encp : BArray2048.t)
    (i : W64.t) (s : W8.t) (x : W32.t) (off : W64.t)
    (x_max rcp bias packed complement shift q : W32.t) : bool =
  encoder_after_inner_ready enc0 symbols0 encp i s x off
    x_max rcp bias packed complement shift /\
  q = encoder_shift_ladder
    (truncateu32
      (((zeroextu64 x) * (zeroextu64 rcp)) `>>` W8.of_int 32)) shift.

op encoder_before_shift_ready
    (enc0 symbols0 encp : BArray2048.t)
    (i : W64.t) (s : W8.t) (x : W32.t) (off : W64.t)
    (x_max rcp bias packed complement shift q : W32.t) : bool =
  encoder_after_inner_ready enc0 symbols0 encp i s x off
    x_max rcp bias packed complement shift /\
  q = truncateu32
    (((zeroextu64 x) * (zeroextu64 rcp)) `>>` W8.of_int 32).

lemma encoder_generated_success_outer_post
    (enc0 symbols0 encp : BArray2048.t)
    (statep state0 : BArray16.t)
    (symsp : BArray2048.t) (esymsp : BArray528.t)
    (count i off : W64.t) (s : W8.t) (x x_max rcp bias packed
      complement shift : W32.t) :
  statep = state0 =>
  symsp = symbols0 =>
  esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms =>
  count = W64.of_int mode2_hbz_count =>
  mode2_hbz_symbol_stream symbols0 =>
  encoder_after_inner_ready enc0 symbols0 encp i s x off
    x_max rcp bias packed complement shift =>
  !(off \ult W64.of_int 4) =>
  statep = state0 /\
  symsp = symbols0 /\
  esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
  count = W64.of_int mode2_hbz_count /\
  mode2_hbz_symbol_stream symbols0 /\
  0 <= W64.to_uint i <= mode2_hbz_count /\
  (W64.zero = W64.zero \/ W64.zero = W64.one) /\
  (W64.zero = W64.zero =>
    encoder_outer_tail_inv enc0 symbols0 encp (W64.to_uint i)
      (generated_loaded_nested_update x rcp bias complement shift) off).
proof.
move=> hstate hsymsp hesymsp hcount hstream hready hoff.
rewrite /encoder_after_inner_ready in hready.
move: hready =>
  [hi [hs [hxmax [hrcp [hbias [hpacked [hcomp
   [hshift [hguarddone hlive]]]]]]]]].
move: hlive => [hsrange hinner].
have hexit := encoder_inner_tail_exit_exact enc0
  (symbol_suffix symbols0 (W64.to_uint i + 1))
  (W8.to_uint s) x off encp hsrange hinner _.
+ rewrite -hxmax.
  exact hguarddone.
have hword := generated_loaded_nested_word_update x s rcp bias packed
  complement shift _ hrcp hbias hpacked hcomp hshift.
+ smt().
have hofflo : 4 <= W64.to_uint off.
+ rewrite W64.ultE W64.of_uintK /= in hoff.
  smt(W64.to_uint_cmp).
have hnext := encoder_outer_tail_advance_success enc0 symbols0 encp
  (W64.to_uint i) (W8.to_uint s) x off hstream hi _ hsrange
  hofflo hexit.
+ rewrite hs.
  trivial.
split; first exact hstate.
split; first exact hsymsp.
split; first exact hesymsp.
split; first exact hcount.
split; first exact hstream.
split; first by smt().
split; first by left.
move=> _.
rewrite hword.
exact hnext.
qed.

lemma encoder_generated_failure_outer_post
    (enc0 symbols0 encp : BArray2048.t)
    (statep state0 : BArray16.t)
    (symsp : BArray2048.t) (esymsp : BArray528.t)
    (count i off : W64.t) (s : W8.t) (x x_max rcp bias packed
      complement shift : W32.t) :
  statep = state0 =>
  symsp = symbols0 =>
  esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms =>
  count = W64.of_int mode2_hbz_count =>
  mode2_hbz_symbol_stream symbols0 =>
  encoder_after_inner_ready enc0 symbols0 encp i s x off
    x_max rcp bias packed complement shift =>
  statep = state0 /\
  symsp = symbols0 /\
  esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
  count = W64.of_int mode2_hbz_count /\
  mode2_hbz_symbol_stream symbols0 /\
  0 <= W64.to_uint i <= mode2_hbz_count /\
  (W64.one = W64.zero \/ W64.one = W64.one) /\
  (W64.one = W64.zero =>
    encoder_outer_tail_inv enc0 symbols0 encp (W64.to_uint i) x off).
proof.
move=> hstate hsym hesym hcount hstream hready.
have hi : 0 <= W64.to_uint i < mode2_hbz_count.
- move: hready.
  rewrite /encoder_after_inner_ready.
  smt().
split; first exact hstate.
split; first exact hsym.
split; first exact hesym.
split; first exact hcount.
split; first exact hstream.
split; first by smt().
split; first by right.
move=> honezero.
have hcontra : W64.to_uint W64.one = W64.to_uint W64.zero.
- rewrite honezero.
  trivial.
rewrite W64.to_uint1 W64.to_uint0 in hcontra.
smt().
qed.

lemma encoder_outer_tail_guard_exit_zero
    (enc0 symbols0 encp : BArray2048.t)
    (i : W64.t) (x : W32.t) (off : W64.t) :
  !(W64.zero \ult i) =>
  encoder_outer_tail_inv enc0 symbols0 encp (W64.to_uint i) x off =>
  encoder_outer_tail_inv enc0 symbols0 encp 0 x off.
proof.
move=> hguard hlive.
have hi0 : W64.to_uint i = 0.
+ rewrite W64.ultE W64.to_uint0 in hguard.
  have hiu := W64.to_uint_cmp i.
  smt().
rewrite -hi0.
exact hlive.
qed.

lemma actual_rans_encode_trace_closure
    (enc0 : BArray2048.t)
    (state0 : BArray16.t)
    (symbols0 : BArray2048.t) :
  hoare [Encode._rans_encode :
    encp = enc0 /\
    statep = state0 /\
    symsp = symbols0 /\
    esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
    count = W64.of_int mode2_hbz_count /\
    mode2_hbz_symbol_stream symbols0
    ==> encoder_trace_post enc0 symbols0 res].
proof.
proc.
seq 5 :
  (statep = state0 /\
   symsp = symbols0 /\
   esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
   count = W64.of_int mode2_hbz_count /\
   mode2_hbz_symbol_stream symbols0 /\
   (bad = W64.zero \/ bad = W64.one) /\
   !(W64.zero \ult i) /\
   (bad = W64.zero =>
      encoder_outer_tail_inv enc0 symbols0 encp
        (W64.to_uint i) x off)).
+ while
  (statep = state0 /\
   symsp = symbols0 /\
   esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
   count = W64.of_int mode2_hbz_count /\
   mode2_hbz_symbol_stream symbols0 /\
   0 <= W64.to_uint i <= mode2_hbz_count /\
   (bad = W64.zero \/ bad = W64.one) /\
   (bad = W64.zero =>
      encoder_outer_tail_inv enc0 symbols0 encp
        (W64.to_uint i) x off)).
+ if.
  - auto => &m />; smt().
  - seq 22 :
      (statep = state0 /\
       symsp = symbols0 /\
       esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
       count = W64.of_int mode2_hbz_count /\
       mode2_hbz_symbol_stream symbols0 /\
       bad = W64.zero /\
       encoder_after_inner_ready enc0 symbols0 encp i s x off
         x_max rcp_freq bias packed cmpl_freq rcp_shift).
    + wp.
    while
      (x_max = hbz_xmax_word (W8.to_uint s) /\
       encoder_inner_tail_live enc0
         (symbol_suffix symbols0 (W64.to_uint i + 1))
         (W8.to_uint s) x off encp).
    * auto => &m hboth.
      move: hboth => [[hxmax hlive] hguard].
      have [hs hinv] := hlive.
      have hguard' : hbz_xmax_word (W8.to_uint s{m}) \ule x{m}.
      + rewrite -hxmax.
        exact hguard.
      have hprogress := encoder_inner_tail_live_progress enc0
        (symbol_suffix symbols0 (W64.to_uint i{m} + 1))
        (W8.to_uint s{m}) x{m} off{m} encp{m}
        hlive hguard'.
      split; first exact hxmax.
      exact hprogress.
    * auto.
    auto => &m houter.
    move: houter => [[hout higuard] hbadzero].
    move: hout =>
      [hstate [hsym [hesym [hcount [hstream [hi [hbaddisj hlive]]]]]]].
    rewrite W64.ultE W64.to_uint0 in higuard.
    have hipos : 0 < W64.to_uint i{m} by exact higuard.
    have hj :
      W64.to_uint (i{m} - W64.one) = W64.to_uint i{m} - 1.
    + exact (cursor_decrement_no_underflow i{m} hipos).
    have hjbound :
      0 <= W64.to_uint (i{m} - W64.one) < mode2_hbz_count.
    + rewrite hj; smt().
    have hsrange := hstream
      (W64.to_uint (i{m} - W64.one)) hjbound.
    have hidx_product :
        W64.to_uint
          (zeroextu64 (BArray2048.get8 symbols0
            (W64.to_uint (i{m} - W64.one)))) *
        W64.to_uint (W64.of_int 4) < W64.modulus.
    + rewrite W8u8.to_uint_zeroextu64 W64.of_uintK /=.
      have hu := W8.to_uint_cmp
        (BArray2048.get8 symbols0
          (W64.to_uint (i{m} - W64.one))).
      smt().
    have hidx :
        W64.to_uint
          ((zeroextu64 (BArray2048.get8 symbols0
              (W64.to_uint (i{m} - W64.one)))) * W64.of_int 4) =
        4 * W8.to_uint (BArray2048.get8 symbols0
          (W64.to_uint (i{m} - W64.one))).
    + rewrite W64.to_uintM_small 1:hidx_product
              W8u8.to_uint_zeroextu64 W64.of_uintK /=.
      ring.
    have hidx1 :
        W64.to_uint
          (((zeroextu64 (BArray2048.get8 symbols0
              (W64.to_uint (i{m} - W64.one)))) * W64.of_int 4) +
            W64.one) =
        4 * W8.to_uint (BArray2048.get8 symbols0
          (W64.to_uint (i{m} - W64.one))) + 1.
    + rewrite W64.to_uintD_small 1:/# hidx W64.to_uint1.
      ring.
    have hidx2 :
        W64.to_uint
          ((((zeroextu64 (BArray2048.get8 symbols0
              (W64.to_uint (i{m} - W64.one)))) * W64.of_int 4) +
            W64.one) + W64.one) =
        4 * W8.to_uint (BArray2048.get8 symbols0
          (W64.to_uint (i{m} - W64.one))) + 2.
    + rewrite W64.to_uintD_small 1:/# hidx1 W64.to_uint1.
      ring.
    have hidx3 :
        W64.to_uint
          (((((zeroextu64 (BArray2048.get8 symbols0
              (W64.to_uint (i{m} - W64.one)))) * W64.of_int 4) +
            W64.one) + W64.one) + W64.one) =
        4 * W8.to_uint (BArray2048.get8 symbols0
          (W64.to_uint (i{m} - W64.one))) + 3.
    + rewrite W64.to_uintD_small 1:/# hidx2 W64.to_uint1.
      ring.
    have hinner := encoder_outer_tail_to_inner
      enc0 symbols0 encp{m}
      (W64.to_uint (i{m} - W64.one)) x{m} off{m}
      hstream hjbound _.
    + rewrite hj.
      have -> : W64.to_uint i{m} - 1 + 1 = W64.to_uint i{m} by ring.
      exact (hlive hbadzero).
    split.
    + rewrite hsym hesym /protect_64 /protect_32 hidx /=.
      split.
      - have [hxmax _] := actual_mode2_esym_word_fields
          (W8.to_uint (BArray2048.get8 symbols0
            (W64.to_uint (i{m} - W64.one)))) hsrange.
        exact hxmax.
      - rewrite /encoder_inner_tail_live.
        split; first exact hsrange.
        exact hinner.
    move=> encp1 off1 x1 hguarddone [hxmax1 hlive1].
    rewrite /encoder_after_inner_ready.
    split; first exact hstate.
    split; first exact hsym.
    split; first exact hesym.
    split; first exact hcount.
    split; first exact hstream.
    split; first exact hbadzero.
    split; first exact hjbound.
    split.
    + rewrite hsym.
      trivial.
    split; first exact hxmax1.
    split.
    + rewrite hsym hesym /protect_64 hidx1.
      trivial.
    split.
    + rewrite hsym hesym /protect_64 hidx2.
      trivial.
    split.
    + rewrite hsym hesym /protect_64 hidx3.
      trivial.
    split; first trivial.
    split; first by rewrite /protect_32.
    split; first exact hguarddone.
    rewrite hsym in hlive1.
    rewrite hj in hlive1.
    move: hlive1.
    smt().
    + wp.
      auto => &m hpost.
      move: hpost =>
        [hstate [hsym [hesym [hcount [hstream [hbadzero hready]]]]]].
      case (off{m} \ult W64.of_int 4) => hoff.
      -
        simplify.
        move: hready.
        rewrite /encoder_after_inner_ready.
        auto => />.
        smt(W64.to_uint1 W64.to_uint0).
      -
        simplify.
        have hsuccess := (encoder_generated_success_outer_post
          enc0 symbols0 encp{m} statep{m} state0 symsp{m} esymsp{m}
          count{m} i{m} off{m} s{m} x{m} x_max{m} rcp_freq{m}
          bias{m} packed{m} cmpl_freq{m} rcp_shift{m}
          hstate hsym hesym hcount hstream hready hoff).
        move: hsuccess =>
          [hsucc_state [hsucc_symbols [hsucc_table [hsucc_count
            [hsucc_stream [hsucc_i [hsucc_bad hsucc_live]]]]]]].
        have hlive_success :
            encoder_outer_tail_inv enc0 symbols0 encp{m}
              (W64.to_uint i{m})
              (generated_loaded_nested_update x{m} rcp_freq{m} bias{m}
                cmpl_freq{m} rcp_shift{m}) off{m}.
        + apply hsucc_live.
          trivial.
        rewrite /encoder_outer_tail_inv /generated_loaded_nested_update
          in hlive_success.
        rewrite /encoder_outer_tail_inv /generated_loaded_nested_update.
        move: hlive_success =>
          [hlive_i [hlive_x [hlive_cursor [hlive_segment
            [hlive_frame hlive_low]]]]].
        rewrite hbadzero.
        rewrite -hlive_x.
        auto.
+ auto => />.
  move=> _.
  rewrite W64.of_uintK /= /mode2_hbz_count.
  have hmod : 1024 %% 18446744073709551616 = 1024 by smt().
  rewrite hmod symbol_suffix_at_end /= /rans_initial_state
    /mode2_hbz_capacity.
  smt().
+ if.
  - wp.
    auto => &m1 hpost.
    have higuard : !(W64.zero \ult i{m1}) by
      move: hpost; smt().
    have hlive :
        encoder_outer_tail_inv enc0 symbols0 encp{m1}
          (W64.to_uint i{m1}) x{m1} off{m1} by
      move: hpost; smt().
    have hbad0 : bad{m1} = W64.zero by
      move: hpost; smt().
    have hout :
        encoder_outer_tail_inv enc0 symbols0 encp{m1} 0 x{m1} off{m1}.
    + apply (encoder_outer_tail_guard_exit_zero enc0 symbols0
        encp{m1} i{m1} x{m1} off{m1} higuard).
      apply hlive.
      trivial.
    have hfinal := generated_encoder_outer_finalize_success
      enc0 symbols0 encp{m1} x{m1} off{m1} hout.
    move: hfinal =>
      [hoff [hsize [hsegment [hcursor hframe]]]].
    rewrite /encoder_trace_post /=.
    right.
    split; first exact hbad0.
    split; first exact hoff.
    split; first exact hsize.
    split.
    + rewrite /generated_store_w32_le /= in hsegment.
      exact hsegment.
    split; first exact hcursor.
    rewrite /generated_store_w32_le /= in hframe.
    exact hframe.
  - wp.
    auto => &m2 hpost.
    rewrite /encoder_trace_post /=.
    left.
    move: hpost; smt().
qed.

end Mode2RansEncoderActualTraceClosure.
