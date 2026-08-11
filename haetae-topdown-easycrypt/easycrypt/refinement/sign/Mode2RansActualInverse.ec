require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  RansEncodeTarget RansDecodeTarget HbzFullEncodeTarget
  SignaturePackMode2Target SignatureUnpackMode2Target
  Mode2HbzCodecSpec Mode2RansEncodeRefinement
  Mode2RansDecodeRefinement Mode2RansSuffixCopy.

theory Mode2RansActualInverse.

import Mode2HbzCodecSpec Mode2RansEncodeRefinement
       Mode2RansDecodeRefinement Mode2RansSuffixCopy.

module Encode = RansEncodeTarget.M.
module Decode = RansDecodeTarget.M.
module Copy = HbzFullEncodeTarget.M.

module Mode2RansActualHarness = {
  var encoder_off : W64.t
  var encoder_bad : W64.t
  var encoded_size : W64.t
  var decoder_ran : bool
  var decoder_count_input : W64.t
  var decoder_size_input : W64.t
  var decoder_alphabet_input : W64.t
  var decoder_off : W64.t
  var decoder_bad : W64.t

  proc run(enc0 : BArray2048.t,
           copied0 : BArray2048.t,
           decoded0 : BArray2048.t,
           encoder_state0 : BArray16.t,
           decoder_state0 : BArray24.t,
           symbols : BArray2048.t) :
      BArray2048.t * BArray2048.t * BArray24.t = {
    var encoded : BArray2048.t;
    var copied : BArray2048.t;
    var decoded : BArray2048.t;
    var encoder_state : BArray16.t;
    var decoder_state : BArray24.t;

    (encoded, encoder_state) <@ Encode._rans_encode(
      enc0, encoder_state0, symbols,
      SignaturePackMode2Target.jmode2_hb_z1_esyms,
      W64.of_int mode2_hbz_count);
    encoder_off <- BArray16.get64 encoder_state 0;
    encoder_bad <- BArray16.get64 encoder_state 1;
    decoder_ran <- false;
    encoded_size <- W64.zero;
    copied <- copied0;
    decoded <- decoded0;
    decoder_state <- decoder_state0;
    decoder_count_input <- W64.zero;
    decoder_size_input <- W64.zero;
    decoder_alphabet_input <- W64.zero;
    decoder_off <- W64.zero;
    decoder_bad <- W64.one;

    if (encoder_bad = W64.zero) {
      encoded_size <- W64.of_int mode2_hbz_count - encoder_off;
      copied <@ Copy.__copy_encoded_suffix(
        copied, encoded, encoder_off, encoded_size);
      decoder_state <- BArray24.set64 decoder_state 0
        (W64.of_int mode2_hbz_count);
      decoder_state <- BArray24.set64 decoder_state 1 encoded_size;
      decoder_state <- BArray24.set64 decoder_state 2
        (W64.of_int mode2_hbz_alphabet);
      decoder_count_input <- BArray24.get64 decoder_state 0;
      decoder_size_input <- BArray24.get64 decoder_state 1;
      decoder_alphabet_input <- BArray24.get64 decoder_state 2;
      decoder_ran <- true;
      (decoded, decoder_state) <@ Decode._rans_decode(
        decoded, decoder_state, copied,
        SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words,
        SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words);
      decoder_off <- BArray24.get64 decoder_state 0;
      decoder_bad <- BArray24.get64 decoder_state 1;
    }

    return (encoded, decoded, decoder_state);
  }
}.

lemma actual_rans_harness_branches_on_encoder_result
    (enc0 copied0 decoded0 : BArray2048.t)
    (encoder_state0 : BArray16.t)
    (decoder_state0 : BArray24.t)
    (symbols : BArray2048.t) :
  hoare [Mode2RansActualHarness.run :
    arg = (enc0, copied0, decoded0, encoder_state0,
           decoder_state0, symbols) /\
    mode2_hbz_symbol_stream symbols
    ==>
    (Mode2RansActualHarness.encoder_bad = W64.zero \/
     Mode2RansActualHarness.encoder_bad = W64.one) /\
    (Mode2RansActualHarness.decoder_ran <=>
       Mode2RansActualHarness.encoder_bad = W64.zero) /\
    (Mode2RansActualHarness.decoder_ran =>
       Mode2RansActualHarness.decoder_count_input =
         W64.of_int mode2_hbz_count /\
       Mode2RansActualHarness.decoder_size_input =
         Mode2RansActualHarness.encoded_size /\
       Mode2RansActualHarness.decoder_alphabet_input =
         W64.of_int mode2_hbz_alphabet)].
proof.
proc.
seq 1 :
  (encoder_state0 = encoder_state0 /\
   symbols = symbols /\
   mode2_hbz_symbol_stream symbols /\
   (BArray16.get64 encoder_state 1 = W64.zero \/
    BArray16.get64 encoder_state 1 = W64.one)).
+ call (actual_rans_encode_mode2_control
    enc0 encoder_state0 symbols).
  auto.
+ sp 12.
  if.
  - wp.
    call (_ : true ==> true); first by auto.
    wp.
    call (_ : true ==> true); first by auto.
    auto.
  - auto.
qed.

op actual_core_success_result
    (encoder_bad decoder_bad decoder_off encoded_size : W64.t)
    (decoder_ran : bool) : bool =
  encoder_bad = W64.zero /\
  decoder_ran /\
  decoder_bad = W64.zero /\
  decoder_off = encoded_size.

(*
  OBL-RANS-CORE-INVERSE remains the semantic edge from this exact harness to:
    - decoded symbols equal the encoder input symbols;
    - decoder state is 2^23;
    - decoder consumes exactly encoded_size;
    - required array frames.
  No theorem below assumes [actual_core_success_result].
*)

end Mode2RansActualInverse.
