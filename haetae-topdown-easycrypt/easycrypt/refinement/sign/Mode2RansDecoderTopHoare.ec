require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import
  RansDecodeTarget SignatureUnpackMode2Target
  Mode2HbzCodecSpec Mode2RansDecodeRefinement
  Mode2RansDecoderGeneratedStep
  Mode2RansDecoderActualTrace.

theory Mode2RansDecoderTopHoare.

import Mode2HbzCodecSpec Mode2RansDecodeRefinement
       Mode2RansDecoderGeneratedStep
       Mode2RansDecoderActualTrace.

module Decode = RansDecodeTarget.M.

lemma actual_rans_decode_trace_refinement
    (decoded0 expected_symbols buffer0 : BArray2048.t)
    (state0 : BArray24.t)
    (encoded_size : int) :
  hoare [Decode._rans_decode :
    symsp = decoded0 /\
    statep = state0 /\
    bufp = buffer0 /\
    symbolwp = SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words /\
    dsymswp = SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words /\
    actual_mode2_decoder_trace_input
      expected_symbols buffer0 state0 encoded_size
    ==>
    actual_mode2_decoder_trace_post
      decoded0 expected_symbols res encoded_size].
proof.
proc.
seq 32 :
  (decoder_outer_trace_live
     decoded0 expected_symbols buffer0 state0 encoded_size
     symsp statep bufp symbolwp dsymswp count size_in m bad i off x /\
   cond = (i \ult count) /\
   !cond).
+ while
    (decoder_outer_trace_live
       decoded0 expected_symbols buffer0 state0 encoded_size
       symsp statep bufp symbolwp dsymswp count size_in m bad i off x /\
     cond = (i \ult count)).
  - wp.
    sp 2.
    if.
    * auto => &m />.
    * seq 14 :
        (decoder_outer_trace_live
           decoded0 expected_symbols buffer0 state0 encoded_size
           symsp statep bufp symbolwp dsymswp count size_in m bad i off x /\
         W64.to_uint i < mode2_hbz_count /\
         tmp64 =
           zeroextu64
             (generated_decoder_lookup_word_from symbolwp x `&`
              W32.of_int 65535)).
      + auto.
        move=> &hr hpre.
        move: hpre =>
          [[ms0 [hms [hb [[houter hguard] hcond]]]] hnotb].
        have hi := decoder_outer_guard_index
          decoded0 expected_symbols buffer0 state0 encoded_size
          symsp{hr} statep{hr} bufp{hr} symbolwp{hr} dsymswp{hr}
          count{hr} size_in{hr} m{hr} bad{hr} i{hr} off{hr} x{hr}
          cond{hr} houter hguard hcond.
        rewrite /protect_64 /=.
        rewrite /generated_decoder_lookup_word_from
          /generated_decoder_word_index /generated_decoder_parity
          /generated_decoder_slot /=.
        case (zeroextu64 x{hr} `&` W64.of_int 1023 `&` W64.one <>
              W64.zero) => hpar.
        * simplify.
          trivial.
        * simplify.
          trivial.
      + sp 1.
        if.
        * auto => &hr hpre.
          move: hpre => [[hbdef [houter [hi htmp]]] hbtrue].
          have hbelow := decoder_outer_loaded_symbol_below_m
            decoded0 expected_symbols buffer0 state0 encoded_size
            symsp{hr} statep{hr} bufp{hr} symbolwp{hr} dsymswp{hr}
            count{hr} size_in{hr} m{hr} bad{hr} i{hr} off{hr} x{hr}
            tmp64{hr} houter hi htmp.
          move: hbelow hbdef hbtrue.
          smt().
        * seq 21 :
            (decoder_inner_trace_live
               decoded0 expected_symbols buffer0 state0 encoded_size
               symsp statep bufp symbolwp dsymswp
               count size_in m bad i off again x /\
             cond = (again <> W64.zero) /\
             !cond).
          - wp.
            while
              (decoder_inner_trace_live
                 decoded0 expected_symbols buffer0 state0 encoded_size
                 symsp statep bufp symbolwp dsymswp
                 count size_in m bad i off again x /\
               cond = (again <> W64.zero)).
            * auto => &hr hpre.
              move: hpre => [[hlive hcond_eq] hcond].
              have hagain : again{hr} <> W64.zero.
              + move: hcond.
                rewrite hcond_eq.
                trivial.
              rewrite /protect_64 /protect_8 /=.
              case (zeroextu64 x{hr} \ult W64.of_int 8388608) => hsmall.
              + have hxsmall : W32.to_uint x{hr} < rans_initial_state.
                - have hsmall_copy := hsmall.
                  move: hsmall_copy.
                  rewrite W64.ultE W2u32.to_uint_zeroextu64
                    W64.of_uintK /= /rans_initial_state.
                  trivial.
                have hoffsmall := decoder_inner_trace_off_lt_size
                  decoded0 expected_symbols buffer0 state0 encoded_size
                  symsp{hr} statep{hr} bufp{hr} symbolwp{hr} dsymswp{hr}
                  count{hr} size_in{hr} m{hr} bad{hr} i{hr} off{hr}
                  again{hr} x{hr} hlive hxsmall.
                rewrite hoffsmall /=.
                have hstep := decoder_inner_trace_step
                  decoded0 expected_symbols buffer0 state0 encoded_size
                  symsp{hr} statep{hr} bufp{hr} symbolwp{hr}
                  dsymswp{hr} count{hr} size_in{hr} m{hr} bad{hr}
                  i{hr} off{hr} again{hr} x{hr}
                  hlive hagain hxsmall.
                rewrite /append_word_byte in hstep.
                exact hstep.
              + have hxlarge :
                    !(W32.to_uint x{hr} < rans_initial_state).
                - have hsmall_copy := hsmall.
                  move: hsmall_copy.
                  rewrite W64.ultE W2u32.to_uint_zeroextu64
                    W64.of_uintK /= /rans_initial_state.
                  trivial.
                exact (decoder_inner_trace_stop
                  decoded0 expected_symbols buffer0 state0 encoded_size
                  symsp{hr} statep{hr} bufp{hr} symbolwp{hr}
                  dsymswp{hr} count{hr} size_in{hr} m{hr} bad{hr}
                  i{hr} off{hr} again{hr} x{hr} hlive hxlarge).
            * auto => &hr hpre.
              move: hpre => [[hbdef [houter [hi htmp]]] hbfalse].
              have hbound := decoder_outer_loaded_symbol_byte_bound
                decoded0 expected_symbols buffer0 state0 encoded_size
                symsp{hr} statep{hr} bufp{hr} symbolwp{hr} dsymswp{hr}
                count{hr} size_in{hr} m{hr} bad{hr} i{hr} off{hr} x{hr}
                tmp64{hr} houter hi htmp.
              have hinit := decoder_outer_to_inner_trace_actual_loaded
                decoded0 expected_symbols buffer0 state0 encoded_size
                symsp{hr} statep{hr} bufp{hr} symbolwp{hr} dsymswp{hr}
                count{hr} size_in{hr} m{hr} bad{hr} i{hr} off{hr} x{hr}
                tmp64{hr} houter hi htmp hbound.
              split.
              + split; first exact hinit.
                trivial.
              + move=> again1 cond0 off0 x0 hnot [hlive0 heq0].
                split; first exact hlive0.
                split; first exact heq0.
                exact hnot.
          - auto => &hr [hlive [heq hnot]].
            have hagain : again{hr} = W64.zero.
            + move: hnot.
              rewrite heq.
              smt().
            have hnext := decoder_inner_trace_exit_to_outer
              decoded0 expected_symbols buffer0 state0 encoded_size
              symsp{hr} statep{hr} bufp{hr} symbolwp{hr} dsymswp{hr}
              count{hr} size_in{hr} m{hr} bad{hr} i{hr} off{hr}
              again{hr} x{hr} hlive hagain.
            rewrite /protect_64 (truncateu32_zeroextu64_id x{hr}).
            exact hnext.
  - auto => &hr hpre.
    move: hpre => [hsym [hstate [hbuf [htable [hdtable hinput]]]]].
    have hinput_copy := hinput.
    rewrite /actual_mode2_decoder_trace_input in hinput_copy.
    move: hinput_copy =>
      [hstream [_ [_ [_ [hsegment [_ [hcount [hsize hm]]]]]]]].
    have hlo := generated_decoder_parse32_no_low_reject
      buffer0 expected_symbols hstream hsegment.
    rewrite /rans_initial_state in hlo.
    have hhi := generated_decoder_parse32_no_high_reject
      buffer0 expected_symbols hstream hsegment.
    have hinit := decoder_outer_trace_initial
      decoded0 expected_symbols buffer0 state0 encoded_size hinput.
    have hraw :
        (((zeroextu32 (BArray2048.get8 buffer0 0) `|`
            (zeroextu32 (BArray2048.get8 buffer0 1) `<<` W8.of_int 8)) `|`
            (zeroextu32 (BArray2048.get8 buffer0 2) `<<` W8.of_int 16)) `|`
            (zeroextu32 (BArray2048.get8 buffer0 3) `<<` W8.of_int 24)) =
        generated_decoder_parse32 buffer0.
    + rewrite /generated_decoder_parse32.
      trivial.
    rewrite hsym hstate hbuf htable hdtable /protect_64.
    rewrite hcount hm hraw.
    have htr := truncateu32_zeroextu64_id
      (generated_decoder_parse32 buffer0).
    smt().
+ auto => &hr [houter [hguard hnot]].
  have hexit := decoder_outer_trace_exit_components
    decoded0 expected_symbols buffer0 state0 encoded_size
    symsp{hr} statep{hr} bufp{hr} symbolwp{hr} dsymswp{hr}
    count{hr} size_in{hr} m{hr} bad{hr} i{hr} off{hr} x{hr}
    cond{hr} houter hguard hnot.
  move: hexit => [hbad [hx [hoff [hsize [hprefix htail]]]]].
  rewrite hbad hx hoff hsize /rans_initial_state /=.
  rewrite /actual_mode2_decoder_trace_post /=.
  smt().
qed.

end Mode2RansDecoderTopHoare.
