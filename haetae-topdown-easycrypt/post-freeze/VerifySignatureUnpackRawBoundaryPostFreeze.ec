require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8 BArray24 BArray528 BArray1024 BArray2048
               BArray2948 BArray8192
               RawVerifyApiTarget SignatureUnpackMode2Target
               Mode2HbzCodecSpec Mode2VerifyPrepareNorm
               VerifyHbzRansSuccessCanonicalPostFreeze.

theory VerifySignatureUnpackRawBoundaryPostFreeze.

module Raw = RawVerifyApiTarget.M.
module Focused = SignatureUnpackMode2Target.M.

lemma raw_mode2_h_symbol_words_eq :
  RawVerifyApiTarget.jmode2_h_symbol_words =
  SignatureUnpackMode2Target.jmode2_h_symbol_words.
proof. by trivial. qed.

lemma raw_mode2_h_dsyms_words_eq :
  RawVerifyApiTarget.jmode2_h_dsyms_words =
  SignatureUnpackMode2Target.jmode2_h_dsyms_words.
proof. by trivial. qed.

lemma raw_mode2_hbz_symbol_words_eq :
  RawVerifyApiTarget.jmode2_hb_z1_symbol_words =
  SignatureUnpackMode2Target.jmode2_hb_z1_symbol_words.
proof. by trivial. qed.

lemma raw_mode2_hbz_dsyms_words_eq :
  RawVerifyApiTarget.jmode2_hb_z1_dsyms_words =
  SignatureUnpackMode2Target.jmode2_hb_z1_dsyms_words.
proof. by trivial. qed.

lemma raw_unpack_sig_full_equiv_focused :
  equiv [Raw._unpack_sig_full ~ Focused._unpack_sig_full :
    ={Glob.mem, cp, lowp, hbzp, hp, badp, sigp,
      h_symbolwp, h_dsymswp, hb_symbolwp, hb_dsymswp,
      lcount_i, hb_count_i, hb_m_i, hb_offset_i,
      h_count_i, h_m_i, h_offset_i,
      base_hb_i, base_h_i, payload_limit_i}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma raw_unpack_sig_full_mode2_challenge_canonical
    (cp0 : BArray1024.t) (low0 hbz0 : BArray8192.t)
    (bad0 : BArray8.t) (sig0 : BArray2948.t) :
  hoare [Raw._unpack_sig_full :
    cp = cp0 /\ lowp = low0 /\ hbzp = hbz0 /\
    badp = bad0 /\ sigp = sig0 /\
    lcount_i = 4 /\ hb_count_i = 1024 /\
    hb_m_i = 13 /\ hb_offset_i = 6
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge res.`1].
proof.
conseq raw_unpack_sig_full_equiv_focused
  (VerifyHbzRansSuccessCanonicalPostFreeze.unpack_sig_full_mode2_verify_canonical
    cp0 low0 hbz0 bad0 sig0).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists
    (cp{1}, lowp{1}, hbzp{1}, hp{1}, badp{1}, sigp{1},
     h_symbolwp{1}, h_dsymswp{1}, hb_symbolwp{1}, hb_dsymswp{1},
     lcount_i{1}, hb_count_i{1}, hb_m_i{1}, hb_offset_i{1},
     h_count_i{1}, h_m_i{1}, h_offset_i{1},
     base_hb_i{1}, base_h_i{1}, payload_limit_i{1}).
  by auto.
+ move=> &1 &2 [_ hres] [hcanonical _].
  rewrite hres.
  exact hcanonical.
qed.

module RawUnpackSignatureMode2 = {
  proc run
      (cp : BArray1024.t,
       lowp hbzp hp : BArray8192.t,
       badp : BArray8.t,
       sigp : BArray2948.t)
      : BArray1024.t * BArray8192.t * BArray8192.t *
        BArray8192.t * BArray8.t = {
    (cp, lowp, hbzp, hp, badp) <@ Raw._unpack_sig_full
      (cp, lowp, hbzp, hp, badp, sigp,
       RawVerifyApiTarget.jmode2_h_symbol_words,
       RawVerifyApiTarget.jmode2_h_dsyms_words,
       RawVerifyApiTarget.jmode2_hb_z1_symbol_words,
       RawVerifyApiTarget.jmode2_hb_z1_dsyms_words,
       4, 1024, 13, 6, 512, 13, 239, 132, 7, 416);
    return (cp, lowp, hbzp, hp, badp);
  }
}.

lemma raw_unpack_signature_mode2_equiv_focused_wrapper :
  equiv [RawUnpackSignatureMode2.run ~ Focused.unpack_sig_mode2_full_jazz :
    ={Glob.mem, cp, lowp, hbzp, hp, badp, sigp}
    ==>
    ={Glob.mem, res}].
proof.
proc.
call raw_unpack_sig_full_equiv_focused.
auto.
qed.

lemma raw_unpack_signature_mode2_verify_canonical
    (cp0 : BArray1024.t) (low0 hbz0 : BArray8192.t)
    (bad0 : BArray8.t) (sig0 : BArray2948.t) :
  hoare [RawUnpackSignatureMode2.run :
    cp = cp0 /\
    lowp = low0 /\
    hbzp = hbz0 /\
    badp = bad0 /\
    sigp = sig0
    ==>
    Mode2VerifyPrepareNorm.canonical_challenge res.`1 /\
    Mode2VerifyPrepareNorm.canonical_signed_low res.`2 /\
    (BArray8.get64 res.`5 0 = W64.zero =>
      Mode2VerifyPrepareNorm.canonical_hbz_mode2 res.`3 /\
      Mode2VerifyPrepareNorm.coeff_tail_frame
        hbz0 res.`3 Mode2HbzCodecSpec.mode2_hbz_count)].
proof.
conseq raw_unpack_signature_mode2_equiv_focused_wrapper
  (VerifyHbzRansSuccessCanonicalPostFreeze.unpack_sig_mode2_full_jazz_verify_canonical
       cp0 low0 hbz0 bad0 sig0).
+ move=> &1 hpre.
  exists Glob.mem{1}.
  exists (cp{1}, lowp{1}, hbzp{1}, hp{1}, badp{1}, sigp{1}).
  by auto.
+ move=> &1 &2 [_ hres] hpost.
  rewrite hres.
  exact hpost.
qed.

end VerifySignatureUnpackRawBoundaryPostFreeze.
