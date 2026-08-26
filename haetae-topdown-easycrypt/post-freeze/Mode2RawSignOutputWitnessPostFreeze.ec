require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import RawSignApiTarget
               RawApiSignOutputFrame
               SignCoreChallengeTracePostFreeze
               ApiKeyMemoryBridge.

theory Mode2RawSignOutputWitnessPostFreeze.

(* This is a raw-output witness layer only.  It introduces a ghost trace that
   records the exact core-returned [sigp] immediately before the generated raw
   API copies it to [sigu].  It does not identify that serialized witness with
   a full abstract HAETAE signature object, prove a raw-memory refinement to
   the internal signer state, or add any termination/distributional claim. *)

module Sign = RawSignApiTarget.M.

module OutputCopyTrace = {
  var observed_sigp : BArray2948.t

  proc run (sigu : int, siglenu : int,
            sigp : BArray2948.t) : W64.t = {
    var r : W64.t;

    observed_sigp <- sigp;
    sigu <@ Sign._api_copy_2948_to_raw(sigu, sigp, 1474);
    Glob.mem <- storeW64 Glob.mem siglenu (W64.of_int 1474);
    r <- W64.zero;
    return r;
  }
}.

module SignRawApiPackedTrace = {
  var observed_sigp : BArray2948.t
  var observed_cp : BArray1024.t

  proc run (sigu : int, siglenu : int, mu : int, mlen : int,
            preu : int, prelen : int, rndu : int, sku : int) : W64.t = {
    var r : W64.t;
    var sig : BArray2948.t;
    var sigp : BArray2948.t;
    var sk : BArray2752.t;
    var skp : BArray2752.t;
    var rnd0 : BArray32.t;
    var rndp : BArray32.t;
    var desc : BArray32.t;
    var descp : BArray32.t;
    var ms : W64.t;

    desc <- witness;
    descp <- witness;
    rnd0 <- witness;
    rndp <- witness;
    sig <- witness;
    sigp <- witness;
    sk <- witness;
    skp <- witness;
    sigp <- sig;
    skp <- sk;
    rndp <- rnd0;
    descp <- desc;
    skp <@ Sign._api_copy_raw_to_2752_prefix(skp, sku, 1408);
    rndp <@ Sign._api_copy_raw_to_32(rndp, rndu);
    descp <- BArray32.set64 descp 0 (W64.of_int preu);
    descp <- BArray32.set64 descp 1 (W64.of_int prelen);
    descp <- BArray32.set64 descp 2 (W64.of_int mu);
    descp <- BArray32.set64 descp 3 (W64.of_int mlen);
    ms <- init_msf;
    descp <- protect_ptr descp ms;
    sigp <@
      SignCoreChallengeTracePostFreeze.SignInternalMuCpTrace.run(
        sigp, skp, rndp, descp);
    observed_cp <-
      SignCoreChallengeTracePostFreeze.SignInternalMuCpTrace.observed_cp;
    r <@ OutputCopyTrace.run(sigu, siglenu, sigp);
    observed_sigp <- OutputCopyTrace.observed_sigp;
    return r;
  }
}.

lemma sign_raw_api_exact_packed_trace :
  equiv [Sign.cryptolab_haetae_mode2_signature_internal ~
         SignRawApiPackedTrace.run :
    ={Glob.mem, sigu, siglenu, mu, mlen, preu, prelen, rndu, sku}
    ==>
    ={Glob.mem, res}].
proof.
proc.
inline OutputCopyTrace.run.
sim.
qed.

lemma signature_prefix_storeW64_disjoint
    (mem : global_mem_t) (addr base len : int)
    (sig : BArray2948.t) (w : W64.t) :
  ApiKeyMemoryBridge.disjoint_regions addr 8 base len =>
  RawApiSignOutputFrame.signature_prefix mem base sig len =>
  RawApiSignOutputFrame.signature_prefix
    (storeW64 mem addr w) base sig len.
proof.
move=> hdis hpref.
have hstable :=
  RawApiSignOutputFrame.stable_region_storeW64_disjoint
    mem addr base len w hdis.
rewrite /RawApiSignOutputFrame.signature_prefix => i hi.
rewrite (hstable i hi).
exact (hpref i hi).
qed.

lemma output_copy_trace_exact
    (sigu0 siglenu0 : int) :
  hoare [OutputCopyTrace.run :
    sigu = sigu0 /\ siglenu = siglenu0 /\
    ApiKeyMemoryBridge.valid_region_int
      sigu0 RawApiSignOutputFrame.mode2_sigbytes /\
    ApiKeyMemoryBridge.disjoint_regions
      siglenu0 RawApiSignOutputFrame.siglenbytes
      sigu0 RawApiSignOutputFrame.mode2_sigbytes
    ==>
    res = W64.zero /\
    RawApiSignOutputFrame.signature_prefix
      Glob.mem sigu0 OutputCopyTrace.observed_sigp
      RawApiSignOutputFrame.mode2_sigbytes /\
    loadW64 Glob.mem siglenu0 =
      W64.of_int RawApiSignOutputFrame.mode2_sigbytes].
proof.
proc.
wp.
exlim Glob.mem => mem_before_copy0.
exlim sigp => sig_before_copy0.
call
  (RawApiSignOutputFrame.sign_output_copy_exact_and_frames_reused
    mem_before_copy0 sig_before_copy0 sigu0).
auto => />.
move=> hsigu hlen hsum hdis heq mem hpref hframe.
split.
+ apply
    (signature_prefix_storeW64_disjoint
      mem siglenu0 sigu0
      RawApiSignOutputFrame.mode2_sigbytes sig_before_copy0
      (W64.of_int 1474)); assumption.
+ rewrite -heq.
   apply RawApiSignOutputFrame.loadW64_storeW64_same.
qed.

lemma sign_raw_api_packed_trace_exact_output
    (sigu0 siglenu0 : int) :
  hoare [SignRawApiPackedTrace.run :
    sigu = sigu0 /\ siglenu = siglenu0 /\
    ApiKeyMemoryBridge.valid_region_int
      sigu0 RawApiSignOutputFrame.mode2_sigbytes /\
    ApiKeyMemoryBridge.disjoint_regions
      siglenu0 RawApiSignOutputFrame.siglenbytes
      sigu0 RawApiSignOutputFrame.mode2_sigbytes
    ==>
    res = W64.zero /\
    RawApiSignOutputFrame.signature_prefix
      Glob.mem sigu0 SignRawApiPackedTrace.observed_sigp
      RawApiSignOutputFrame.mode2_sigbytes /\
    loadW64 Glob.mem siglenu0 =
      W64.of_int RawApiSignOutputFrame.mode2_sigbytes].
proof.
proc.
wp.
call (output_copy_trace_exact sigu0 siglenu0).
wp.
call (_ : true); first by auto.
wp.
call (_ : true); first by auto.
call (_ : true); first by auto.
auto => />.
qed.

lemma sign_raw_api_packed_trace_observed_cp_valid :
  hoare [SignRawApiPackedTrace.run :
    true
    ==>
    SignCoreChallengeTracePostFreeze.valid_mode2_carrier_challenge
      (SignCoreChallengeTracePostFreeze.challenge_of_barray
        SignRawApiPackedTrace.observed_cp)].
proof.
proc.
wp.
call (_ : true); first by auto.
wp.
call
  SignCoreChallengeTracePostFreeze.sign_internal_trace_observed_cp_valid.
wp.
call (_ : true); first by auto.
call (_ : true); first by auto.
auto.
qed.

(* The existential below ranges over serialized [BArray2948] bytes only; it
   is not an abstract [HAETAE_Algebra.signature] witness. *)
lemma raw_sign_api_success_has_serialized_output_witness
    (sigu0 siglenu0 : int) :
  hoare [Sign.cryptolab_haetae_mode2_signature_internal :
    sigu = sigu0 /\ siglenu = siglenu0 /\
    ApiKeyMemoryBridge.valid_region_int
      sigu0 RawApiSignOutputFrame.mode2_sigbytes /\
    ApiKeyMemoryBridge.disjoint_regions
      siglenu0 RawApiSignOutputFrame.siglenbytes
      sigu0 RawApiSignOutputFrame.mode2_sigbytes
    ==>
    res = W64.zero /\
    loadW64 Glob.mem siglenu0 =
      W64.of_int RawApiSignOutputFrame.mode2_sigbytes /\
    exists sigw,
      RawApiSignOutputFrame.signature_prefix
        Glob.mem sigu0 sigw
        RawApiSignOutputFrame.mode2_sigbytes].
proof.
conseq sign_raw_api_exact_packed_trace
  (sign_raw_api_packed_trace_exact_output sigu0 siglenu0).
+ move=> &1 hpre.
   exists Glob.mem{1}
     (sigu{1}, siglenu{1}, mu{1}, mlen{1},
      preu{1}, prelen{1}, rndu{1}, sku{1}) => /=.
   exact hpre.
+ move=> &1 &2 [hmem hres] [hz [hprefix hlen]].
   split; first by rewrite hres.
   split; first by rewrite hmem.
   exists SignRawApiPackedTrace.observed_sigp{2}.
   by rewrite hmem.
qed.

end Mode2RawSignOutputWitnessPostFreeze.
