require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import RawSignApiTarget
               ExtractedChallengeAbsorb
               SignChallengeM23AbsorbComponentsPostFreeze
               SignChallengeM23SamplerBridgePostFreeze
               SignChallengeM23CarrierBridgePostFreeze
               Mode2ConcreteHonestSigningTranscriptPostFreeze
               Mode2ChallengeROMProgrammingPostFreeze
               HAETAE_Algebra.

theory SignCoreChallengeTracePostFreeze.

(* Ghost observation only.  The generated Sign core is mirrored so that its
   last challenge array remains nameable after the rejection loop; thin
   wrappers carry that ghost to the internal signer and raw ABI trace while
   preserving their result and memory semantics.  The uninstrumented API does
   not itself expose cp, and this layer makes no termination, distributional,
   transcript-validity, SHAKE-to-RO, or challenge_from_seed claim. *)

module Sign = RawSignApiTarget.M.

op challenge_of_barray =
  SignChallengeM23CarrierBridgePostFreeze.challenge_of_barray.

op valid_mode2_carrier_challenge =
  SignChallengeM23CarrierBridgePostFreeze.valid_mode2_carrier_challenge.

op mu32_prefix =
  SignChallengeM23CarrierBridgePostFreeze.mu32_prefix.

op mu32_of_mu64 (mu : BArray64.t) : BArray32.t =
  BArray32.init (fun i => BArray64.get8 mu i).

op concrete_honest_site_clear
    (sk : HAETAE_Algebra.skey) (m : HAETAE_Algebra.message)
    (ctx : HAETAE_Algebra.context) (coins : HAETAE_Algebra.random_coins)
    (cp : BArray1024.t) : bool =
  valid_mode2_carrier_challenge (challenge_of_barray cp) /\
  ! Mode2ChallengeROMProgrammingPostFreeze.mode2_fs_with_aborts_failure
      (Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2
        sk m ctx coins cp)
      (Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_programming_site_mode2
        sk m ctx coins cp).

lemma mu32_of_mu64_prefix mu :
  mu32_prefix mu (mu32_of_mu64 mu).
proof.
rewrite /mu32_prefix
        /SignChallengeM23CarrierBridgePostFreeze.mu32_prefix
        /SignChallengeM23SamplerBridgePostFreeze.mu32_prefix
        /SignChallengeM23AbsorbComponentsPostFreeze.mu32_prefix
        /ExtractedChallengeAbsorb.mu32_prefix
        /mu32_of_mu64.
move=> i hi.
by rewrite BArray32.initiE 1:hi.
qed.

lemma sign_challenge_mode2_valid_carrier :
  hoare [Sign._sf_challenge_mode2 :
    true
    ==>
    valid_mode2_carrier_challenge (challenge_of_barray res.`1)].
proof.
proc.
exlim mup => mup0.
call
  (SignChallengeM23CarrierBridgePostFreeze.raw_sign_challenge_m23_mode2_valid_carrier
    (mu32_of_mu64 mup0)).
wp.
call (_ : true ==> true); first by auto.
wp.
call (_ : true ==> true); first by auto.
wp.
call (_ : true ==> true); first by auto.
wp.
call (_ : true ==> true); first by auto.
auto => />.
rewrite /protect_64 /protect_ptr.
split; first exact (mu32_of_mu64_prefix mup0).
move=> _ _ _ result s hsubset hcard heq.
exists s.
split.
+ split; [exact hsubset | exact hcard].
+ exact heq.
qed.

lemma sign_round_challenge_mode2_valid_carrier :
  hoare [Sign._sf_round_challenge_mode2 :
    true
    ==>
    valid_mode2_carrier_challenge (challenge_of_barray res.`1)].
proof.
proc.
call sign_challenge_mode2_valid_carrier.
wp.
call (_ : true ==> true); first by auto.
wp.
call (_ : true ==> true); first by auto.
wp.
call (_ : true ==> true); first by auto.
wp.
call (_ : true ==> true); first by auto.
call (_ : true ==> true); first by auto.
call (_ : true ==> true); first by auto.
call (_ : true ==> true); first by auto.
auto.
qed.

module SignCoreCpTrace = {
  var observed_cp : BArray1024.t

  proc run(sigp : BArray2948.t, skp : BArray2752.t,
           rndp : BArray32.t, mup : BArray64.t) : BArray2948.t = {
    var seedbuf : BArray64.t;
    var seedbufp : BArray64.t;
    var key : BArray32.t;
    var keyp : BArray32.t;
    var b : BArray1.t;
    var bp : BArray1.t;
    var counter : BArray8.t;
    var counterp : BArray8.t;
    var a1 : BArray32768.t;
    var a1p : BArray32768.t;
    var s1 : BArray8192.t;
    var s1p : BArray8192.t;
    var s2 : BArray8192.t;
    var s2p : BArray8192.t;
    var y1 : BArray8192.t;
    var y1p : BArray8192.t;
    var y2 : BArray8192.t;
    var y2p : BArray8192.t;
    var z1 : BArray8192.t;
    var z1p : BArray8192.t;
    var z2 : BArray8192.t;
    var z2p : BArray8192.t;
    var z1tmp : BArray8192.t;
    var z1tmpp : BArray8192.t;
    var z2tmp : BArray8192.t;
    var z2tmpp : BArray8192.t;
    var z1rnd : BArray8192.t;
    var z1rndp : BArray8192.t;
    var z2rnd : BArray8192.t;
    var z2rndp : BArray8192.t;
    var highbits : BArray8192.t;
    var highp : BArray8192.t;
    var ay : BArray8192.t;
    var ayp : BArray8192.t;
    var h : BArray8192.t;
    var hp : BArray8192.t;
    var c : BArray1024.t;
    var cp : BArray1024.t;
    var z10 : BArray1024.t;
    var z10p : BArray1024.t;
    var s1polys : W64.t;
    var s2polys : W64.t;
    var lcount : W64.t;
    var kcount : W64.t;
    var b1bound : W64.t;
    var b0bound : W64.t;
    var bad : W64.t;
    var bv : W8.t;
    var reject : W64.t;
    var ms : W64.t;

    a1 <- witness;
    a1p <- witness;
    ay <- witness;
    ayp <- witness;
    b <- witness;
    bp <- witness;
    c <- witness;
    counter <- witness;
    counterp <- witness;
    cp <- witness;
    h <- witness;
    highbits <- witness;
    highp <- witness;
    hp <- witness;
    key <- witness;
    keyp <- witness;
    s1 <- witness;
    s1p <- witness;
    s2 <- witness;
    s2p <- witness;
    seedbuf <- witness;
    seedbufp <- witness;
    y1 <- witness;
    y1p <- witness;
    y2 <- witness;
    y2p <- witness;
    z1 <- witness;
    z10 <- witness;
    z10p <- witness;
    z1p <- witness;
    z1rnd <- witness;
    z1rndp <- witness;
    z1tmp <- witness;
    z1tmpp <- witness;
    z2 <- witness;
    z2p <- witness;
    z2rnd <- witness;
    z2rndp <- witness;
    z2tmp <- witness;
    z2tmpp <- witness;
    seedbufp <- seedbuf;
    keyp <- key;
    bp <- b;
    counterp <- counter;
    a1p <- a1;
    s1p <- s1;
    s2p <- s2;
    y1p <- y1;
    y2p <- y2;
    z1p <- z1;
    z2p <- z2;
    z1tmpp <- z1tmp;
    z2tmpp <- z2tmp;
    z1rndp <- z1rnd;
    z2rndp <- z2rnd;
    highp <- highbits;
    ayp <- ay;
    hp <- h;
    cp <- c;
    z10p <- z10;
    s1polys <- W64.of_int 3;
    s2polys <- W64.of_int 2;
    lcount <- W64.of_int 1024;
    kcount <- W64.of_int 512;
    b1bound <- W64.of_int 6496508945891328;
    b0bound <- W64.of_int 6505809026482176;
    (a1p, s1p, s2p, keyp) <@
      Sign._sf_unpack_sk_mode2(a1p, s1p, s2p, keyp, skp);
    seedbufp <@ Sign._sf_sign_expand_seedbuf(seedbufp, keyp, rndp, mup);
    s1p <@ Sign._polyvec_ntt(s1p, s1polys);
    s2p <@ Sign._polyvec_ntt(s2p, s2polys);
    counterp <- BArray8.set64 counterp 0 (W64.of_int 0);
    bad <- W64.of_int 1;
    while (bad <> W64.of_int 0) {
      (y1p, y2p, bp, counterp) <@
        Sign._sf_hyperball_mode2(y1p, y2p, bp, counterp, seedbufp);
      (cp, highp, ayp, z1rndp, z2rndp, z10p) <@
        Sign._sf_round_challenge_mode2(
          cp, highp, ayp, z1rndp, z2rndp, z10p,
          y1p, y2p, a1p, mup);
      observed_cp <- cp;
      bv <- BArray1.get8 bp 0;
      (z1p, z2p, z1tmpp, z2tmpp, reject) <@
        Sign._sf_z_check(
          z1p, z2p, z1tmpp, z2tmpp, y1p, y2p, cp,
          s1p, s2p, bv, lcount, kcount, b1bound, b0bound);
      ms <- init_msf;
      reject <- protect_64 reject ms;
      bad <- W64.of_int 1;
      if (reject = W64.of_int 0) {
        (hp, z1rndp, z2rndp) <@
          Sign._sf_hint_mode2(hp, z1rndp, z2rndp, highp,
                              ayp, z1p, z2p);
        (sigp, bad) <@ Sign._sf_pack_mode2(sigp, cp, z1rndp, hp);
      }
      ms <- init_msf;
      bad <- protect_64 bad ms;
    }
    return sigp;
  }
}.

module SignInternalMuCpTrace = {
  var observed_sk : BArray2752.t
  var observed_vkbytes : W64.t
  var observed_preaddr : W64.t
  var observed_prelen : W64.t
  var observed_maddr : W64.t
  var observed_mlen : W64.t
  var observed_mu : BArray64.t
  var observed_cp : BArray1024.t

  proc run(sigp : BArray2948.t, skp : BArray2752.t,
           rndp : BArray32.t, descp : BArray32.t) : BArray2948.t = {
    var ms : W64.t;
    var mu : BArray64.t;
    var mup : BArray64.t;
    var vkbytes : W64.t;
    var preaddr : W64.t;
    var prelen : W64.t;
    var maddr : W64.t;
    var mlen : W64.t;

    mu <- witness;
    mup <- witness;
    ms <- init_msf;
    descp <- protect_ptr descp ms;
    mup <- mu;
    vkbytes <- W64.of_int 992;
    preaddr <- BArray32.get64 descp 0;
    prelen <- BArray32.get64 descp 1;
    maddr <- BArray32.get64 descp 2;
    mlen <- BArray32.get64 descp 3;
    observed_sk <- skp;
    observed_vkbytes <- vkbytes;
    observed_preaddr <- preaddr;
    observed_prelen <- prelen;
    observed_maddr <- maddr;
    observed_mlen <- mlen;
    mup <@ Sign._sf_mu_rawpre(
      mup, skp, vkbytes, preaddr, prelen, maddr, mlen);
    observed_mu <- mup;
    sigp <@ SignCoreCpTrace.run(sigp, skp, rndp, mup);
    observed_cp <- SignCoreCpTrace.observed_cp;
    return sigp;
  }
}.

module SignRawApiMuCpTrace = {
  var observed_sk : BArray2752.t
  var observed_vkbytes : W64.t
  var observed_preaddr : W64.t
  var observed_prelen : W64.t
  var observed_maddr : W64.t
  var observed_mlen : W64.t
  var observed_mu : BArray64.t
  var observed_cp : BArray1024.t

  proc run(sigu : int, siglenu : int, mu : int, mlen : int,
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
    observed_vkbytes <- W64.of_int 992;
    observed_preaddr <- W64.of_int preu;
    observed_prelen <- W64.of_int prelen;
    observed_maddr <- W64.of_int mu;
    observed_mlen <- W64.of_int mlen;
    sigp <@ SignInternalMuCpTrace.run(sigp, skp, rndp, descp);
    observed_sk <- skp;
    observed_mu <- SignInternalMuCpTrace.observed_mu;
    observed_cp <- SignInternalMuCpTrace.observed_cp;
    sigu <@ Sign._api_copy_2948_to_raw(sigu, sigp, 1474);
    Glob.mem <- storeW64 Glob.mem siglenu (W64.of_int 1474);
    r <- W64.of_int 0;
    return r;
  }
}.

lemma sign_signature_core_exact_cp_trace :
  equiv [Sign._sf_signature_core_mode2 ~ SignCoreCpTrace.run :
    ={Glob.mem, sigp, skp, rndp, mup}
    ==>
    ={Glob.mem, res}].
proof. by proc; sim. qed.

lemma sign_internal_exact_mu_cp_trace :
  equiv [Sign.crypto_sign_signature_internal_mode2_jazz ~
         SignInternalMuCpTrace.run :
    ={Glob.mem, sigp, skp, rndp, descp}
    ==>
    ={Glob.mem, res}].
proof.
by proc; sim.
qed.

lemma sign_raw_api_exact_mu_cp_trace :
  equiv [Sign.cryptolab_haetae_mode2_signature_internal ~
         SignRawApiMuCpTrace.run :
    ={Glob.mem, sigu, siglenu, mu, mlen, preu, prelen, rndu, sku}
    ==>
    ={Glob.mem, res}].
proof.
by proc; sim.
qed.

lemma sign_signature_core_trace_observed_cp_valid :
  hoare [SignCoreCpTrace.run :
    true
    ==>
    valid_mode2_carrier_challenge
      (challenge_of_barray SignCoreCpTrace.observed_cp)].
proof.
proc.
while
  (bad <> W64.zero \/
   valid_mode2_carrier_challenge
     (challenge_of_barray SignCoreCpTrace.observed_cp)).
+ seq 8 :
    (valid_mode2_carrier_challenge
      (challenge_of_barray SignCoreCpTrace.observed_cp)).
  + wp.
    call (_ : true ==> true); first by auto.
    wp.
    call sign_round_challenge_mode2_valid_carrier.
    call (_ : true ==> true); first by auto.
    auto.
  + conseq (_ :
      valid_mode2_carrier_challenge
        (challenge_of_barray SignCoreCpTrace.observed_cp)
      ==>
      valid_mode2_carrier_challenge
        (challenge_of_barray SignCoreCpTrace.observed_cp)).
    + auto.
    + auto.
    + auto.
    + move=> &hr hvalid bad0 _.
      right.
      exact hvalid.
    if.
    * wp.
      call (_ : true ==> true); first by auto.
      call (_ : true ==> true); first by auto.
      auto.
    * auto.
+ wp.
  call (_ : true ==> true); first by auto.
  call (_ : true ==> true); first by auto.
  call (_ : true ==> true); first by auto.
  call (_ : true ==> true); first by auto.
  auto => />.
  rewrite /protect_64.
  smt().
qed.

lemma sign_internal_trace_observed_cp_valid :
  hoare [SignInternalMuCpTrace.run :
    true
    ==>
    valid_mode2_carrier_challenge
      (challenge_of_barray SignInternalMuCpTrace.observed_cp)].
proof.
proc.
wp.
call sign_signature_core_trace_observed_cp_valid.
wp.
call (_ : true ==> true); first by auto.
auto.
qed.

lemma sign_raw_api_trace_observed_cp_valid :
  hoare [SignRawApiMuCpTrace.run :
    true
    ==>
    valid_mode2_carrier_challenge
      (challenge_of_barray SignRawApiMuCpTrace.observed_cp)].
proof.
proc.
wp.
call (_ : true ==> true); first by auto.
wp.
call sign_internal_trace_observed_cp_valid.
wp.
call (_ : true ==> true); first by auto.
call (_ : true ==> true); first by auto.
auto.
qed.

lemma sign_internal_cp_trace_concrete_honest_site_no_failure
    (sk : HAETAE_Algebra.skey) (m : HAETAE_Algebra.message)
    (ctx : HAETAE_Algebra.context)
    (coins : HAETAE_Algebra.random_coins) :
  hoare [SignInternalMuCpTrace.run :
    true
    ==>
    ! Mode2ChallengeROMProgrammingPostFreeze.mode2_fs_with_aborts_failure
        (Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2
          sk m ctx coins SignInternalMuCpTrace.observed_cp)
        (Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_programming_site_mode2
          sk m ctx coins SignInternalMuCpTrace.observed_cp)].
proof.
conseq sign_internal_trace_observed_cp_valid.
move=> &hr _ hvalid.
apply
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2_actual_site_no_failure.
qed.

lemma sign_raw_api_cp_trace_concrete_honest_site_no_failure
    (sk : HAETAE_Algebra.skey) (m : HAETAE_Algebra.message)
    (ctx : HAETAE_Algebra.context)
    (coins : HAETAE_Algebra.random_coins) :
  hoare [SignRawApiMuCpTrace.run :
    true
    ==>
    ! Mode2ChallengeROMProgrammingPostFreeze.mode2_fs_with_aborts_failure
        (Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2
          sk m ctx coins SignRawApiMuCpTrace.observed_cp)
        (Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_programming_site_mode2
          sk m ctx coins SignRawApiMuCpTrace.observed_cp)].
proof.
conseq sign_raw_api_trace_observed_cp_valid.
move=> &hr _ hvalid.
apply
  Mode2ConcreteHonestSigningTranscriptPostFreeze.concrete_honest_transcript_mode2_actual_site_no_failure.
qed.

lemma sign_raw_api_trace_concrete_honest_site_clear
    (sk : HAETAE_Algebra.skey) (m : HAETAE_Algebra.message)
    (ctx : HAETAE_Algebra.context)
    (coins : HAETAE_Algebra.random_coins) :
  hoare [SignRawApiMuCpTrace.run :
    true
    ==>
    concrete_honest_site_clear
      sk m ctx coins SignRawApiMuCpTrace.observed_cp].
proof.
conseq
  sign_raw_api_trace_observed_cp_valid
  (sign_raw_api_cp_trace_concrete_honest_site_no_failure
    sk m ctx coins).
qed.

(* Hiding the trace ghost yields an existence statement only.  It does not
   make cp an observable return value of the uninstrumented raw ABI. *)
lemma sign_raw_api_concrete_honest_site_clear_witness
    (sk : HAETAE_Algebra.skey) (m : HAETAE_Algebra.message)
    (ctx : HAETAE_Algebra.context)
    (coins : HAETAE_Algebra.random_coins) :
  hoare [Sign.cryptolab_haetae_mode2_signature_internal :
    true
    ==>
    exists cp,
      concrete_honest_site_clear sk m ctx coins cp].
proof.
conseq
  sign_raw_api_exact_mu_cp_trace
  (sign_raw_api_trace_concrete_honest_site_clear sk m ctx coins).
+ move=> &1 _.
  exists Glob.mem{1}.
  exists
    (sigu{1}, siglenu{1}, mu{1}, mlen{1},
     preu{1}, prelen{1}, rndu{1}, sku{1}).
  by auto.
+ move=> &1 &2 [_ _] hclear.
  exists SignRawApiMuCpTrace.observed_cp{2}.
  exact hclear.
qed.

end SignCoreChallengeTracePostFreeze.
