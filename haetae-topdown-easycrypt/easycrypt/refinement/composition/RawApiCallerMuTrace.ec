require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import RawSignApiTarget ApiKeyMemoryBridge.

theory RawApiCallerMuTrace.

module Sign = RawSignApiTarget.M.

op mode2_vkbytes : int = ApiKeyMemoryBridge.mode2_vkbytes.
op mode2_skbytes : int = ApiKeyMemoryBridge.mode2_skbytes.

(* This mirror preserves the complete signing continuation.  Its only change
   is to return the mu value produced by the actual generated hash call. *)
module SignInternalMuTrace = {
  var observed_sk : BArray2752.t
  var observed_vkbytes : W64.t
  var observed_preaddr : W64.t
  var observed_prelen : W64.t
  var observed_maddr : W64.t
  var observed_mlen : W64.t
  var observed_mu : BArray64.t

  proc run (sigp : BArray2948.t, skp : BArray2752.t,
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
    mup <@ Sign._sf_mu_rawpre
      (mup, skp, vkbytes, preaddr, prelen, maddr, mlen);
    observed_mu <- mup;
    sigp <@ Sign._sf_signature_core_mode2 (sigp, skp, rndp, mup);
    return sigp;
  }
}.

(* The raw ABI mirror performs every import, hash/core call and output write
   of the generated caller.  It additionally returns the imported SK and mu
   so that a later composition theorem can name the real intermediate data. *)
module SignRawApiMuTrace = {
  var observed_sk : BArray2752.t
  var observed_vkbytes : W64.t
  var observed_preaddr : W64.t
  var observed_prelen : W64.t
  var observed_maddr : W64.t
  var observed_mlen : W64.t
  var observed_mu : BArray64.t

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
    skp <@ Sign._api_copy_raw_to_2752_prefix (skp, sku, 1408);
    rndp <@ Sign._api_copy_raw_to_32 (rndp, rndu);
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
    sigp <@ SignInternalMuTrace.run (sigp, skp, rndp, descp);
    observed_sk <- skp;
    observed_mu <- SignInternalMuTrace.observed_mu;
    sigu <@ Sign._api_copy_2948_to_raw (sigu, sigp, 1474);
    Glob.mem <- storeW64 Glob.mem siglenu (W64.of_int 1474);
    r <- W64.of_int 0;
    return r;
  }
}.

lemma sign_internal_exact_mu_trace :
  equiv [Sign.crypto_sign_signature_internal_mode2_jazz ~
         SignInternalMuTrace.run :
    ={Glob.mem, sigp, skp, rndp, descp}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma sign_raw_api_exact_mu_trace :
  equiv [Sign.cryptolab_haetae_mode2_signature_internal ~
         SignRawApiMuTrace.run :
    ={Glob.mem, sigu, siglenu, mu, mlen, preu, prelen, rndu, sku}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma sign_raw_import_mode2_sk_prefix
    (src0 : int) (mem0 : global_mem_t) :
  hoare [Sign._api_copy_raw_to_2752_prefix :
    Glob.mem = mem0 /\ srcp = src0 /\ len = mode2_skbytes /\
    ApiKeyMemoryBridge.valid_region_int src0 mode2_skbytes
    ==>
    Glob.mem = mem0 /\
    ApiKeyMemoryBridge.imported_prefix res mem0 src0 mode2_vkbytes].
proof.
proc.
while (len = mode2_skbytes /\ Glob.mem = mem0 /\ srcp = src0 /\
       ApiKeyMemoryBridge.valid_region_int src0 mode2_skbytes /\
       mode2_skbytes <= i <= 2752 /\
       ApiKeyMemoryBridge.imported_prefix
         dstp mem0 src0 mode2_vkbytes).
+ auto => /> &hr hbase hlen hsum hi_ge hi_le hpref hguard.
  split; first smt().
  rewrite /ApiKeyMemoryBridge.imported_prefix => j hj.
  rewrite BArray2752.get_set_if.
  have hiword : W64.to_uint (W64.of_int i{hr}) = i{hr} by
    rewrite W64.of_uintK /=; smt().
  rewrite hiword.
  have hjlt : j < 992 by
    move: hj; rewrite /mode2_vkbytes /ApiKeyMemoryBridge.mode2_vkbytes; smt().
  have hige : 1408 <= i{hr} by
    move: hi_ge; rewrite /mode2_skbytes /ApiKeyMemoryBridge.mode2_skbytes; smt().
  rewrite ifF 1:/#.
  exact (hpref j hj).
while (len = mode2_skbytes /\ Glob.mem = mem0 /\ srcp = src0 /\
       ApiKeyMemoryBridge.valid_region_int src0 mode2_skbytes /\
       0 <= i <= mode2_skbytes /\
       forall j, 0 <= j < i =>
         BArray2752.get8 dstp j = loadW8 mem0 (src0 + j)).
+ auto => /> &hr hbase hlen hsum hi_ge hi_le hpref hguard.
  split; first smt().
  move=> j hj0 hjlt.
  have hiword : W64.to_uint (W64.of_int i{hr}) = i{hr} by
    rewrite W64.of_uintK /=;
    rewrite /mode2_skbytes /ApiKeyMemoryBridge.mode2_skbytes in hguard;
    smt().
  rewrite BArray2752.get_set_if hiword.
  case: (j = i{hr}) => [-> | hne].
  + rewrite ifT 1:/#.
    trivial.
  + rewrite ifF 1:/#.
    apply hpref; smt().
auto => />.
move=> &hr hbase hlen hsum.
split; first smt().
move=> dst i hdone hi0 hile hpref.
split.
+ split;
  rewrite /mode2_skbytes /ApiKeyMemoryBridge.mode2_skbytes;
  smt().
+ rewrite /ApiKeyMemoryBridge.imported_prefix => j hj.
  apply hpref.
  move: hdone hile hj.
  rewrite /mode2_vkbytes /mode2_skbytes
          /ApiKeyMemoryBridge.mode2_vkbytes
          /ApiKeyMemoryBridge.mode2_skbytes.
  smt().
qed.

lemma sign_internal_trace_binds_mode2_inputs
    (sk0 : BArray2752.t)
    (preaddr0 prelen0 maddr0 mlen0 : W64.t) :
  hoare [SignInternalMuTrace.run :
    skp = sk0 /\
    BArray32.get64 descp 0 = preaddr0 /\
    BArray32.get64 descp 1 = prelen0 /\
    BArray32.get64 descp 2 = maddr0 /\
    BArray32.get64 descp 3 = mlen0
    ==>
    SignInternalMuTrace.observed_sk = sk0 /\
    SignInternalMuTrace.observed_vkbytes = W64.of_int mode2_vkbytes /\
    SignInternalMuTrace.observed_preaddr = preaddr0 /\
    SignInternalMuTrace.observed_prelen = prelen0 /\
    SignInternalMuTrace.observed_maddr = maddr0 /\
    SignInternalMuTrace.observed_mlen = mlen0].
proof.
proc.
wp.
call (_ : true); first by auto.
wp.
call (_ : true); first by auto.
auto => />.
qed.

lemma sign_raw_api_trace_imports_mode2_sk
    (sku0 : int) (mem0 : global_mem_t) :
  hoare [SignRawApiMuTrace.run :
    Glob.mem = mem0 /\ sku = sku0 /\
    ApiKeyMemoryBridge.valid_region_int sku0 mode2_skbytes
    ==>
    res = W64.zero /\
    ApiKeyMemoryBridge.imported_prefix
      SignRawApiMuTrace.observed_sk mem0 sku0 mode2_vkbytes].
proof.
proc.
wp.
call (_ : true); first by auto.
wp.
call (_ : true); first by auto.
wp.
call (_ : true); first by auto.
call (sign_raw_import_mode2_sk_prefix sku0 mem0).
auto => />.
qed.

lemma sign_raw_api_trace_binds_hash_inputs
    (preu0 prelen0 mu0 mlen0 : int) :
  hoare [SignRawApiMuTrace.run :
    preu = preu0 /\ prelen = prelen0 /\ mu = mu0 /\ mlen = mlen0
    ==>
    SignRawApiMuTrace.observed_vkbytes = W64.of_int mode2_vkbytes /\
    SignRawApiMuTrace.observed_preaddr = W64.of_int preu0 /\
    SignRawApiMuTrace.observed_prelen = W64.of_int prelen0 /\
    SignRawApiMuTrace.observed_maddr = W64.of_int mu0 /\
    SignRawApiMuTrace.observed_mlen = W64.of_int mlen0].
proof.
proc.
wp.
call (_ : true); first by auto.
wp.
call (_ : true); first by auto.
wp.
call (_ : true); first by auto.
call (_ : true); first by auto.
auto => />.
qed.

end RawApiCallerMuTrace.
