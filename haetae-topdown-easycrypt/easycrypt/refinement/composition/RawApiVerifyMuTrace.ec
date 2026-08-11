require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import RawVerifyApiTarget ApiKeyMemoryBridge ExactMuTopControl.

theory RawApiVerifyMuTrace.

module Verify = RawVerifyApiTarget.M.

op mode2_sigbytes : int = 1474.
op mode2_vkbytes : int = ApiKeyMemoryBridge.mode2_vkbytes.

op mode2_verify_desc
    (descp : BArray40.t) (vku : int)
    (prep prelen mp mlen : W64.t) : bool =
  BArray40.get64 descp 0 = W64.of_int vku /\
  BArray40.get64 descp 1 = prep /\
  BArray40.get64 descp 2 = prelen /\
  BArray40.get64 descp 3 = mp /\
  BArray40.get64 descp 4 = mlen.

(* This mirror preserves the full tail computation. Its only extra effect is to
   expose the mu value returned by the real generated __verify_hash_mu call. *)
module VerifyTailMuTrace = {
  var observed_vkp : W64.t
  var observed_prep : W64.t
  var observed_prelen : W64.t
  var observed_mp : W64.t
  var observed_mlen : W64.t
  var observed_vklen : W64.t
  var observed_mu : BArray32.t

  proc run (wp_0 : BArray8192.t, wprimep : BArray1024.t,
            cp : BArray1024.t, descp : BArray40.t, k_i : int,
            highbits_len_i : int, vklen_i : int, tau_i : int) : W64.t = {
    var reject : W64.t;
    var ms : W64.t;
    var highbuf : BArray1152.t;
    var highp : BArray1152.t;
    var lsb : BArray32.t;
    var lsbp : BArray32.t;
    var mu : BArray32.t;
    var mup : BArray32.t;
    var cprime : BArray1024.t;
    var cprimep : BArray1024.t;
    var vkp : W64.t;
    var prep : W64.t;
    var prelen : W64.t;
    var mp : W64.t;
    var mlen : W64.t;
    var highlen : W64.t;
    var count : W64.t;
    var vklen : W64.t;
    var tau : W64.t;

    cprime <- witness;
    cprimep <- witness;
    highbuf <- witness;
    highp <- witness;
    lsb <- witness;
    lsbp <- witness;
    mu <- witness;
    mup <- witness;
    observed_vkp <- witness;
    observed_prep <- witness;
    observed_prelen <- witness;
    observed_mp <- witness;
    observed_mlen <- witness;
    observed_vklen <- witness;
    observed_mu <- witness;
    ms <- init_msf;
    descp <- protect_ptr descp ms;
    highp <- highbuf;
    lsbp <- lsb;
    mup <- mu;
    cprimep <- cprime;
    vkp <- BArray40.get64 descp 0;
    prep <- BArray40.get64 descp 1;
    prelen <- BArray40.get64 descp 2;
    mp <- BArray40.get64 descp 3;
    mlen <- BArray40.get64 descp 4;
    highlen <- W64.of_int highbits_len_i;
    ms <- init_msf;
    highp <- protect_ptr highp ms;
    highlen <- protect_64 highlen ms;
    highp <@ Verify.__verify_zero_highbuf (highp, highlen);
    count <- W64.of_int k_i;
    ms <- init_msf;
    highp <- protect_ptr highp ms;
    wp_0 <- protect_ptr wp_0 ms;
    count <- protect_64 count ms;
    highp <@ Verify._pack_vec_highbits_m23 (highp, wp_0, count);
    ms <- init_msf;
    lsbp <- protect_ptr lsbp ms;
    wprimep <- protect_ptr wprimep ms;
    lsbp <@ Verify._pack_poly_lsb (lsbp, wprimep);
    vklen <- W64.of_int vklen_i;
    observed_vkp <- vkp;
    observed_prep <- prep;
    observed_prelen <- prelen;
    observed_mp <- mp;
    observed_mlen <- mlen;
    observed_vklen <- vklen;
    ms <- init_msf;
    mup <- protect_ptr mup ms;
    mup <@ Verify.__verify_hash_mu (mup, vkp, prep, prelen, mp, mlen, vklen);
    observed_mu <- mup;
    tau <- W64.of_int tau_i;
    ms <- init_msf;
    cprimep <- protect_ptr cprimep ms;
    highp <- protect_ptr highp ms;
    lsbp <- protect_ptr lsbp ms;
    mup <- protect_ptr mup ms;
    highlen <- protect_64 highlen ms;
    tau <- protect_64 tau ms;
    cprimep <@ Verify.__verify_challenge_m23
      (cprimep, highp, highlen, lsbp, mup, tau);
    ms <- init_msf;
    cp <- protect_ptr cp ms;
    cprimep <- protect_ptr cprimep ms;
    reject <@ Verify._poly_mismatch (cp, cprimep);
    return reject;
  }
}.

module VerifyFullM23MuTrace = {
  var observed_vk : BArray2752.t
  var observed_vkp : W64.t
  var observed_prep : W64.t
  var observed_prelen : W64.t
  var observed_mp : W64.t
  var observed_mlen : W64.t
  var observed_vklen : W64.t
  var observed_mu : BArray32.t
  var tail_reached : bool

  proc run (sigp : BArray2948.t, siglen : W64.t, vkp : BArray2752.t,
            vku : int, descp : BArray40.t, k_i : int, l_i : int,
            m_i : int, sigbytes_i : int, vkbytes_i : int,
            highbits_len_i : int, tau_i : int, b2sq_i : int,
            hb_count_i : int, hb_m_i : int, hb_offset_i : int,
            h_count_i : int, h_m_i : int, h_offset_i : int,
            base_hb_i : int, base_h_i : int, payload_limit_i : int) : W64.t = {
    var reject : W64.t;
    var k : W64.t;
    var l : W64.t;
    var m : W64.t;
    var desc : BArray40.t;
    var copydescp : BArray40.t;
    var a1 : BArray32768.t;
    var a1p : BArray32768.t;
    var h_symbolwp : BArray2048.t;
    var h_dsymswp : BArray528.t;
    var hb_symbolwp : BArray2048.t;
    var hb_dsymswp : BArray528.t;
    var c : BArray1024.t;
    var cp : BArray1024.t;
    var lowz : BArray8192.t;
    var lowzp : BArray8192.t;
    var highz : BArray8192.t;
    var highzp : BArray8192.t;
    var h : BArray8192.t;
    var hp : BArray8192.t;
    var bad : BArray8.t;
    var badp : BArray8.t;
    var ms : W64.t;
    var badv : W64.t;
    var z1 : BArray8192.t;
    var z1p : BArray8192.t;
    var wprime : BArray1024.t;
    var wprimep : BArray1024.t;
    var lcount : W64.t;
    var sqnorm2 : W64.t;
    var highbits : BArray8192.t;
    var highbitsp : BArray8192.t;
    var w : BArray8192.t;
    var wp_0 : BArray8192.t;
    var z2 : BArray8192.t;
    var z2p : BArray8192.t;
    var kcount : W64.t;
    var bound : W64.t;
    var taildescp : BArray40.t;

    a1 <- witness;
    a1p <- witness;
    bad <- witness;
    badp <- witness;
    c <- witness;
    copydescp <- witness;
    cp <- witness;
    desc <- witness;
    h <- witness;
    h_dsymswp <- witness;
    h_symbolwp <- witness;
    hb_dsymswp <- witness;
    hb_symbolwp <- witness;
    highbits <- witness;
    highbitsp <- witness;
    highz <- witness;
    highzp <- witness;
    hp <- witness;
    lowz <- witness;
    lowzp <- witness;
    taildescp <- witness;
    w <- witness;
    wp_0 <- witness;
    wprime <- witness;
    wprimep <- witness;
    z1 <- witness;
    z1p <- witness;
    z2 <- witness;
    z2p <- witness;
    observed_vk <- witness;
    observed_vkp <- witness;
    observed_prep <- witness;
    observed_prelen <- witness;
    observed_mp <- witness;
    observed_mlen <- witness;
    observed_vklen <- witness;
    observed_mu <- witness;
    tail_reached <- false;
    if (siglen <> W64.of_int sigbytes_i) {
      reject <- W64.of_int 1;
    } else {
      k <- W64.of_int k_i;
      l <- W64.of_int l_i;
      m <- W64.of_int m_i;
      copydescp <- desc;
      copydescp <- BArray40.set64 copydescp 0 (BArray40.get64 descp 0);
      copydescp <- BArray40.set64 copydescp 1 (BArray40.get64 descp 1);
      copydescp <- BArray40.set64 copydescp 2 (BArray40.get64 descp 2);
      copydescp <- BArray40.set64 copydescp 3 (BArray40.get64 descp 3);
      copydescp <- BArray40.set64 copydescp 4 (BArray40.get64 descp 4);
      a1p <- a1;
      a1p <@ Verify._unpack_vk_m23_full (a1p, vkp, vku, k, l, m);
      observed_vk <- vkp;
      h_symbolwp <- jmode2_h_symbol_words;
      h_dsymswp <- jmode2_h_dsyms_words;
      hb_symbolwp <- jmode2_hb_z1_symbol_words;
      hb_dsymswp <- jmode2_hb_z1_dsyms_words;
      if (k_i = 3) {
        h_symbolwp <- jmode3_h_symbol_words;
        h_dsymswp <- jmode3_h_dsyms_words;
        hb_symbolwp <- jmode3_hb_z1_symbol_words;
        hb_dsymswp <- jmode3_hb_z1_dsyms_words;
      } else {
      }
      cp <- c;
      lowzp <- lowz;
      highzp <- highz;
      hp <- h;
      badp <- bad;
      ms <- init_msf;
      badp <- protect_ptr badp ms;
      badp <- BArray8.set64 badp 0 (W64.of_int 0);
      ms <- init_msf;
      cp <- protect_ptr cp ms;
      lowzp <- protect_ptr lowzp ms;
      highzp <- protect_ptr highzp ms;
      hp <- protect_ptr hp ms;
      badp <- protect_ptr badp ms;
      sigp <- protect_ptr sigp ms;
      (cp, lowzp, highzp, hp, badp) <@
        Verify._unpack_sig_full
          (cp, lowzp, highzp, hp, badp, sigp,
           h_symbolwp, h_dsymswp, hb_symbolwp, hb_dsymswp,
           l_i, hb_count_i, hb_m_i, hb_offset_i,
           h_count_i, h_m_i, h_offset_i,
           base_hb_i, base_h_i, payload_limit_i);
      ms <- init_msf;
      badp <- protect_ptr badp ms;
      badv <- BArray8.get64 badp 0;
      ms <- init_msf;
      badv <- protect_64 badv ms;
      if (badv <> W64.of_int 0) {
        reject <- W64.of_int 1;
      } else {
        z1p <- z1;
        wprimep <- wprime;
        lcount <- l;
        lcount <- lcount * W64.of_int 256;
        ms <- init_msf;
        z1p <- protect_ptr z1p ms;
        wprimep <- protect_ptr wprimep ms;
        highzp <- protect_ptr highzp ms;
        lowzp <- protect_ptr lowzp ms;
        cp <- protect_ptr cp ms;
        lcount <- protect_64 lcount ms;
        (z1p, wprimep, sqnorm2) <@
          Verify._verify_prepare_z1_wprime
            (z1p, wprimep, highzp, lowzp, cp, lcount);
        highbitsp <- highbits;
        ms <- init_msf;
        z1p <- protect_ptr z1p ms;
        highbitsp <- protect_ptr highbitsp ms;
        a1p <- protect_ptr a1p ms;
        wprimep <- protect_ptr wprimep ms;
        k <- protect_64 k ms;
        l <- protect_64 l ms;
        (z1p, highbitsp) <@
          Verify._verify_matrix_crt (z1p, highbitsp, a1p, wprimep, k, l);
        wp_0 <- w;
        z2p <- z2;
        kcount <- k;
        kcount <- kcount * W64.of_int 256;
        ms <- init_msf;
        wp_0 <- protect_ptr wp_0 ms;
        z2p <- protect_ptr z2p ms;
        z1p <- protect_ptr z1p ms;
        hp <- protect_ptr hp ms;
        wprimep <- protect_ptr wprimep ms;
        kcount <- protect_64 kcount ms;
        (wp_0, z2p) <@
          Verify._sign_verify_recover_w_z2
            (wp_0, z2p, z1p, hp, wprimep, kcount, 256, 9, 252, 512);
        bound <- W64.of_int b2sq_i;
        ms <- init_msf;
        z2p <- protect_ptr z2p ms;
        sqnorm2 <- protect_64 sqnorm2 ms;
        kcount <- protect_64 kcount ms;
        bound <- protect_64 bound ms;
        reject <@ Verify._sign_verify_norm_reject
          (z2p, sqnorm2, kcount, bound);
        ms <- init_msf;
        reject <- protect_64 reject ms;
        if (reject = W64.of_int 0) {
          tail_reached <- true;
          taildescp <- copydescp;
          ms <- init_msf;
          wp_0 <- protect_ptr wp_0 ms;
          wprimep <- protect_ptr wprimep ms;
          cp <- protect_ptr cp ms;
          taildescp <- protect_ptr taildescp ms;
          reject <@ VerifyTailMuTrace.run
            (wp_0, wprimep, cp, taildescp, k_i, highbits_len_i, vkbytes_i,
             tau_i);
          observed_vkp <- VerifyTailMuTrace.observed_vkp;
          observed_prep <- VerifyTailMuTrace.observed_prep;
          observed_prelen <- VerifyTailMuTrace.observed_prelen;
          observed_mp <- VerifyTailMuTrace.observed_mp;
          observed_mlen <- VerifyTailMuTrace.observed_mlen;
          observed_vklen <- VerifyTailMuTrace.observed_vklen;
          observed_mu <- VerifyTailMuTrace.observed_mu;
        } else {
        }
      }
    }
    return reject;
  }
}.

module VerifyFullMode2MuTrace = {
  var observed_vk : BArray2752.t
  var observed_vkp : W64.t
  var observed_prep : W64.t
  var observed_prelen : W64.t
  var observed_mp : W64.t
  var observed_mlen : W64.t
  var observed_vklen : W64.t
  var observed_mu : BArray32.t
  var tail_reached : bool

  proc run (sigp : BArray2948.t, siglen : W64.t, vkp : BArray2752.t,
            vku : int, descp : BArray40.t) : W64.t = {
    var reject : W64.t;

    observed_vk <- witness;
    observed_vkp <- witness;
    observed_prep <- witness;
    observed_prelen <- witness;
    observed_mp <- witness;
    observed_mlen <- witness;
    observed_vklen <- witness;
    observed_mu <- witness;
    tail_reached <- false;
    reject <@ VerifyFullM23MuTrace.run
      (sigp, siglen, vkp, vku, descp, 2, 4, 3, 1474, 992, 576, 58,
       163265017, 1024, 13, 6, 512, 13, 239, 132, 7, 416);
    observed_vk <- VerifyFullM23MuTrace.observed_vk;
    observed_vkp <- VerifyFullM23MuTrace.observed_vkp;
    observed_prep <- VerifyFullM23MuTrace.observed_prep;
    observed_prelen <- VerifyFullM23MuTrace.observed_prelen;
    observed_mp <- VerifyFullM23MuTrace.observed_mp;
    observed_mlen <- VerifyFullM23MuTrace.observed_mlen;
    observed_vklen <- VerifyFullM23MuTrace.observed_vklen;
    observed_mu <- VerifyFullM23MuTrace.observed_mu;
    tail_reached <- VerifyFullM23MuTrace.tail_reached;
    return reject;
  }
}.

module VerifyInternalMode2MuTrace = {
  var observed_vk : BArray2752.t
  var observed_vkp : W64.t
  var observed_prep : W64.t
  var observed_prelen : W64.t
  var observed_mp : W64.t
  var observed_mlen : W64.t
  var observed_vklen : W64.t
  var observed_mu : BArray32.t
  var tail_reached : bool

  proc run (sigp : BArray2948.t, siglen : W64.t, vkp : BArray2752.t,
            vku : int, descp : BArray40.t) : W64.t = {
    var reject : W64.t;
    var ms : W64.t;

    observed_vk <- witness;
    observed_vkp <- witness;
    observed_prep <- witness;
    observed_prelen <- witness;
    observed_mp <- witness;
    observed_mlen <- witness;
    observed_vklen <- witness;
    observed_mu <- witness;
    tail_reached <- false;
    ms <- init_msf;
    siglen <- protect_64 siglen ms;
    reject <@ VerifyFullMode2MuTrace.run (sigp, siglen, vkp, vku, descp);
    observed_vk <- VerifyFullMode2MuTrace.observed_vk;
    observed_vkp <- VerifyFullMode2MuTrace.observed_vkp;
    observed_prep <- VerifyFullMode2MuTrace.observed_prep;
    observed_prelen <- VerifyFullMode2MuTrace.observed_prelen;
    observed_mp <- VerifyFullMode2MuTrace.observed_mp;
    observed_mlen <- VerifyFullMode2MuTrace.observed_mlen;
    observed_vklen <- VerifyFullMode2MuTrace.observed_vklen;
    observed_mu <- VerifyFullMode2MuTrace.observed_mu;
    tail_reached <- VerifyFullMode2MuTrace.tail_reached;
    return reject;
  }
}.

module VerifyRawApiMuTrace = {
  var observed_vk : BArray2752.t
  var observed_vkp : W64.t
  var observed_prep : W64.t
  var observed_prelen : W64.t
  var observed_mp : W64.t
  var observed_mlen : W64.t
  var observed_vklen : W64.t
  var observed_mu : BArray32.t
  var tail_reached : bool

  proc run (sigu : int, siglen : W64.t, mu : W64.t, mlen : W64.t,
            preu : W64.t, prelen : W64.t, vku : int) : W64.t = {
    var reject : W64.t;
    var sig : BArray2948.t;
    var sigp : BArray2948.t;
    var vk : BArray2752.t;
    var vkp : BArray2752.t;
    var desc : BArray40.t;
    var descp : BArray40.t;

    desc <- witness;
    descp <- witness;
    sig <- witness;
    sigp <- witness;
    vk <- witness;
    vkp <- witness;
    observed_vk <- witness;
    observed_vkp <- witness;
    observed_prep <- witness;
    observed_prelen <- witness;
    observed_mp <- witness;
    observed_mlen <- witness;
    observed_vklen <- witness;
    observed_mu <- witness;
    tail_reached <- false;
    if (siglen <> W64.of_int mode2_sigbytes) {
      reject <- W64.of_int 1;
    } else {
      sigp <- sig;
      vkp <- vk;
      descp <- desc;
      sigp <@ Verify._api_copy_raw_to_2948_prefix (sigp, sigu, mode2_sigbytes);
      vkp <@ Verify._api_copy_raw_to_2752_prefix (vkp, vku, mode2_vkbytes);
      observed_vk <- vkp;
      descp <- BArray40.set64 descp 0 (W64.of_int vku);
      descp <- BArray40.set64 descp 1 preu;
      descp <- BArray40.set64 descp 2 prelen;
      descp <- BArray40.set64 descp 3 mu;
      descp <- BArray40.set64 descp 4 mlen;
      reject <@ VerifyInternalMode2MuTrace.run
        (sigp, W64.of_int mode2_sigbytes, vkp, vku, descp);
      tail_reached <- VerifyInternalMode2MuTrace.tail_reached;
      observed_vkp <- VerifyInternalMode2MuTrace.observed_vkp;
      observed_prep <- VerifyInternalMode2MuTrace.observed_prep;
      observed_prelen <- VerifyInternalMode2MuTrace.observed_prelen;
      observed_mp <- VerifyInternalMode2MuTrace.observed_mp;
      observed_mlen <- VerifyInternalMode2MuTrace.observed_mlen;
      observed_vklen <- VerifyInternalMode2MuTrace.observed_vklen;
      observed_mu <- VerifyInternalMode2MuTrace.observed_mu;
    }
    return reject;
  }
}.

module VerifyCryptolabMuTrace = {
  var observed_vk : BArray2752.t
  var observed_vkp : W64.t
  var observed_prep : W64.t
  var observed_prelen : W64.t
  var observed_mp : W64.t
  var observed_mlen : W64.t
  var observed_vklen : W64.t
  var observed_mu : BArray32.t
  var tail_reached : bool

  proc run (sigu : int, siglen : int, mu : int, mlen : int,
            preu : int, prelen : int, vku : int) : W64.t = {
    var r : W64.t;
    var reject : W64.t;

    reject <@ VerifyRawApiMuTrace.run
      (sigu, W64.of_int siglen, W64.of_int mu, W64.of_int mlen,
       W64.of_int preu, W64.of_int prelen, vku);
    reject <@ Verify._verify_publish_reject (reject);
    if (reject = W64.of_int 0) {
      r <- W64.of_int 0;
    } else {
      r <@ Verify._api_reject ();
    }
    observed_vk <- VerifyRawApiMuTrace.observed_vk;
    observed_vkp <- VerifyRawApiMuTrace.observed_vkp;
    observed_prep <- VerifyRawApiMuTrace.observed_prep;
    observed_prelen <- VerifyRawApiMuTrace.observed_prelen;
    observed_mp <- VerifyRawApiMuTrace.observed_mp;
    observed_mlen <- VerifyRawApiMuTrace.observed_mlen;
    observed_vklen <- VerifyRawApiMuTrace.observed_vklen;
    observed_mu <- VerifyRawApiMuTrace.observed_mu;
    tail_reached <- VerifyRawApiMuTrace.tail_reached;
    return r;
  }
}.

lemma verify_tail_exact_mu_trace :
  equiv [Verify._sign_verify_tail_m23 ~ VerifyTailMuTrace.run :
    ={Glob.mem, wp_0, wprimep, cp, descp, k_i, highbits_len_i, vklen_i, tau_i}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma verify_full_m23_exact_mu_trace :
  equiv [Verify._verify_full_m23 ~ VerifyFullM23MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp, k_i, l_i, m_i, sigbytes_i,
      vkbytes_i, highbits_len_i, tau_i, b2sq_i, hb_count_i, hb_m_i,
      hb_offset_i, h_count_i, h_m_i, h_offset_i, base_hb_i, base_h_i,
      payload_limit_i}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma verify_full_mode2_exact_mu_trace :
  equiv [Verify._verify_full_mode2 ~ VerifyFullMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma verify_internal_mode2_exact_mu_trace :
  equiv [Verify.sign_verify_internal_mode2_jazz ~ VerifyInternalMode2MuTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res}].
proof.
proc; sim.
qed.

lemma verify_raw_api_exact_mu_trace :
  equiv [Verify._api_verify_mode2_raw ~ VerifyRawApiMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res}].
proof.
proc.
sp.
if => //.
+ sim.
+ wp.
  call verify_internal_mode2_exact_mu_trace.
  sim : (={Glob.mem, sigp, vkp, vku, descp}).
  call (_: ={Glob.mem, arg} ==> ={Glob.mem, res}).
  + proc; sim.
  + sim : (={Glob.mem, sigp, sigu, vku, preu, prelen, mu, mlen,
             descp, vkp}).
    call (_: ={Glob.mem, arg} ==> ={Glob.mem, res}).
    + proc; sim.
    + auto.
qed.

lemma verify_cryptolab_exact_mu_trace :
  equiv [Verify.cryptolab_haetae_mode2_verify_internal ~ VerifyCryptolabMuTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res}].
proof.
proc.
seq 1 1 : (={Glob.mem, reject}).
+ call verify_raw_api_exact_mu_trace.
  auto.
+ sim.
qed.

lemma verify_raw_import_reads_mode2_vk_992
    (vku0 : int) (mem0 : global_mem_t) :
  hoare [ApiKeyMemoryBridge.Verify._api_copy_raw_to_2752_prefix :
    Glob.mem = mem0 /\ srcp = vku0 /\ len = mode2_vkbytes /\
    ApiKeyMemoryBridge.valid_region_int vku0 mode2_vkbytes
    ==>
    Glob.mem = mem0 /\
    ApiKeyMemoryBridge.imported_prefix res mem0 vku0 mode2_vkbytes].
proof.
exact (ApiKeyMemoryBridge.verify_import_mode2_vk_prefix vku0 mem0).
qed.

lemma mode2_verify_desc_binding
    (vku0 : int) (preu0 prelen0 mu0 mlen0 : W64.t) :
  ExactMuTopControl.raw_prelen prelen0 =>
  mode2_verify_desc
    (BArray40.set64
       (BArray40.set64
          (BArray40.set64
             (BArray40.set64
                (BArray40.set64 witness 0 (W64.of_int vku0))
                1 preu0)
             2 prelen0)
          3 mu0)
       4 mlen0)
    vku0 preu0 prelen0 mu0 mlen0 /\
  ExactMuTopControl.raw_prelen prelen0.
proof.
move=> hraw.
split.
+ rewrite /mode2_verify_desc /=.
   smt().
+ exact hraw.
qed.

end RawApiVerifyMuTrace.
