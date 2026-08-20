require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8 BArray40 BArray528 BArray1024 BArray2048
               BArray2752 BArray2948 BArray8192 BArray32768
               RawVerifyApiTarget RawApiVerifyMuTrace
               Rq KeygenM23ArithmeticSpec KeygenM23MatrixSpec
               VerifyHbzRansSuccessCanonicalPostFreeze
               VerifyUnpackMatrixCrtRawCompositionPostFreeze
               VerifySignatureUnpackRawBoundaryPostFreeze
               VerifyPrepareZ1RawBoundaryPostFreeze
               VerifyMatrixCrtRawBoundaryPostFreeze
               VerifyRecoverNormRawBoundaryPostFreeze
               VerifySignatureUnpackPrepareMatrixCrtRecoverNormRawCompositionPostFreeze
               VerifyTailRawBoundaryPostFreeze
               VerifySignatureUnpackPrepareMatrixCrtRecoverNormTailRawCompositionPostFreeze.

import VerifySignatureUnpackPrepareMatrixCrtRecoverNormRawCompositionPostFreeze
       VerifyUnpackMatrixCrtRawCompositionPostFreeze
       VerifySignatureUnpackRawBoundaryPostFreeze
       VerifyPrepareZ1RawBoundaryPostFreeze
       VerifyMatrixCrtRawBoundaryPostFreeze
       VerifyRecoverNormRawBoundaryPostFreeze
       VerifyTailRawBoundaryPostFreeze
       VerifySignatureUnpackPrepareMatrixCrtRecoverNormTailRawCompositionPostFreeze.

theory VerifyActualFullFunctionalRawPostFreeze.

module Raw = RawVerifyApiTarget.M.
module VerifyFullMode2FunctionalTrace = {
  proc run
      (sigp : BArray2948.t, siglen : W64.t, vkp : BArray2752.t,
       vku : int, descp : BArray40.t)
      : BArray32768.t * BArray1024.t * BArray8192.t * BArray8192.t *
        BArray8192.t * BArray8.t * BArray8192.t * BArray8192.t *
        BArray1024.t * W64.t * BArray8192.t * BArray8192.t * W64.t *
        W64.t = {
    var a1 : BArray32768.t;
    var a1p : BArray32768.t;
    var bad : BArray8.t;
    var badp : BArray8.t;
    var c : BArray1024.t;
    var cp : BArray1024.t;
    var copydescp : BArray40.t;
    var desc : BArray40.t;
    var h : BArray8192.t;
    var hp : BArray8192.t;
    var highbits : BArray8192.t;
    var highbitsp : BArray8192.t;
    var highz : BArray8192.t;
    var highzp : BArray8192.t;
    var lowz : BArray8192.t;
    var lowzp : BArray8192.t;
    var norm_reject : W64.t;
    var reject : W64.t;
    var total : W64.t;
    var w : BArray8192.t;
    var wp_0 : BArray8192.t;
    var wprime : BArray1024.t;
    var wprimep : BArray1024.t;
    var z1 : BArray8192.t;
    var z1p : BArray8192.t;
    var z2 : BArray8192.t;
    var z2p : BArray8192.t;

    a1 <- witness;
    a1p <- witness;
    bad <- witness;
    badp <- witness;
    c <- witness;
    copydescp <- witness;
    cp <- witness;
    desc <- witness;
    h <- witness;
    highbits <- witness;
    highbitsp <- witness;
    highz <- witness;
    highzp <- witness;
    hp <- witness;
    lowz <- witness;
    lowzp <- witness;
    w <- witness;
    wp_0 <- witness;
    wprime <- witness;
    wprimep <- witness;
    z1 <- witness;
    z1p <- witness;
    z2 <- witness;
    z2p <- witness;
    norm_reject <- W64.one;
    reject <- W64.one;
    total <- W64.zero;

    if (siglen <> W64.of_int 1474) {
      reject <- W64.one;
    } else {
      copydescp <- desc;
      copydescp <- BArray40.set64 copydescp 0 (BArray40.get64 descp 0);
      copydescp <- BArray40.set64 copydescp 1 (BArray40.get64 descp 1);
      copydescp <- BArray40.set64 copydescp 2 (BArray40.get64 descp 2);
      copydescp <- BArray40.set64 copydescp 3 (BArray40.get64 descp 3);
      copydescp <- BArray40.set64 copydescp 4 (BArray40.get64 descp 4);
      a1p <- a1;
      cp <- c;
      lowzp <- lowz;
      highzp <- highz;
      hp <- h;
      badp <- bad;
      z1p <- z1;
      wprimep <- wprime;
      highbitsp <- highbits;
      wp_0 <- w;
      z2p <- z2;
      (a1p, cp, lowzp, highzp, hp, badp,
       z1p, highbitsp, wprimep, total,
       wp_0, z2p, norm_reject, reject) <@
        RawVerifySignatureUnpackPrepareMatrixCrtRecoverNormTailMode2.run
        (a1p, vkp, vku,
         z1p, highbitsp, lowzp, highzp, hp,
         wp_0, z2p, wprimep, cp, badp, sigp, copydescp);
    }

    return
      (a1p, cp, lowzp, highzp, hp, badp,
       z1p, highbitsp, wprimep, total,
       wp_0, z2p, norm_reject, reject);
  }
}.

module VerifyFullMode2FlatTrace = {
  proc run
      (sigp : BArray2948.t, siglen : W64.t, vkp : BArray2752.t,
       vku : int, descp : BArray40.t)
      : BArray32768.t * BArray1024.t * BArray8192.t * BArray8192.t *
        BArray8192.t * BArray8.t * BArray8192.t * BArray8192.t *
        BArray1024.t * W64.t * BArray8192.t * BArray8192.t * W64.t *
        W64.t = {
    var a1 : BArray32768.t;
    var a1p : BArray32768.t;
    var bad : BArray8.t;
    var badp : BArray8.t;
    var badv : W64.t;
    var base_h_i : int;
    var base_hb_i : int;
    var b2sq_i : int;
    var bound : W64.t;
    var c : BArray1024.t;
    var cp : BArray1024.t;
    var copydescp : BArray40.t;
    var desc : BArray40.t;
    var h : BArray8192.t;
    var h_count_i : int;
    var h_dsymswp : BArray528.t;
    var h_m_i : int;
    var h_offset_i : int;
    var h_symbolwp : BArray2048.t;
    var hb_count_i : int;
    var hb_dsymswp : BArray528.t;
    var hb_m_i : int;
    var hb_offset_i : int;
    var hb_symbolwp : BArray2048.t;
    var highbits : BArray8192.t;
    var highbits_len_i : int;
    var highbitsp : BArray8192.t;
    var highz : BArray8192.t;
    var highzp : BArray8192.t;
    var hp : BArray8192.t;
    var k : W64.t;
    var k_i : int;
    var kcount : W64.t;
    var l : W64.t;
    var l_i : int;
    var lcount : W64.t;
    var lowz : BArray8192.t;
    var lowzp : BArray8192.t;
    var m : W64.t;
    var m_i : int;
    var ms : W64.t;
    var norm_reject : W64.t;
    var payload_limit_i : int;
    var reject : W64.t;
    var sigbytes_i : int;
    var sqnorm2 : W64.t;
    var taildescp : BArray40.t;
    var tau_i : int;
    var vkbytes_i : int;
    var w : BArray8192.t;
    var wp_0 : BArray8192.t;
    var wprime : BArray1024.t;
    var wprimep : BArray1024.t;
    var z1 : BArray8192.t;
    var z1p : BArray8192.t;
    var z2 : BArray8192.t;
    var z2p : BArray8192.t;

    k_i <- 2;
    l_i <- 4;
    m_i <- 3;
    sigbytes_i <- 1474;
    vkbytes_i <- 992;
    highbits_len_i <- 576;
    tau_i <- 58;
    b2sq_i <- 163265017;
    hb_count_i <- 1024;
    hb_m_i <- 13;
    hb_offset_i <- 6;
    h_count_i <- 512;
    h_m_i <- 13;
    h_offset_i <- 239;
    base_hb_i <- 132;
    base_h_i <- 7;
    payload_limit_i <- 416;
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
    norm_reject <- W64.one;
    reject <- W64.one;
    sqnorm2 <- W64.zero;

    if (siglen <> W64.of_int sigbytes_i) {
      reject <- W64.one;
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
      a1p <@ Raw._unpack_vk_m23_full (a1p, vkp, vku, k, l, m);
      h_symbolwp <- RawVerifyApiTarget.jmode2_h_symbol_words;
      h_dsymswp <- RawVerifyApiTarget.jmode2_h_dsyms_words;
      hb_symbolwp <- RawVerifyApiTarget.jmode2_hb_z1_symbol_words;
      hb_dsymswp <- RawVerifyApiTarget.jmode2_hb_z1_dsyms_words;
      if (k_i = 3) {
        h_symbolwp <- RawVerifyApiTarget.jmode3_h_symbol_words;
        h_dsymswp <- RawVerifyApiTarget.jmode3_h_dsyms_words;
        hb_symbolwp <- RawVerifyApiTarget.jmode3_hb_z1_symbol_words;
        hb_dsymswp <- RawVerifyApiTarget.jmode3_hb_z1_dsyms_words;
      }
      cp <- c;
      lowzp <- lowz;
      highzp <- highz;
      hp <- h;
      badp <- bad;
      ms <- init_msf;
      badp <- protect_ptr badp ms;
      badp <- BArray8.set64 badp 0 W64.zero;
      ms <- init_msf;
      cp <- protect_ptr cp ms;
      lowzp <- protect_ptr lowzp ms;
      highzp <- protect_ptr highzp ms;
      hp <- protect_ptr hp ms;
      badp <- protect_ptr badp ms;
      sigp <- protect_ptr sigp ms;
      (cp, lowzp, highzp, hp, badp) <@ Raw._unpack_sig_full
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
      if (badv <> W64.zero) {
        reject <- W64.one;
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
        (z1p, wprimep, sqnorm2) <@ Raw._verify_prepare_z1_wprime
          (z1p, wprimep, highzp, lowzp, cp, lcount);
        highbitsp <- highbits;
        ms <- init_msf;
        z1p <- protect_ptr z1p ms;
        highbitsp <- protect_ptr highbitsp ms;
        a1p <- protect_ptr a1p ms;
        wprimep <- protect_ptr wprimep ms;
        k <- protect_64 k ms;
        l <- protect_64 l ms;
        (z1p, highbitsp) <@ Raw._verify_matrix_crt
          (z1p, highbitsp, a1p, wprimep, k, l);
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
        (wp_0, z2p) <@ Raw._sign_verify_recover_w_z2
          (wp_0, z2p, z1p, hp, wprimep,
           kcount, 256, 9, 252, 512);
        bound <- W64.of_int b2sq_i;
        ms <- init_msf;
        z2p <- protect_ptr z2p ms;
        sqnorm2 <- protect_64 sqnorm2 ms;
        kcount <- protect_64 kcount ms;
        bound <- protect_64 bound ms;
        reject <@ Raw._sign_verify_norm_reject
          (z2p, sqnorm2, kcount, bound);
        norm_reject <- reject;
        ms <- init_msf;
        reject <- protect_64 reject ms;
        if (reject = W64.zero) {
          taildescp <- copydescp;
          ms <- init_msf;
          wp_0 <- protect_ptr wp_0 ms;
          wprimep <- protect_ptr wprimep ms;
          cp <- protect_ptr cp ms;
          taildescp <- protect_ptr taildescp ms;
          reject <@ RawApiVerifyMuTrace.VerifyTailMuTrace.run
            (wp_0, wprimep, cp, taildescp,
             k_i, highbits_len_i, vkbytes_i, tau_i);
        }
      }
    }

    return
      (a1p, cp, lowzp, highzp, hp, badp,
       z1p, highbitsp, wprimep, sqnorm2,
       wp_0, z2p, norm_reject, reject);
  }
}.

op verify_full_mode2_functional_trace_result
    (siglen0 : W64.t) (vkp0 : BArray2752.t)
    (outmat : BArray32768.t)
    (parsed_cp : BArray1024.t)
    (parsed_low parsed_high parsed_h : BArray8192.t)
    (parsed_bad : BArray8.t)
    (out high : BArray8192.t)
    (outw : BArray1024.t) (total : W64.t)
    (w z2 : BArray8192.t) (norm_reject reject : W64.t) : bool =
  (siglen0 = W64.of_int 1474 =>
    raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
      vkp0
      witness<:BArray8192.t> witness<:BArray8192.t>
      witness<:BArray1024.t>
      witness<:BArray8192.t> witness<:BArray8192.t>
      outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
      out high outw total w z2 norm_reject reject) /\
  (siglen0 <> W64.of_int 1474 => reject = W64.one).

lemma verify_full_mode2_functional_trace_exact
    (sig0 : BArray2948.t) (siglen0 : W64.t)
    (vkp0 : BArray2752.t) (vku0 : int) (desc0 : BArray40.t) :
  hoare [VerifyFullMode2FunctionalTrace.run :
    sigp = sig0 /\ siglen = siglen0 /\ vkp = vkp0 /\
    vku = vku0 /\ descp = desc0
    ==>
    verify_full_mode2_functional_trace_result
      siglen0 vkp0
      res.`1 res.`2 res.`3 res.`4 res.`5 res.`6
      res.`7 res.`8 res.`9 res.`10 res.`11 res.`12 res.`13 res.`14].
proof.
proc.
sp 27.
if.
+ auto => />.
+ sp 17.
  exlim copydescp => copied_desc0.
  call
    (raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_exact
      witness vkp0 vku0
      witness witness witness witness witness witness witness
      witness witness witness sig0 copied_desc0).
  auto => />.
qed.

lemma actual_verify_full_mode2_exact_flat_trace :
  equiv [Raw._verify_full_mode2 ~ VerifyFullMode2FlatTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem} /\ res{1} = res{2}.`14].
proof.
proc.
inline Raw._verify_full_m23.
sim : (={Glob.mem, reject}).
qed.

end VerifyActualFullFunctionalRawPostFreeze.
