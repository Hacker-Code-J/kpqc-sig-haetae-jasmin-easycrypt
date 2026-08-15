require import AllCore.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray8 BArray40 BArray1024 BArray2752 BArray2948
               BArray8192 BArray32768
               RawVerifyApiTarget RawApiVerifyAcceptTrace
               VerifySignatureUnpackPrepareMatrixCrtRecoverNormTailRawCompositionPostFreeze
               VerifyActualFullFunctionalRawPostFreeze
               VerifyActualFullAcceptRawPostFreeze.

import VerifySignatureUnpackPrepareMatrixCrtRecoverNormTailRawCompositionPostFreeze
       VerifyActualFullFunctionalRawPostFreeze
       VerifyActualFullAcceptRawPostFreeze.

theory VerifyActualFullAcceptApiRawPostFreeze.

module Raw = RawVerifyApiTarget.M.
module Flat = VerifyFullMode2FlatTrace.

op accepted_full_trace_result
    (vkp0 : BArray2752.t)
    (outmat : BArray32768.t)
    (parsed_cp : BArray1024.t)
    (parsed_low parsed_high parsed_h : BArray8192.t)
    (parsed_bad : BArray8.t)
    (out high : BArray8192.t)
    (outw : BArray1024.t) (total : W64.t)
    (w z2 : BArray8192.t) (norm_reject reject : W64.t) : bool =
  raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
    vkp0
    witness<:BArray8192.t> witness<:BArray8192.t>
    witness<:BArray1024.t>
    witness<:BArray8192.t> witness<:BArray8192.t>
    outmat parsed_cp parsed_low parsed_high parsed_h parsed_bad
    out high outw total w z2 norm_reject reject.

module VerifyInternalMode2FlatTrace = {
  var observed_vk : BArray2752.t
  var out_mat : BArray32768.t
  var out_cp : BArray1024.t
  var out_low : BArray8192.t
  var out_high : BArray8192.t
  var out_h : BArray8192.t
  var out_bad : BArray8.t
  var out_z1 : BArray8192.t
  var out_highbits : BArray8192.t
  var out_wprime : BArray1024.t
  var out_total : W64.t
  var out_w : BArray8192.t
  var out_z2 : BArray8192.t
  var out_norm_reject : W64.t
  var out_reject : W64.t

  proc run
      (sigp : BArray2948.t, siglen : W64.t, vkp : BArray2752.t,
       vku : int, descp : BArray40.t) : W64.t = {
    var ms : W64.t;

    ms <- init_msf;
    siglen <- protect_64 siglen ms;
    (out_mat, out_cp, out_low, out_high, out_h, out_bad,
     out_z1, out_highbits, out_wprime, out_total,
     out_w, out_z2, out_norm_reject, out_reject) <@
      Flat.run (sigp, siglen, vkp, vku, descp);
    observed_vk <- vkp;
    return out_reject;
  }
}.

module VerifyRawApiFlatTrace = {
  var observed_vk : BArray2752.t
  var out_mat : BArray32768.t
  var out_cp : BArray1024.t
  var out_low : BArray8192.t
  var out_high : BArray8192.t
  var out_h : BArray8192.t
  var out_bad : BArray8.t
  var out_z1 : BArray8192.t
  var out_highbits : BArray8192.t
  var out_wprime : BArray1024.t
  var out_total : W64.t
  var out_w : BArray8192.t
  var out_z2 : BArray8192.t
  var out_norm_reject : W64.t
  var out_reject : W64.t

  proc run
      (sigu : int, siglen : W64.t, mu : W64.t, mlen : W64.t,
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
    if (siglen <> W64.of_int 1474) {
      reject <- W64.one;
    } else {
      sigp <- sig;
      vkp <- vk;
      descp <- desc;
      sigp <@ Raw._api_copy_raw_to_2948_prefix (sigp, sigu, 1474);
      vkp <@ Raw._api_copy_raw_to_2752_prefix (vkp, vku, 992);
      descp <- BArray40.set64 descp 0 (W64.of_int vku);
      descp <- BArray40.set64 descp 1 preu;
      descp <- BArray40.set64 descp 2 prelen;
      descp <- BArray40.set64 descp 3 mu;
      descp <- BArray40.set64 descp 4 mlen;
      reject <@ VerifyInternalMode2FlatTrace.run
        (sigp, W64.of_int 1474, vkp, vku, descp);
      observed_vk <- VerifyInternalMode2FlatTrace.observed_vk;
      out_mat <- VerifyInternalMode2FlatTrace.out_mat;
      out_cp <- VerifyInternalMode2FlatTrace.out_cp;
      out_low <- VerifyInternalMode2FlatTrace.out_low;
      out_high <- VerifyInternalMode2FlatTrace.out_high;
      out_h <- VerifyInternalMode2FlatTrace.out_h;
      out_bad <- VerifyInternalMode2FlatTrace.out_bad;
      out_z1 <- VerifyInternalMode2FlatTrace.out_z1;
      out_highbits <- VerifyInternalMode2FlatTrace.out_highbits;
      out_wprime <- VerifyInternalMode2FlatTrace.out_wprime;
      out_total <- VerifyInternalMode2FlatTrace.out_total;
      out_w <- VerifyInternalMode2FlatTrace.out_w;
      out_z2 <- VerifyInternalMode2FlatTrace.out_z2;
      out_norm_reject <- VerifyInternalMode2FlatTrace.out_norm_reject;
      out_reject <- VerifyInternalMode2FlatTrace.out_reject;
    }
    return reject;
  }
}.

module VerifyCryptolabFlatTrace = {
  var observed_vk : BArray2752.t
  var out_mat : BArray32768.t
  var out_cp : BArray1024.t
  var out_low : BArray8192.t
  var out_high : BArray8192.t
  var out_h : BArray8192.t
  var out_bad : BArray8.t
  var out_z1 : BArray8192.t
  var out_highbits : BArray8192.t
  var out_wprime : BArray1024.t
  var out_total : W64.t
  var out_w : BArray8192.t
  var out_z2 : BArray8192.t
  var out_norm_reject : W64.t
  var out_reject : W64.t

  proc run
      (sigu : int, siglen : int, mu : int, mlen : int,
       preu : int, prelen : int, vku : int) : W64.t = {
    var r : W64.t;
    var reject : W64.t;

    reject <@ VerifyRawApiFlatTrace.run
      (sigu, W64.of_int siglen, W64.of_int mu, W64.of_int mlen,
       W64.of_int preu, W64.of_int prelen, vku);
    reject <@ Raw._verify_publish_reject (reject);
    if (reject = W64.zero) {
      r <- W64.zero;
    } else {
      r <@ Raw._api_reject ();
    }
    observed_vk <- VerifyRawApiFlatTrace.observed_vk;
    out_mat <- VerifyRawApiFlatTrace.out_mat;
    out_cp <- VerifyRawApiFlatTrace.out_cp;
    out_low <- VerifyRawApiFlatTrace.out_low;
    out_high <- VerifyRawApiFlatTrace.out_high;
    out_h <- VerifyRawApiFlatTrace.out_h;
    out_bad <- VerifyRawApiFlatTrace.out_bad;
    out_z1 <- VerifyRawApiFlatTrace.out_z1;
    out_highbits <- VerifyRawApiFlatTrace.out_highbits;
    out_wprime <- VerifyRawApiFlatTrace.out_wprime;
    out_total <- VerifyRawApiFlatTrace.out_total;
    out_w <- VerifyRawApiFlatTrace.out_w;
    out_z2 <- VerifyRawApiFlatTrace.out_z2;
    out_norm_reject <- VerifyRawApiFlatTrace.out_norm_reject;
    out_reject <- VerifyRawApiFlatTrace.out_reject;
    return r;
  }
}.

lemma verify_internal_mode2_exact_flat_trace :
  equiv [Raw.sign_verify_internal_mode2_jazz ~ VerifyInternalMode2FlatTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp}
    ==>
    ={Glob.mem, res}].
proof.
proc.
wp.
call actual_verify_full_mode2_exact_flat_trace.
sim.
qed.

lemma verify_internal_mode2_flat_trace_accept_exact :
  hoare [VerifyInternalMode2FlatTrace.run :
    siglen = W64.of_int 1474
    ==>
    res = W64.zero =>
    accepted_full_trace_result
      VerifyInternalMode2FlatTrace.observed_vk
      VerifyInternalMode2FlatTrace.out_mat
      VerifyInternalMode2FlatTrace.out_cp
      VerifyInternalMode2FlatTrace.out_low
      VerifyInternalMode2FlatTrace.out_high
      VerifyInternalMode2FlatTrace.out_h
      VerifyInternalMode2FlatTrace.out_bad
      VerifyInternalMode2FlatTrace.out_z1
      VerifyInternalMode2FlatTrace.out_highbits
      VerifyInternalMode2FlatTrace.out_wprime
      VerifyInternalMode2FlatTrace.out_total
      VerifyInternalMode2FlatTrace.out_w
      VerifyInternalMode2FlatTrace.out_z2
      VerifyInternalMode2FlatTrace.out_norm_reject
      VerifyInternalMode2FlatTrace.out_reject].
proof.
proc.
wp.
exists* sigp{hr}, vkp{hr}, vku{hr}, descp{hr};
elim* => sig0 vkp0 vku0 desc0.
call (verify_full_mode2_flat_trace_accept_exact sig0 vkp0 vku0 desc0).
auto => /> &hr result hresult hzero.
move: (hresult hzero).
rewrite
  /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
  /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result.
smt().
qed.

lemma actual_verify_internal_mode2_accept_exact_flat_trace :
  equiv [Raw.sign_verify_internal_mode2_jazz ~ VerifyInternalMode2FlatTrace.run :
    ={Glob.mem, sigp, siglen, vkp, vku, descp} /\
    siglen{2} = W64.of_int 1474
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero =>
      accepted_full_trace_result
        VerifyInternalMode2FlatTrace.observed_vk{2}
        VerifyInternalMode2FlatTrace.out_mat{2}
        VerifyInternalMode2FlatTrace.out_cp{2}
        VerifyInternalMode2FlatTrace.out_low{2}
        VerifyInternalMode2FlatTrace.out_high{2}
        VerifyInternalMode2FlatTrace.out_h{2}
        VerifyInternalMode2FlatTrace.out_bad{2}
        VerifyInternalMode2FlatTrace.out_z1{2}
        VerifyInternalMode2FlatTrace.out_highbits{2}
        VerifyInternalMode2FlatTrace.out_wprime{2}
        VerifyInternalMode2FlatTrace.out_total{2}
        VerifyInternalMode2FlatTrace.out_w{2}
        VerifyInternalMode2FlatTrace.out_z2{2}
        VerifyInternalMode2FlatTrace.out_norm_reject{2}
        VerifyInternalMode2FlatTrace.out_reject{2})].
proof.
conseq verify_internal_mode2_exact_flat_trace
  (_ : true ==> true)
  verify_internal_mode2_flat_trace_accept_exact => //=.
qed.

lemma verify_raw_api_exact_flat_trace :
  equiv [Raw._api_verify_mode2_raw ~ VerifyRawApiFlatTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res}].
proof.
proc.
sp.
if => //.
+ sim.
+ wp.
  call verify_internal_mode2_exact_flat_trace.
  sim : (={Glob.mem, sigp, vkp, vku, descp}).
qed.

lemma verify_raw_api_flat_trace_accept_exact :
  hoare [VerifyRawApiFlatTrace.run :
    true
    ==>
    res = W64.zero =>
    accepted_full_trace_result
      VerifyRawApiFlatTrace.observed_vk
      VerifyRawApiFlatTrace.out_mat
      VerifyRawApiFlatTrace.out_cp
      VerifyRawApiFlatTrace.out_low
      VerifyRawApiFlatTrace.out_high
      VerifyRawApiFlatTrace.out_h
      VerifyRawApiFlatTrace.out_bad
      VerifyRawApiFlatTrace.out_z1
      VerifyRawApiFlatTrace.out_highbits
      VerifyRawApiFlatTrace.out_wprime
      VerifyRawApiFlatTrace.out_total
      VerifyRawApiFlatTrace.out_w
      VerifyRawApiFlatTrace.out_z2
      VerifyRawApiFlatTrace.out_norm_reject
      VerifyRawApiFlatTrace.out_reject].
proof.
proc.
sp.
if.
+ auto => />.
  rewrite /W64.one /W64.zero /=.
  smt().
+ wp.
  call verify_internal_mode2_flat_trace_accept_exact.
  wp.
  call (_ : true ==> true); first by auto.
  wp.
  call (_ : true ==> true); first by auto.
  auto.
qed.

lemma actual_verify_raw_api_accept_exact_flat_trace :
  equiv [Raw._api_verify_mode2_raw ~ VerifyRawApiFlatTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero =>
      accepted_full_trace_result
        VerifyRawApiFlatTrace.observed_vk{2}
        VerifyRawApiFlatTrace.out_mat{2}
        VerifyRawApiFlatTrace.out_cp{2}
        VerifyRawApiFlatTrace.out_low{2}
        VerifyRawApiFlatTrace.out_high{2}
        VerifyRawApiFlatTrace.out_h{2}
        VerifyRawApiFlatTrace.out_bad{2}
        VerifyRawApiFlatTrace.out_z1{2}
        VerifyRawApiFlatTrace.out_highbits{2}
        VerifyRawApiFlatTrace.out_wprime{2}
        VerifyRawApiFlatTrace.out_total{2}
        VerifyRawApiFlatTrace.out_w{2}
        VerifyRawApiFlatTrace.out_z2{2}
        VerifyRawApiFlatTrace.out_norm_reject{2}
        VerifyRawApiFlatTrace.out_reject{2})].
proof.
conseq verify_raw_api_exact_flat_trace
  (_ : true ==> true)
  verify_raw_api_flat_trace_accept_exact => //=.
qed.

lemma verify_cryptolab_exact_flat_trace :
  equiv [Raw.cryptolab_haetae_mode2_verify_internal ~ VerifyCryptolabFlatTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res}].
proof.
proc.
seq 1 1 : (={Glob.mem, reject}).
+ call verify_raw_api_exact_flat_trace.
  auto.
+ sim.
qed.

lemma verify_cryptolab_flat_trace_accept_exact :
  hoare [VerifyCryptolabFlatTrace.run :
    true
    ==>
    res = W64.zero =>
    accepted_full_trace_result
      VerifyCryptolabFlatTrace.observed_vk
      VerifyCryptolabFlatTrace.out_mat
      VerifyCryptolabFlatTrace.out_cp
      VerifyCryptolabFlatTrace.out_low
      VerifyCryptolabFlatTrace.out_high
      VerifyCryptolabFlatTrace.out_h
      VerifyCryptolabFlatTrace.out_bad
      VerifyCryptolabFlatTrace.out_z1
      VerifyCryptolabFlatTrace.out_highbits
      VerifyCryptolabFlatTrace.out_wprime
      VerifyCryptolabFlatTrace.out_total
      VerifyCryptolabFlatTrace.out_w
      VerifyCryptolabFlatTrace.out_z2
      VerifyCryptolabFlatTrace.out_norm_reject
      VerifyCryptolabFlatTrace.out_reject].
proof.
proc.
seq 2 :
  (reject = W64.zero =>
    accepted_full_trace_result
      VerifyRawApiFlatTrace.observed_vk
      VerifyRawApiFlatTrace.out_mat
      VerifyRawApiFlatTrace.out_cp
      VerifyRawApiFlatTrace.out_low
      VerifyRawApiFlatTrace.out_high
      VerifyRawApiFlatTrace.out_h
      VerifyRawApiFlatTrace.out_bad
      VerifyRawApiFlatTrace.out_z1
      VerifyRawApiFlatTrace.out_highbits
      VerifyRawApiFlatTrace.out_wprime
      VerifyRawApiFlatTrace.out_total
      VerifyRawApiFlatTrace.out_w
      VerifyRawApiFlatTrace.out_z2
      VerifyRawApiFlatTrace.out_norm_reject
      VerifyRawApiFlatTrace.out_reject).
+ inline Raw._verify_publish_reject.
  wp.
  call verify_raw_api_flat_trace_accept_exact.
  auto => />.
  move=> result observed_vk out_bad out_cp out_h out_high out_highbits
    out_low out_mat out_norm_reject out_reject out_total out_w out_wprime
    out_z1 out_z2 hresult hzero.
  move: (hresult hzero).
  rewrite
    /accepted_full_trace_result
    /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_tail_mode2_result
    /raw_verify_signature_unpack_prepare_matrix_crt_recover_norm_mode2_result.
  smt().
+ if.
  + auto.
  + wp.
    call RawApiVerifyAcceptTrace.api_reject_returns_nonzero.
    auto => />; smt().
qed.

lemma actual_verify_cryptolab_accept_exact_flat_trace :
  equiv [Raw.cryptolab_haetae_mode2_verify_internal ~ VerifyCryptolabFlatTrace.run :
    ={Glob.mem, sigu, siglen, mu, mlen, preu, prelen, vku}
    ==>
    ={Glob.mem, res} /\
    (res{1} = W64.zero =>
      accepted_full_trace_result
        VerifyCryptolabFlatTrace.observed_vk{2}
        VerifyCryptolabFlatTrace.out_mat{2}
        VerifyCryptolabFlatTrace.out_cp{2}
        VerifyCryptolabFlatTrace.out_low{2}
        VerifyCryptolabFlatTrace.out_high{2}
        VerifyCryptolabFlatTrace.out_h{2}
        VerifyCryptolabFlatTrace.out_bad{2}
        VerifyCryptolabFlatTrace.out_z1{2}
        VerifyCryptolabFlatTrace.out_highbits{2}
        VerifyCryptolabFlatTrace.out_wprime{2}
        VerifyCryptolabFlatTrace.out_total{2}
        VerifyCryptolabFlatTrace.out_w{2}
        VerifyCryptolabFlatTrace.out_z2{2}
        VerifyCryptolabFlatTrace.out_norm_reject{2}
        VerifyCryptolabFlatTrace.out_reject{2})].
proof.
conseq verify_cryptolab_exact_flat_trace
  (_ : true ==> true)
  verify_cryptolab_flat_trace_accept_exact => //=.
qed.

end VerifyActualFullAcceptApiRawPostFreeze.
