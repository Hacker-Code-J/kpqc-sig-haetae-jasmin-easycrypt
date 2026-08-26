require import AllCore Distr List.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import HAETAE_Params HAETAE_Algebra HAETAE_Distributions
               HAETAE_Scheme.
require import KeygenMode2ParentSpec.
require import Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
               Mode2FaithfulSecurityRawSeedDistributionPostFreeze
               Mode2FaithfulSecurityInitializedNMAViewPostFreeze
               Mode2FaithfulSecurityCheckedSourceLosslessPostFreeze
               Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
               Mode2FaithfulSecurityNMAViewAdapterPostFreeze.

theory Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.

import HAETAE_Params.
import HAETAE_Algebra.
import HAETAE_Distributions.
import HAETAE_Scheme.

(* This source samples exactly the raw 32-byte seed distribution and feeds it
   into the initialized checked source with fixed zero scratch arrays.  It does
   not claim full retry termination, equality with [HAETAE.kg], or equality
   with the actual public-key distribution. *)

op zero_seedbuf128 : BArray128.t = BArray128.init_arr W8.zero.
op zero_mat32768 : BArray32768.t = BArray32768.init_arr W8.zero.
op zero_vec8192 : BArray8192.t = BArray8192.init_arr W8.zero.

(* This is an explicit hypothesis for the conditional losslessness theorem;
   this file does not prove that one fixed witness family covers all seeds. *)
op sampled_checked_source_progress mat_limit vec_limit eta_limit : bool =
  forall raw,
    raw \in
      Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed =>
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw mat_limit vec_limit eta_limit.

lemma draw_raw_seed_support_decodes_dseed raw :
  raw \in Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed =>
  Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed raw
    \in dseed.
proof.
rewrite
  /Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
  supp_dmap.
move=> [sd [hsd ->]].
rewrite
  Mode2FaithfulSecurityRawSeedDistributionPostFreeze
    .raw_security_seed_roundtrip //.
qed.

module SampledCheckedPublicKeySource
    : Mode2FaithfulSecurityNMAViewAdapterPostFreeze.PublicKeySource = {
  var raw_current : BArray32.t

  proc sample() : pkey = {
    var pk : pkey;

    raw_current <$
      Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed;
    pk <@
      Mode2FaithfulSecurityInitializedNMAViewPostFreeze
        .InitializedCheckedSourceSample.main(
          zero_seedbuf128, zero_mat32768,
          zero_vec8192, zero_vec8192, zero_vec8192,
          zero_vec8192, zero_vec8192, raw_current);
    return pk;
  }
}.

lemma initialized_checked_source_sample_ready_sd
    (seedbuf_init : BArray128.t)
    (mat_init : BArray32768.t)
    (avec_init s1_init s2_init bp_init s1hat_init : BArray8192.t)
    (raw_init : BArray32.t) :
  hoare [Mode2FaithfulSecurityInitializedNMAViewPostFreeze
           .InitializedCheckedSourceSample.main :
    seedbuf0 = seedbuf_init /\ mat0 = mat_init /\ avec0 = avec_init /\
    s10 = s1_init /\ s20 = s2_init /\ bp0 = bp_init /\
    s1hat0 = s1hat_init /\ raw0 = raw_init
    ==>
    res =
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.pk_current /\
    Mode2FaithfulSecurityNMAViewAdapterPostFreeze.faithful_mode2_nma_ready
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.pk_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.sd_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.a_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.b1_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.agen_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.sgen_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.eadj_current /\
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.sd_current =
      Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed
        raw_init].
proof.
proc.
wp.
call
  (Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
    .checked_mode2_public_key_source_sample_ready
    seedbuf_init mat_init avec_init s1_init s2_init
    bp_init s1hat_init raw_init).
auto => />.
qed.

lemma initialized_checked_source_sample_progress_ll
    (seedbuf_init : BArray128.t)
    (mat_init : BArray32768.t)
    (avec_init s1_init s2_init bp_init s1hat_init : BArray8192.t)
    (raw_init : BArray32.t)
    mat_limit vec_limit eta_limit :
  phoare [Mode2FaithfulSecurityInitializedNMAViewPostFreeze
            .InitializedCheckedSourceSample.main :
    seedbuf0 = seedbuf_init /\ mat0 = mat_init /\ avec0 = avec_init /\
    s10 = s1_init /\ s20 = s2_init /\ bp0 = bp_init /\
    s1hat0 = s1hat_init /\ raw0 = raw_init /\
    KeygenMode2ParentSpec.mode2_sampler_prefix_progress
      raw_init mat_limit vec_limit eta_limit
    ==> true] = 1%r.
proof.
proc.
wp.
call
  (Mode2FaithfulSecurityCheckedSourceLosslessPostFreeze
    .checked_mode2_public_key_source_sample_progress_ll
    seedbuf_init raw_init mat_limit vec_limit eta_limit).
auto => />.
qed.

lemma sampled_checked_source_sample_ready :
  hoare [SampledCheckedPublicKeySource.sample : true ==>
    res =
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.pk_current /\
    Mode2FaithfulSecurityNMAViewAdapterPostFreeze.faithful_mode2_nma_ready
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.pk_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.sd_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.a_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.b1_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.agen_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.sgen_current
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.eadj_current /\
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.sd_current \in dseed /\
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.sd_current =
      Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed
        SampledCheckedPublicKeySource.raw_current].
proof.
proc.
seq 1 :
  (SampledCheckedPublicKeySource.raw_current \in
    Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed).
+ rnd; auto.
wp.
exlim SampledCheckedPublicKeySource.raw_current => raw0.
call
  (initialized_checked_source_sample_ready_sd
    zero_seedbuf128 zero_mat32768
    zero_vec8192 zero_vec8192 zero_vec8192 zero_vec8192 zero_vec8192
    raw0).
auto => />.
move=> hraw *.
exact (draw_raw_seed_support_decodes_dseed raw0 hraw).
qed.

lemma sampled_checked_source_sample_progress_ll
    mat_limit vec_limit eta_limit :
  phoare [SampledCheckedPublicKeySource.sample :
    sampled_checked_source_progress mat_limit vec_limit eta_limit
    ==> true] = 1%r.
proof.
proc.
seq 1 :
  (sampled_checked_source_progress mat_limit vec_limit eta_limit /\
   SampledCheckedPublicKeySource.raw_current \in
     Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed)
  1%r 1%r 0%r _ => //=.
+ rnd.
  auto => />.
  move=> _.
  rewrite -weightE_support.
  exact
    Mode2FaithfulSecurityRawSeedDistributionPostFreeze
      .draw_raw_seed_lossless.
wp.
exlim SampledCheckedPublicKeySource.raw_current => raw0.
call
  (initialized_checked_source_sample_progress_ll
    zero_seedbuf128 zero_mat32768
    zero_vec8192 zero_vec8192 zero_vec8192 zero_vec8192 zero_vec8192 raw0
    mat_limit vec_limit eta_limit).
auto => />.
move=> hprogress hraw.
exact (hprogress raw0 hraw).
rnd.
auto.
move=> _ hprogress.
apply mu0_false => raw hraw.
by rewrite hprogress.
qed.

section SampledCheckedSourceNMAExact.

declare module H <: SIG.Oracle
  {-SIG.UF_NMA,
   -Mode2FaithfulSecurityNMAViewAdapterPostFreeze.DirectPublicOnlyUFNMA,
   -SampledCheckedPublicKeySource,
   -Mode2FaithfulSecurityInitializedNMAViewPostFreeze
      .InitializedCheckedSourceSample,
   -Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource}.
declare module A <: SIG.NMA_Adversary
  {-H, -SIG.UF_NMA,
   -Mode2FaithfulSecurityNMAViewAdapterPostFreeze.DirectPublicOnlyUFNMA,
   -SampledCheckedPublicKeySource,
   -Mode2FaithfulSecurityInitializedNMAViewPostFreeze
      .InitializedCheckedSourceSample,
   -Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource}.

lemma sampled_checked_source_wrapper_direct_exact &m :
  Pr[SIG.UF_NMA(
       H,
       Mode2FaithfulSecurityNMAViewAdapterPostFreeze
         .NMAViewScheme(SampledCheckedPublicKeySource),
       A).main() @ &m : res] =
  Pr[Mode2FaithfulSecurityNMAViewAdapterPostFreeze
       .DirectPublicOnlyUFNMA(H, SampledCheckedPublicKeySource, A).main()
       @ &m : res].
proof.
exact
  (Mode2FaithfulSecurityNMAViewAdapterPostFreeze
    .public_only_nma_wrapper_direct_exact
    H SampledCheckedPublicKeySource A &m).
qed.

end section SampledCheckedSourceNMAExact.

end Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.
