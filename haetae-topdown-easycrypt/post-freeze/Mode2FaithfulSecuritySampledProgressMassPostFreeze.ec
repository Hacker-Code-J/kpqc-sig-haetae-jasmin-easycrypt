require import AllCore Distr List Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray32.
require import HAETAE_Params HAETAE_Algebra HAETAE_Distributions.
require import KeygenMode2ParentSpec.
require import Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
               Mode2FaithfulSecurityNMAViewAdapterPostFreeze
               Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
               Mode2FaithfulSecurityRawSeedDistributionPostFreeze
               Mode2FaithfulSecurityInitializedNMAViewPostFreeze
               Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.

theory Mode2FaithfulSecuritySampledProgressMassPostFreeze.

import RealOrder.
import HAETAE_Distributions.

(* This file weakens the support-wide fixed progress hypothesis to a
   seed-by-seed existential certificate and exposes the unsupported mass as an
   explicit delta.  It does not prove that delta is zero, full retry
   termination, or any HAETAE.kg/public-key distribution equality. *)

type sampler_progress_witness =
  (int -> int -> int) * (int -> int) * (int -> int).

op sampler_progress_witness_valid
    (raw : BArray32.t) (w : sampler_progress_witness) : bool =
  KeygenMode2ParentSpec.mode2_sampler_prefix_progress
    raw w.`1 w.`2 w.`3.

op raw_seed_has_progress (raw : BArray32.t) : bool =
  exists w, sampler_progress_witness_valid raw w.

(* The selector is a logical proof witness only; it is not called by the
   sampled source and does not change its distribution or implementation. *)
op selected_sampler_progress_witness
    (raw : BArray32.t) : sampler_progress_witness =
  choiceb (sampler_progress_witness_valid raw) witness.

lemma selected_sampler_progress_witness_valid raw :
  raw_seed_has_progress raw =>
  sampler_progress_witness_valid raw
    (selected_sampler_progress_witness raw).
proof.
rewrite /raw_seed_has_progress /selected_sampler_progress_witness.
exact (choicebP (sampler_progress_witness_valid raw) witness).
qed.

op delta_sampler_progress : real =
  mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    (predC raw_seed_has_progress).

lemma delta_sampler_progress_bounded :
  0%r <= delta_sampler_progress <= 1%r.
proof.
rewrite /delta_sampler_progress.
exact mu_bounded.
qed.

lemma raw_seed_progress_good_massE :
  mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    raw_seed_has_progress =
  1%r - delta_sampler_progress.
proof.
have hnot :=
  mu_not Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    raw_seed_has_progress.
have hll :=
  Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed_lossless.
rewrite /is_lossless in hll.
rewrite /delta_sampler_progress in hnot.
smt().
qed.

lemma initialized_checked_source_good_raw_ll
    (raw_init : BArray32.t) :
  phoare [Mode2FaithfulSecurityInitializedNMAViewPostFreeze
            .InitializedCheckedSourceSample.main :
    seedbuf0 =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128 /\
    mat0 =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768 /\
    avec0 =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    s10 = Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    s20 = Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    bp0 = Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    s1hat0 =
      Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192 /\
    raw0 = raw_init /\
    raw_seed_has_progress raw_init
    ==> true] >= 1%r.
proof.
conseq
  (Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
    .initialized_checked_source_sample_progress_ll
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_seedbuf128
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_mat32768
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze.zero_vec8192
    raw_init
    (selected_sampler_progress_witness raw_init).`1
    (selected_sampler_progress_witness raw_init).`2
    (selected_sampler_progress_witness raw_init).`3) => //=.
move=> &hr
  [hseedbuf [hmat [havec [hs1 [hs2 [hbp [hs1hat [hraw hgood]]]]]]]].
have hselected := selected_sampler_progress_witness_valid raw_init hgood.
smt().
qed.

lemma sampled_checked_source_termination_progress_mass :
  phoare [Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
            .SampledCheckedPublicKeySource.sample :
    true ==> true] >=
  (mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
    raw_seed_has_progress).
proof.
proc.
seq 1 :
  (raw_seed_has_progress
    Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
      .SampledCheckedPublicKeySource.raw_current)
  (mu Mode2FaithfulSecurityRawSeedDistributionPostFreeze.draw_raw_seed
     raw_seed_has_progress)
  1%r 0%r _ => //=.
+ by rnd raw_seed_has_progress; skip.
wp.
exlim
  Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
    .SampledCheckedPublicKeySource.raw_current => raw0.
call (initialized_checked_source_good_raw_ll raw0).
auto => />.
qed.

lemma sampled_checked_source_termination_mass :
  phoare [Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
            .SampledCheckedPublicKeySource.sample :
    true ==> true] >= (1%r - delta_sampler_progress).
proof.
rewrite -raw_seed_progress_good_massE.
exact sampled_checked_source_termination_progress_mass.
qed.

lemma sampled_checked_source_ready_mass :
  phoare [Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
            .SampledCheckedPublicKeySource.sample :
    true ==>
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
        Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
          .SampledCheckedPublicKeySource.raw_current] >=
  (1%r - delta_sampler_progress).
proof.
conseq
  sampled_checked_source_termination_mass
  Mode2FaithfulSecuritySampledCheckedSourcePostFreeze
    .sampled_checked_source_sample_ready => //=.
qed.

end Mode2FaithfulSecuritySampledProgressMassPostFreeze.
