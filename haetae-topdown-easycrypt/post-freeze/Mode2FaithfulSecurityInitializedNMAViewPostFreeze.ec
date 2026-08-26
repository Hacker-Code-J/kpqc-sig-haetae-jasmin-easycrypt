require import AllCore List.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import HAETAE_Params HAETAE_Algebra HAETAE_Scheme.
require import TargetKeygenM23FinalizeComposition.
require import Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
               Mode2FaithfulSecurityNMAViewAdapterPostFreeze.

theory Mode2FaithfulSecurityInitializedNMAViewPostFreeze.

import HAETAE_Params.
import HAETAE_Algebra.
import HAETAE_Scheme.

(* These initialized front-ends only preload the eight checked-parent inputs
   into [CheckedMode2PublicKeySource].  They do not claim losslessness,
   retry termination, input distribution, HAETAE.kg/API equality, or any CMA
   semantics. *)

module InitializedCheckedSourceSample = {
  proc main
      (seedbuf0 : BArray128.t, mat0 : BArray32768.t,
       avec0 : BArray8192.t, s10 : BArray8192.t, s20 : BArray8192.t,
       bp0 : BArray8192.t, s1hat0 : BArray8192.t, raw0 : BArray32.t)
      : pkey = {
    var pk : pkey;

    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.seedbuf_in <- seedbuf0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.mat_in <- mat0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.avec_in <- avec0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.s1_in <- s10;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.s2_in <- s20;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.bp_in <- bp0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.s1hatp_in <- s1hat0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.raw_seed_in <- raw0;
    pk <@
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.sample();
    return pk;
  }
}.

module InitializedCheckedWrapperUFNMA
    (H : SIG.Oracle, A : SIG.NMA_Adversary) = {
  proc main
      (seedbuf0 : BArray128.t, mat0 : BArray32768.t,
       avec0 : BArray8192.t, s10 : BArray8192.t, s20 : BArray8192.t,
       bp0 : BArray8192.t, s1hat0 : BArray8192.t, raw0 : BArray32.t)
      : bool = {
    var b : bool;

    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.seedbuf_in <- seedbuf0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.mat_in <- mat0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.avec_in <- avec0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.s1_in <- s10;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.s2_in <- s20;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.bp_in <- bp0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.s1hatp_in <- s1hat0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.raw_seed_in <- raw0;
    b <@
      SIG.UF_NMA(
        H,
        Mode2FaithfulSecurityNMAViewAdapterPostFreeze
          .NMAViewScheme(
            Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
              .CheckedMode2PublicKeySource),
        A).main();
    return b;
  }
}.

module InitializedCheckedDirectUFNMA
    (H : SIG.Oracle, A : SIG.NMA_Adversary) = {
  proc main
      (seedbuf0 : BArray128.t, mat0 : BArray32768.t,
       avec0 : BArray8192.t, s10 : BArray8192.t, s20 : BArray8192.t,
       bp0 : BArray8192.t, s1hat0 : BArray8192.t, raw0 : BArray32.t)
      : bool = {
    var b : bool;

    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.seedbuf_in <- seedbuf0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.mat_in <- mat0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.avec_in <- avec0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.s1_in <- s10;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.s2_in <- s20;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.bp_in <- bp0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.s1hatp_in <- s1hat0;
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource.raw_seed_in <- raw0;
    b <@
      Mode2FaithfulSecurityNMAViewAdapterPostFreeze
        .DirectPublicOnlyUFNMA(
          H,
          Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
            .CheckedMode2PublicKeySource,
          A).main();
    return b;
  }
}.

lemma initialized_checked_source_sample_ready
    (seedbuf_init : BArray128.t)
    (mat_init : BArray32768.t)
    (avec_init s1_init s2_init bp_init s1hat_init : BArray8192.t)
    (raw_init : BArray32.t) :
  hoare [InitializedCheckedSourceSample.main :
    seedbuf0 = seedbuf_init /\ mat0 = mat_init /\ avec0 = avec_init /\
    s10 = s1_init /\ s20 = s2_init /\ bp0 = bp_init /\
    s1hat0 = s1hat_init /\ raw0 = raw_init
    ==>
    res =
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.pk_current /\
    Mode2FaithfulSecurityNMAViewAdapterPostFreeze
      .faithful_mode2_nma_ready
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
        .CheckedMode2PublicKeySource.eadj_current].
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

section InitializedCheckedNMAExact.

declare module H <: SIG.Oracle
  {-SIG.UF_NMA,
   -InitializedCheckedWrapperUFNMA,
   -InitializedCheckedDirectUFNMA,
   -Mode2FaithfulSecurityNMAViewAdapterPostFreeze.DirectPublicOnlyUFNMA,
   -Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource}.
declare module A <: SIG.NMA_Adversary
  {-H, -SIG.UF_NMA,
   -InitializedCheckedWrapperUFNMA,
   -InitializedCheckedDirectUFNMA,
   -Mode2FaithfulSecurityNMAViewAdapterPostFreeze.DirectPublicOnlyUFNMA,
   -Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource}.

lemma initialized_checked_direct_main_ready
    (seedbuf_init : BArray128.t)
    (mat_init : BArray32768.t)
    (avec_init s1_init s2_init bp_init s1hat_init : BArray8192.t)
    (raw_init : BArray32.t) :
  hoare [InitializedCheckedDirectUFNMA(H, A).main :
    seedbuf0 = seedbuf_init /\ mat0 = mat_init /\ avec0 = avec_init /\
    s10 = s1_init /\ s20 = s2_init /\ bp0 = bp_init /\
    s1hat0 = s1hat_init /\ raw0 = raw_init
    ==>
    Mode2FaithfulSecurityNMAViewAdapterPostFreeze
      .faithful_mode2_nma_ready
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
        .CheckedMode2PublicKeySource.eadj_current].
proof.
proc.
inline
  Mode2FaithfulSecurityNMAViewAdapterPostFreeze
    .DirectPublicOnlyUFNMA(
      H,
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource,
      A).main.
wp.
call (_ : true).
+ by auto.
wp.
call
  (Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
    .checked_mode2_public_key_source_sample_ready
    seedbuf_init mat_init avec_init s1_init s2_init
    bp_init s1hat_init raw_init).
wp.
call (_ : true).
by auto => />.
qed.

lemma initialized_checked_wrapper_direct_equiv :
  equiv [InitializedCheckedWrapperUFNMA(H, A).main ~
         InitializedCheckedDirectUFNMA(H, A).main :
    ={glob H, glob A,
      glob Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
             .CheckedMode2PublicKeySource,
      arg} ==> ={res}].
proof.
proc.
wp.
call
  (Mode2FaithfulSecurityNMAViewAdapterPostFreeze
    .public_only_nma_equiv
    H
    Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
      .CheckedMode2PublicKeySource
    A).
auto => />.
qed.

lemma initialized_checked_wrapper_direct_exact
    &m
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw0 : BArray32.t) :
  Pr[InitializedCheckedWrapperUFNMA(H, A).main(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0, raw0)
       @ &m : res] =
  Pr[InitializedCheckedDirectUFNMA(H, A).main(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0, raw0)
       @ &m : res].
proof.
byequiv initialized_checked_wrapper_direct_equiv => //.
qed.

end section InitializedCheckedNMAExact.

end Mode2FaithfulSecurityInitializedNMAViewPostFreeze.
