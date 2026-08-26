require import AllCore List.

from Jasmin require import JModel_x86.

require import BArray32 BArray128 BArray8192 BArray32768.
require import HAETAE_Params HAETAE_Algebra HAETAE_Scheme.
require import TargetKeygenM23FinalizeComposition.
require import Mode2FaithfulSecurityExpandVecAPostFreeze
               Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze
               Mode2FaithfulSecurityKeygenPaperLiftPostFreeze
               Mode2FaithfulSecurityKeygenViewPostFreeze
               Mode2FaithfulSecurityNMAViewAdapterPostFreeze.

theory Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze.

import HAETAE_Params.
import HAETAE_Algebra.
import HAETAE_Scheme.

(* This stateful source freezes the eight checked-parent inputs into module
   globals and materializes the already-proved mathematical witnesses.  It is
   a partial-correctness bridge only: no losslessness, retry termination,
   public-key distribution, HAETAE.kg equality, or API equality is claimed. *)
module CheckedMode2PublicKeySource
    : Mode2FaithfulSecurityNMAViewAdapterPostFreeze.PublicKeySource = {
  var seedbuf_in : BArray128.t
  var mat_in : BArray32768.t
  var avec_in : BArray8192.t
  var s1_in : BArray8192.t
  var s2_in : BArray8192.t
  var bp_in : BArray8192.t
  var s1hatp_in : BArray8192.t
  var raw_seed_in : BArray32.t

  var sd_current : seed
  var a_current : polyveck
  var b1_current : polyveck
  var agen_current : matrix
  var sgen_current : poly list
  var eadj_current : polyveck
  var pk_current : pkey

  proc sample() : pkey = {
    var seedbuf0 : BArray128.t;
    var mat0 : BArray32768.t;
    var avec0 : BArray8192.t;
    var s10 : BArray8192.t;
    var s20 : BArray8192.t;
    var bp0 : BArray8192.t;
    var s1hat0 : BArray8192.t;
    var raw0 : BArray32.t;
    var counter : W64.t;
    var sampled_s20 : BArray8192.t;
    var pre_bp : BArray8192.t;

    seedbuf0 <- seedbuf_in;
    mat0 <- mat_in;
    avec0 <- avec_in;
    s10 <- s1_in;
    s20 <- s2_in;
    bp0 <- bp_in;
    s1hat0 <- s1hatp_in;
    raw0 <- raw_seed_in;

    (seedbuf0, mat0, avec0, s10, sampled_s20, counter,
     pre_bp, s1hat0, bp0, s20) <@
      TargetKeygenM23FinalizeComposition.CheckedMode2ParentM23Finalize.run
        (seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0, raw0);

    sd_current <-
      Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed
        raw0;
    a_current <-
      Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
        avec0;
    b1_current <-
      Mode2FaithfulSecurityExpandVecAPostFreeze.actual_mode2_expandveca
        bp0;
    agen_current <-
      Mode2FaithfulSecurityKeygenPaperLiftPostFreeze.actual_Agen mat0;
    sgen_current <-
      Mode2FaithfulSecurityKeygenPaperLiftPostFreeze.actual_sgen s10;
    eadj_current <-
      Mode2FaithfulSecurityKeygenPaperLiftPostFreeze.actual_eadj s20;
    pk_current <-
      Mode2FaithfulSecurityKeygenViewPostFreeze.faithful_mode2_public_key
        sd_current b1_current;
    return pk_current;
  }
}.

lemma checked_mode2_public_key_source_sample_ready
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (raw_seed0 : BArray32.t) :
  hoare [CheckedMode2PublicKeySource.sample :
    CheckedMode2PublicKeySource.seedbuf_in = seedbuf0 /\
    CheckedMode2PublicKeySource.mat_in = mat0 /\
    CheckedMode2PublicKeySource.avec_in = avec0 /\
    CheckedMode2PublicKeySource.s1_in = s10 /\
    CheckedMode2PublicKeySource.s2_in = s20 /\
    CheckedMode2PublicKeySource.bp_in = bp0 /\
    CheckedMode2PublicKeySource.s1hatp_in = s1hat0 /\
    CheckedMode2PublicKeySource.raw_seed_in = raw_seed0
    ==>
    res = CheckedMode2PublicKeySource.pk_current /\
    Mode2FaithfulSecurityNMAViewAdapterPostFreeze.faithful_mode2_nma_ready
      CheckedMode2PublicKeySource.pk_current
      CheckedMode2PublicKeySource.sd_current
      CheckedMode2PublicKeySource.a_current
      CheckedMode2PublicKeySource.b1_current
      CheckedMode2PublicKeySource.agen_current
      CheckedMode2PublicKeySource.sgen_current
      CheckedMode2PublicKeySource.eadj_current /\
    CheckedMode2PublicKeySource.sd_current =
      Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed
        raw_seed0 /\
    CheckedMode2PublicKeySource.pk_current =
      Mode2FaithfulSecurityKeygenViewPostFreeze.faithful_mode2_public_key
        CheckedMode2PublicKeySource.sd_current
        CheckedMode2PublicKeySource.b1_current].
proof.
proc.
wp.
call
  (Mode2FaithfulSecurityNMAViewAdapterPostFreeze
    .checked_mode2_parent_m23_finalize_faithful_mode2_nma_ready
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 raw_seed0).
auto => /> result
  [pk sd a b1 Agen sgen eadj
    [hready [hsd [ha [hb1 [hAgen [hsgen [headj hpk]]]]]]]].
qed.

section CheckedSourceNMAExact.

declare module H <: SIG.Oracle
  {-SIG.UF_NMA,
   -Mode2FaithfulSecurityNMAViewAdapterPostFreeze.DirectPublicOnlyUFNMA,
   -CheckedMode2PublicKeySource}.
declare module A <: SIG.NMA_Adversary
  {-H, -SIG.UF_NMA,
   -Mode2FaithfulSecurityNMAViewAdapterPostFreeze.DirectPublicOnlyUFNMA,
   -CheckedMode2PublicKeySource}.

lemma checked_source_nma_wrapper_direct_exact &m :
  Pr[SIG.UF_NMA(
       H,
       Mode2FaithfulSecurityNMAViewAdapterPostFreeze
         .NMAViewScheme(CheckedMode2PublicKeySource),
       A).main() @ &m : res] =
  Pr[Mode2FaithfulSecurityNMAViewAdapterPostFreeze
       .DirectPublicOnlyUFNMA(H, CheckedMode2PublicKeySource, A).main()
       @ &m : res].
proof.
exact
  (Mode2FaithfulSecurityNMAViewAdapterPostFreeze
    .public_only_nma_wrapper_direct_exact
    H CheckedMode2PublicKeySource A &m).
qed.

end section CheckedSourceNMAExact.

end Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze.
