require import AllCore Real Distr StdOrder.
require import Sig_ROM HAETAE_Scheme HAETAE_Algebra HAETAE_Distributions.
require import HAETAE_Reductions HAETAE_Assumptions.
require import HAETAE_Rejection.
require import HAETAE_Transcript HAETAE_ROM_Programming.
require import HAETAE_HopGames.

theory HAETAE_Security.

import HAETAE_Algebra.
import HAETAE_Distributions.
import HAETAE_Reductions.
import HAETAE_Assumptions.
import HAETAE_Rejection.
import HAETAE_Transcript.
import HAETAE_ROM_Programming.
import HAETAE_HopGames.
import HAETAE_Scheme.
import RealOrder.

op correctness_obligation =
  forall (sd : seed) (coins : random_coins)
         (m : message) (ctx : context),
    verify_internal haetae_mode (keygen_internal haetae_mode sd).`1 m ctx
      (sign_internal haetae_mode
        (keygen_internal haetae_mode sd).`2 m ctx coins).

lemma correctness_obligation_holds : correctness_obligation.
proof.
rewrite /correctness_obligation /keygen_internal.
move=> sd coins m ctx.
by apply verify_internal_sign_internal.
qed.

section.

declare module H <: SIG.Oracle.
declare module A <: SIG.CORR_ADV {-H, -HAETAE}.

lemma correctness_perfect &m :
  Pr[SIG.Correctness(H, HAETAE, A).main() @ &m : res] = 0%r.
proof.
byphoare => //.
hoare.
proc.
inline *.
wp.
call(_: true).
wp.
call(_: true).
wp.
call(_: true).
wp.
rnd.
wp.
call(_: true ==> true).
+ by conseq (: _ ==> true).
wp.
call(_: true).
wp.
rnd.
call(_: true).
auto => /> sd _ result coins _.
move=> result0.
rewrite /keygen_internal /verify_internal /=.
split.
+ by apply valid_signature_sign_internal.
by apply verify_norm_ok_current.
qed.

end section.

section NoSigningSecurity.

declare module H <: SIG.Oracle {-SIG.EUF_CMA}.
declare module N <: SIG.NMA_Adversary {-H, -HAETAE, -SIG.EUF_CMA}.
declare module Bmlwe <: MLWE_Reduction.
declare module Bbimodal <: BimodalSelfTargetMSIS_Reduction.
declare module Bsis <: ModuleSIS_Reduction.

lemma euf_cma_security_no_signing &m :
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] <=
    Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
    bimodal_to_msis_reduction_loss_term =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(Bsis).main() @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, SIG.NMA_As_CMA(N)).main() @ &m : res] <=
    haetae_euf_bound.
proof.
move=> nma_hop bimodal_hop mlwe_bound msis_bound.
rewrite (SIG.nma_as_cma_exact H HAETAE N &m).
rewrite haetae_euf_bound_rejection_groupedE.
have h_nma_msis :
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    (Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
      bimodal_to_msis_reduction_loss_term).
  apply (ler_trans
    (Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
      Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res])).
  + by apply nma_hop.
  apply ler_add.
  + by rewrite lerr.
  + by apply bimodal_hop.
apply (ler_trans
  (Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    (Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
      bimodal_to_msis_reduction_loss_term))).
+ by apply h_nma_msis.
apply (ler_trans
  (mlwe_hardness_term +
    (module_sis_hardness_term + bimodal_to_msis_reduction_loss_term))).
+ apply ler_add.
  + by apply mlwe_bound.
  apply ler_add.
  + by apply msis_bound.
  + by rewrite lerr.
by rewrite ler_addl; apply (rejection_bound_parts_nonnegative
                            rejection_sampling_bound_obligation_holds).
qed.

end section NoSigningSecurity.

section.

declare module H <: SIG.Oracle.
declare module A <: SIG.Adversary {-H, -HAETAE}.
declare module N <: SIG.NMA_Adversary {-H, -HAETAE}.
declare module Bmlwe <: MLWE_Reduction.
declare module Bbimodal <: BimodalSelfTargetMSIS_Reduction.
declare module Bsis <: ModuleSIS_Reduction.

lemma euf_cma_security &m :
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term) =>
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] <=
    Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
    bimodal_to_msis_reduction_loss_term =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(Bsis).main() @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <= haetae_euf_bound.
proof.
move=> fs_hop nma_hop bimodal_hop mlwe_bound msis_bound.
have h_nma_msis :
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    (Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
      bimodal_to_msis_reduction_loss_term).
  apply (ler_trans
    (Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
      Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res])).
  + by apply nma_hop.
  apply ler_add.
  + by rewrite lerr.
  + by apply bimodal_hop.
rewrite haetae_euf_bound_groupedE.
apply (ler_trans
  ((Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
      (Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
        bimodal_to_msis_reduction_loss_term)) +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term))).
+ apply (ler_trans
    (Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
      (fs_with_aborts_reprogramming_term +
        fs_with_aborts_min_entropy_term))).
  + by apply fs_hop.
  apply ler_add.
  + by apply h_nma_msis.
  + by rewrite lerr.
apply ler_add.
+ apply ler_add.
  + by apply mlwe_bound.
  apply ler_add.
  + by apply msis_bound.
  + by rewrite lerr.
+ by rewrite lerr.
qed.

lemma euf_cma_security_with_hop_interfaces &m :
  fs_with_aborts_interfaces_ready haetae_mode =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term) =>
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] <=
    Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
    bimodal_to_msis_reduction_loss_term =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(Bsis).main() @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <= haetae_euf_bound.
proof.
move=> _ fs_hop nma_hop bimodal_hop mlwe_bound msis_bound.
by apply (euf_cma_security &m fs_hop nma_hop bimodal_hop mlwe_bound
          msis_bound).
qed.

end section.

section FullReductionWithSimulatorHop.

declare module H <: SIG.Oracle {-SIG.EUF_CMA, -EUF_CMA_SimulatedSign,
                                 -RealSigningSimulator}.
declare module A <: SIG.Adversary {-H, -HAETAE, -SIG.EUF_CMA,
                                    -EUF_CMA_SimulatedSign,
                                    -RealSigningSimulator}.
declare module N <: SIG.NMA_Adversary {-H, -HAETAE}.
declare module Bmlwe <: MLWE_Reduction.
declare module Bbimodal <: BimodalSelfTargetMSIS_Reduction.
declare module Bsis <: ModuleSIS_Reduction.

lemma euf_cma_security_from_simulated_hop &m :
  fs_with_aborts_interfaces_ready haetae_mode =>
  Pr[EUF_CMA_SimulatedSign(H, HAETAE, A, RealSigningSimulator(HAETAE)).main()
       @ &m : res] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term) =>
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] <=
    Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
    bimodal_to_msis_reduction_loss_term =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(Bsis).main() @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <= haetae_euf_bound.
proof.
move=> iface sim_hop nma_hop bimodal_hop mlwe_bound msis_bound.
rewrite (real_signing_simulator_exact H HAETAE A &m).
have h_nma_msis :
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    (Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
      bimodal_to_msis_reduction_loss_term).
  apply (ler_trans
    (Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
     Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res])).
  + by apply nma_hop.
  apply ler_add.
  + by rewrite lerr.
  + by apply bimodal_hop.
rewrite haetae_euf_bound_groupedE.
apply (ler_trans
  ((Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
      (Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
        bimodal_to_msis_reduction_loss_term)) +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term))).
+ apply (ler_trans
    (Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
      (fs_with_aborts_reprogramming_term +
        fs_with_aborts_min_entropy_term))).
  + by apply sim_hop.
  apply ler_add.
  + by apply h_nma_msis.
  + by rewrite lerr.
apply ler_add.
+ apply ler_add.
  + by apply mlwe_bound.
  apply ler_add.
  + by apply msis_bound.
  + by rewrite lerr.
+ by rewrite lerr.
qed.

lemma euf_cma_security_from_explicit_boundaries &m :
  Pr[EUF_CMA_SimulatedSign(H, HAETAE, A, RealSigningSimulator(HAETAE)).main()
       @ &m : res] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term) =>
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] <=
    Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
    bimodal_to_msis_reduction_loss_term =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(Bsis).main() @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <= haetae_euf_bound.
proof.
move=> sim_hop nma_hop bimodal_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_simulated_hop &m).
+ by apply fs_with_aborts_interfaces_ready_holds.
+ by apply sim_hop.
+ by apply nma_hop.
+ by apply bimodal_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

end section FullReductionWithSimulatorHop.

section FullReductionWithROMTranscriptHop.

declare module H <: SIG.Oracle {-SIG.EUF_CMA,
                                 -EUF_CMA_InternalTranscriptSign,
                                 -EUF_CMA_ROMInternalTranscriptSign}.
declare module A <: SIG.Adversary {-H, -HAETAE, -SIG.EUF_CMA,
                                    -EUF_CMA_InternalTranscriptSign,
                                    -EUF_CMA_ROMInternalTranscriptSign}.
declare module N <: SIG.NMA_Adversary {-H, -HAETAE}.
declare module Bmlwe <: MLWE_Reduction.
declare module Bbimodal <: BimodalSelfTargetMSIS_Reduction.
declare module Bsis <: ModuleSIS_Reduction.

lemma euf_cma_security_from_rom_internal_transcript_hop &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m : res] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term) =>
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] <=
    Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
    bimodal_to_msis_reduction_loss_term =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(Bsis).main() @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <= haetae_euf_bound.
proof.
move=> rom_hop nma_hop bimodal_hop mlwe_bound msis_bound.
apply (euf_cma_security H A N Bmlwe Bbimodal Bsis &m).
+ rewrite (haetae_rom_internal_transcript_erasure_exact H A &m).
  by apply rom_hop.
+ by apply nma_hop.
+ by apply bimodal_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma rom_internal_transcript_hop_from_clear_site_reduction &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
      res /\
      transcript_log_signature_programming_sites_clear haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.transcripts] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] =>
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m : res] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term).
proof.
move=> clear_reduction.
have split_success :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m : res] =
    Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
      res /\
      transcript_log_signature_programming_sites_clear haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.transcripts] +
    Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
      res /\
      ! transcript_log_signature_programming_sites_clear haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.transcripts].
  by rewrite Pr[mu_split (transcript_log_signature_programming_sites_clear
                            haetae_mode
                            EUF_CMA_ROMInternalTranscriptSign.transcripts)].
rewrite split_success.
apply ler_add.
+ by apply clear_reduction.
by apply (rom_internal_transcript_bad_forgery_bound H A &m).
qed.

lemma rom_internal_transcript_hop_from_clear_site_counted_reduction &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
      res /\
      transcript_log_signature_programming_sites_clear haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.transcripts] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] =>
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m : res] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
    counted_rom_programming_loss_term.
proof.
move=> clear_reduction.
have split_success :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m : res] =
    Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
      res /\
      transcript_log_signature_programming_sites_clear haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.transcripts] +
    Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
      res /\
      ! transcript_log_signature_programming_sites_clear haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.transcripts].
  by rewrite Pr[mu_split (transcript_log_signature_programming_sites_clear
                            haetae_mode
                            EUF_CMA_ROMInternalTranscriptSign.transcripts)].
rewrite split_success.
apply ler_add.
+ by apply clear_reduction.
by apply (rom_internal_transcript_bad_forgery_counted_bound H A &m).
qed.

end section FullReductionWithROMTranscriptHop.

section MechanizedBimodalModuleSISLift.

declare module H <: SIG.Oracle {-SIG.EUF_CMA, -EUF_CMA_SimulatedSign,
                                 -RealSigningSimulator}.
declare module A <: SIG.Adversary {-H, -HAETAE, -SIG.EUF_CMA,
                                    -EUF_CMA_SimulatedSign,
                                    -RealSigningSimulator}.
declare module N <: SIG.NMA_Adversary {-H, -HAETAE}.
declare module Bmlwe <: MLWE_Reduction.
declare module Bbimodal <: BimodalSelfTargetMSIS_Reduction.

lemma bimodal_to_module_sis_reduction_bound &m :
  Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] <=
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] +
    bimodal_to_msis_reduction_loss_term.
proof.
rewrite (bimodal_msis_as_module_sis_exact Bbimodal &m).
rewrite bimodal_to_msis_reduction_loss_termE.
have -> :
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] + 0%r =
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] by ring.
by rewrite lerr.
qed.

lemma euf_cma_security_from_mechanized_boundaries &m :
  Pr[EUF_CMA_SimulatedSign(H, HAETAE, A, RealSigningSimulator(HAETAE)).main()
       @ &m : res] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term) =>
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <= haetae_euf_bound.
proof.
move=> sim_hop nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_simulated_hop
         H A N Bmlwe Bbimodal (BimodalMSIS_As_ModuleSIS(Bbimodal)) &m).
+ by apply fs_with_aborts_interfaces_ready_holds.
+ by apply sim_hop.
+ by apply nma_hop.
+ by apply bimodal_to_module_sis_reduction_bound.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

end section MechanizedBimodalModuleSISLift.

section MechanizedROMTranscriptBimodalLift.

declare module H <: SIG.Oracle {-SIG.EUF_CMA,
                                 -EUF_CMA_InternalTranscriptSign,
                                 -EUF_CMA_ROMInternalTranscriptSign}.
declare module A <: SIG.Adversary {-H, -HAETAE, -SIG.EUF_CMA,
                                    -EUF_CMA_InternalTranscriptSign,
                                    -EUF_CMA_ROMInternalTranscriptSign}.
declare module N <: SIG.NMA_Adversary {-H, -HAETAE}.
declare module Bmlwe <: MLWE_Reduction.
declare module Bbimodal <: BimodalSelfTargetMSIS_Reduction.

lemma euf_cma_security_from_rom_transcript_and_mechanized_bimodal &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m : res] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term) =>
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <= haetae_euf_bound.
proof.
move=> rom_hop nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_rom_internal_transcript_hop
         H A N Bmlwe Bbimodal (BimodalMSIS_As_ModuleSIS(Bbimodal)) &m).
+ by apply rom_hop.
+ by apply nma_hop.
+ by apply (bimodal_to_module_sis_reduction_bound Bbimodal &m).
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_rom_transcript_and_counted_bimodal &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m : res] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
    counted_rom_programming_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> rom_hop nma_hop mlwe_bound msis_bound.
rewrite (haetae_rom_internal_transcript_erasure_exact H A &m).
have h_nma_msis :
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    (Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
         @ &m : res] +
      bimodal_to_msis_reduction_loss_term).
  apply (ler_trans
    (Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
     Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res])).
  + by apply nma_hop.
  apply ler_add.
  + by rewrite lerr.
  + by apply (bimodal_to_module_sis_reduction_bound Bbimodal &m).
rewrite haetae_euf_counted_rom_bound_groupedE.
apply (ler_trans
  ((Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
      (Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
         @ &m : res] +
        bimodal_to_msis_reduction_loss_term)) +
    counted_rom_programming_loss_term)).
+ apply (ler_trans
    (Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
      counted_rom_programming_loss_term)).
  + by apply rom_hop.
  apply ler_add.
  + by apply h_nma_msis.
  + by rewrite lerr.
apply ler_add.
+ apply ler_add.
  + by apply mlwe_bound.
  apply ler_add.
  + by apply msis_bound.
  + by rewrite lerr.
+ by rewrite lerr.
qed.

lemma euf_cma_security_from_rom_clear_site_and_mechanized_bimodal &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
      res /\
      transcript_log_signature_programming_sites_clear haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.transcripts] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] =>
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <= haetae_euf_bound.
proof.
move=> clear_reduction nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_rom_transcript_and_mechanized_bimodal
         &m).
+ by apply (rom_internal_transcript_hop_from_clear_site_reduction
              H A N &m clear_reduction).
+ by apply nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_rom_clear_site_and_counted_bimodal &m :
  Pr[EUF_CMA_ROMInternalTranscriptSign(H, A).main() @ &m :
      res /\
      transcript_log_signature_programming_sites_clear haetae_mode
        EUF_CMA_ROMInternalTranscriptSign.transcripts] <=
    Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] =>
  Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> clear_reduction nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_rom_transcript_and_counted_bimodal
         &m).
+ by apply (rom_internal_transcript_hop_from_clear_site_counted_reduction
              H A N &m clear_reduction).
+ by apply nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

end section MechanizedROMTranscriptBimodalLift.

section MechanizedROMTranscriptConstructedNMALift.

declare module H <: SIG.Oracle {-SIG.EUF_CMA,
                                 -EUF_CMA_InternalTranscriptSign,
                                 -EUF_CMA_ROMInternalTranscriptSign,
                                 -ROMInternalTranscriptAsNMA,
                                 -ROMInternalTranscriptPublicSimAsNMA,
                                 -ROMInternalTranscriptPaperSimAsNMA,
                                 -ROMInternalTranscriptBudgetedPaperSimAsNMA,
                                 -ROMPaperSimSigningSampler,
                                 -RealSigningPaperSimSampler,
                                 -ROSigningAttemptPaperSimSampler,
                                 -HAETAERejectionPaperSimSampler,
                                 -ExactHyperballHAETAERejectionPaperSimSampler,
                                 -ExactHyperballPaperSimSampler,
                                 -ROExactHyperballPaperSimSampler}.
declare module A <: SIG.Adversary {-H, -HAETAE, -SIG.EUF_CMA,
                                    -EUF_CMA_InternalTranscriptSign,
                                    -EUF_CMA_ROMInternalTranscriptSign,
                                    -ROMInternalTranscriptAsNMA,
                                    -ROMInternalTranscriptPublicSimAsNMA,
                                    -ROMInternalTranscriptPaperSimAsNMA,
                                    -ROMInternalTranscriptBudgetedPaperSimAsNMA,
                                    -ROMPaperSimSigningSampler,
                                    -RealSigningPaperSimSampler,
                                    -ROSigningAttemptPaperSimSampler,
                                    -HAETAERejectionPaperSimSampler,
                                    -ExactHyperballHAETAERejectionPaperSimSampler,
                                    -ExactHyperballPaperSimSampler,
                                    -ROExactHyperballPaperSimSampler}.
declare module Samp <: PaperSimSigningSampler {-H, -A,
                                               -ROMInternalTranscriptPaperSimAsNMA}.
declare module Bmlwe <: MLWE_Reduction.
declare module Bbimodal <: BimodalSelfTargetMSIS_Reduction.

lemma euf_cma_security_from_structural_nma_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE, ROMInternalTranscriptAsNMA(A)).main()
       @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_rom_clear_site_and_counted_bimodal
         H A (ROMInternalTranscriptAsNMA(A)) Bmlwe Bbimodal &m).
+ by apply (rom_internal_transcript_clear_site_structural_nma_bound H A &m).
+ by apply nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_public_sim_nma_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE, ROMInternalTranscriptPublicSimAsNMA(A)).main()
       @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_structural_nma_and_counted_bimodal
         &m).
+ rewrite (rom_internal_nma_public_sim_exact H A &m).
  by apply nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_paper_sim_nma_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE, ROMInternalTranscriptPublicSimAsNMA(A)).main()
       @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA(A, Samp)).main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA(A, Samp)).main() @ &m : res] +
    rejection_sampling_loss_term <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> sampling_hop paper_nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_public_sim_nma_and_counted_bimodal
         &m).
+ apply (ler_trans
    (Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA(A, Samp)).main() @ &m : res] +
      rejection_sampling_loss_term)).
  + by apply (public_sim_to_paper_sim_nma_hop_from_sampling_hop
              H A Samp &m).
  + by apply paper_nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_rom_paper_sim_nma_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROMPaperSimSigningSampler(H))).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_public_sim_nma_and_counted_bimodal
         &m).
+ rewrite (rom_internal_nma_public_sim_rom_paper_sim_exact H A &m).
  by apply nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_real_signing_paper_sim_nma_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_structural_nma_and_counted_bimodal
         &m).
+ rewrite (rom_internal_nma_real_signing_paper_sim_exact H A &m).
  by apply nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_haetae_rejection_paper_sim_nma_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, HAETAERejectionPaperSimSampler(H))).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_real_signing_paper_sim_nma_and_counted_bimodal
         &m).
+ rewrite (rom_internal_nma_real_signing_haetae_rejection_paper_sim_exact
             H A &m).
  by apply nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma exact_hyperball_haetae_rejection_nma_bound_from_paper_sim &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballPaperSimSampler(H))).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballHAETAERejectionPaperSimSampler(H))).main()
       @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res].
proof.
move=> nma_hop.
rewrite (rom_internal_nma_exact_hyperball_rejection_paper_sim_no_fallback_exact
           H A &m).
by apply nma_hop.
qed.

lemma haetae_rejection_nma_bound_from_exact_hyperball_sampling_hop &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, HAETAERejectionPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballHAETAERejectionPaperSimSampler(H))).main()
       @ &m : res] + rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, HAETAERejectionPaperSimSampler(H))).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res].
proof.
move=> sampling_hop exact_nma_hop.
apply (ler_trans
  (Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballHAETAERejectionPaperSimSampler(H))).main()
       @ &m : res] + rejection_sampling_loss_term)).
+ by apply sampling_hop.
rewrite (rom_internal_nma_exact_hyperball_rejection_paper_sim_no_fallback_exact
           H A &m).
by apply exact_nma_hop.
qed.

lemma haetae_rejection_exact_hyperball_sampling_hop_from_real_signing_exact_hyperball_hop &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, HAETAERejectionPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballHAETAERejectionPaperSimSampler(H))).main()
       @ &m : res] + rejection_sampling_loss_term.
proof.
move=> real_exact_hop.
rewrite -(rom_internal_nma_real_signing_haetae_rejection_paper_sim_exact
            H A &m).
rewrite (rom_internal_nma_exact_hyperball_rejection_paper_sim_no_fallback_exact
           H A &m).
by apply real_exact_hop.
qed.

lemma haetae_rejection_ro_exact_hyperball_sampling_hop_from_real_signing_ro_exact_hyperball_hop &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, HAETAERejectionPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term.
proof.
move=> real_ro_exact_hop.
rewrite -(rom_internal_nma_real_signing_haetae_rejection_paper_sim_exact
            H A &m).
by apply real_ro_exact_hop.
qed.

lemma real_signing_ro_exact_hyperball_hop_from_ro_signing_attempt_hop &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term.
proof.
move=> ro_attempt_hop.
rewrite (rom_internal_nma_real_signing_ro_attempt_paper_sim_exact H A &m).
by apply ro_attempt_hop.
qed.

lemma real_signing_ro_exact_hyperball_hop_from_ro_signing_attempt_hop_loss
  &m (loss : real) :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    loss =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    loss.
proof.
move=> ro_attempt_hop.
rewrite (rom_internal_nma_real_signing_ro_attempt_paper_sim_exact H A &m).
by apply ro_attempt_hop.
qed.

lemma real_signing_ro_exact_hyperball_hop_from_budgeted_lifting &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] =>
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term.
proof.
move=> attempt_unbudgeted_to_budgeted exact_budgeted_to_unbudgeted
        sample_loss.
apply
  (real_signing_ro_exact_hyperball_hop_from_ro_signing_attempt_hop_loss
     &m (rom_signature_query_budget * rejection_sampling_loss_term)).
apply
  (rom_internal_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_budgeted_lifting
     H A &m).
+ by apply attempt_unbudgeted_to_budgeted.
+ by apply exact_budgeted_to_unbudgeted.
by apply sample_loss.
qed.

lemma haetae_rejection_ro_exact_hyperball_sampling_hop_from_budgeted_lifting
  &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] =>
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, HAETAERejectionPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term.
proof.
move=> attempt_unbudgeted_to_budgeted exact_budgeted_to_unbudgeted
        sample_loss.
rewrite -(rom_internal_nma_real_signing_haetae_rejection_paper_sim_exact
            H A &m).
by apply
  (real_signing_ro_exact_hyperball_hop_from_budgeted_lifting &m).
qed.

lemma euf_cma_security_from_exact_hyperball_paper_sim_bridge_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, HAETAERejectionPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballHAETAERejectionPaperSimSampler(H))).main()
       @ &m : res] =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballPaperSimSampler(H))).main() @ &m : res] <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> exact_bridge exact_nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_haetae_rejection_paper_sim_nma_and_counted_bimodal
         &m).
+ apply (ler_trans
    (Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballHAETAERejectionPaperSimSampler(H))).main()
       @ &m : res])).
  + by apply exact_bridge.
  + by apply (exact_hyperball_haetae_rejection_nma_bound_from_paper_sim &m).
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_exact_hyperball_sampling_hop_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, HAETAERejectionPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballHAETAERejectionPaperSimSampler(H))).main()
       @ &m : res] + rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> sampling_hop exact_nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_haetae_rejection_paper_sim_nma_and_counted_bimodal
         &m).
+ by apply (haetae_rejection_nma_bound_from_exact_hyperball_sampling_hop
              &m).
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_ro_exact_hyperball_sampling_hop_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> real_ro_exact_hop ro_exact_nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_haetae_rejection_paper_sim_nma_and_counted_bimodal
         &m).
+ apply (ler_trans
    (Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
      rejection_sampling_loss_term)).
  + by apply
      (haetae_rejection_ro_exact_hyperball_sampling_hop_from_real_signing_ro_exact_hyperball_hop
         &m).
  + by apply ro_exact_nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_ro_signing_attempt_to_ro_exact_hyperball_hop_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> ro_attempt_hop ro_exact_nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_ro_exact_hyperball_sampling_hop_and_counted_bimodal
         &m).
+ by apply
     (real_signing_ro_exact_hyperball_hop_from_ro_signing_attempt_hop &m).
+ by apply ro_exact_nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma real_signing_ro_exact_hyperball_hop_checked_from_loss_budget &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term.
proof.
apply (real_signing_ro_exact_hyperball_hop_from_ro_signing_attempt_hop &m).
by apply (rom_internal_nma_ro_signing_attempt_ro_exact_hyperball_loss_bound
            H A &m).
qed.

lemma real_signing_ro_exact_hyperball_hop_from_paper_sample_lifting &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term.
proof.
move=> sample_loss lifted_loss.
apply (real_signing_ro_exact_hyperball_hop_from_ro_signing_attempt_hop &m).
by apply
  (rom_internal_nma_ro_signing_attempt_ro_exact_hyperball_loss_from_paper_sample_lifting
     H A &m).
qed.

lemma euf_cma_security_from_paper_sample_lifting_and_counted_bimodal &m :
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> sample_loss lifted_loss ro_exact_nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_ro_exact_hyperball_sampling_hop_and_counted_bimodal
         &m).
+ by apply (real_signing_ro_exact_hyperball_hop_from_paper_sample_lifting &m).
+ by apply ro_exact_nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_budgeted_paper_sample_lifting_and_counted_bimodal
  &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROSigningAttemptPaperSimSampler(H))).main() @ &m : res] =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptBudgetedPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] =>
  structural_to_exact_hyperball_paper_sample_loss_obligation haetae_mode =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rom_signature_query_budget * rejection_sampling_loss_term <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> attempt_unbudgeted_to_budgeted exact_budgeted_to_unbudgeted
        sample_loss ro_exact_nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_haetae_rejection_paper_sim_nma_and_counted_bimodal
         &m).
+ apply (ler_trans
    (Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
      rom_signature_query_budget * rejection_sampling_loss_term)).
  + apply
      (haetae_rejection_ro_exact_hyperball_sampling_hop_from_budgeted_lifting
         &m).
    + by apply attempt_unbudgeted_to_budgeted.
    + by apply exact_budgeted_to_unbudgeted.
    by apply sample_loss.
  by apply ro_exact_nma_hop.
+ by apply mlwe_bound.
by apply msis_bound.
qed.

lemma euf_cma_security_from_checked_ro_sampling_hop_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ROExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> ro_exact_nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_ro_exact_hyperball_sampling_hop_and_counted_bimodal
         &m).
+ by apply (real_signing_ro_exact_hyperball_hop_checked_from_loss_budget &m).
+ by apply ro_exact_nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

lemma euf_cma_security_from_real_signing_exact_hyperball_hop_and_counted_bimodal &m :
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, RealSigningPaperSimSampler(H))).main() @ &m : res] <=
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term =>
  Pr[SIG.UF_NMA(H, HAETAE,
       ROMInternalTranscriptPaperSimAsNMA
         (A, ExactHyperballPaperSimSampler(H))).main() @ &m : res] +
    rejection_sampling_loss_term <=
    Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
    Pr[BimodalSelfTargetMSIS_Game(Bbimodal).main() @ &m : res] =>
  Pr[MLWE_Game(Bmlwe).main() @ &m : res] <= mlwe_hardness_term =>
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(Bbimodal)).main()
       @ &m : res] <= module_sis_hardness_term =>
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    haetae_euf_counted_rom_bound.
proof.
move=> real_exact_hop exact_nma_hop mlwe_bound msis_bound.
apply (euf_cma_security_from_exact_hyperball_sampling_hop_and_counted_bimodal
         &m).
+ by apply
     (haetae_rejection_exact_hyperball_sampling_hop_from_real_signing_exact_hyperball_hop
        &m).
+ by apply exact_nma_hop.
+ by apply mlwe_bound.
+ by apply msis_bound.
qed.

end section MechanizedROMTranscriptConstructedNMALift.

end HAETAE_Security.
