require import AllCore Real StdOrder.
require import Sig_ROM HAETAE_Scheme HAETAE_Reductions HAETAE_Assumptions.

theory HAETAE_GameHops.

import HAETAE_Scheme.
import HAETAE_Reductions.
import HAETAE_Assumptions.
import RealOrder.

section NoSigningEmbedding.

declare module H0 <: SIG.Oracle {-SIG.EUF_CMA}.
declare module N0 <: SIG.NMA_Adversary {-H0, -HAETAE, -SIG.EUF_CMA}.

lemma euf_cma_no_signing_exact &m :
  Pr[SIG.EUF_CMA(H0, HAETAE, SIG.NMA_As_CMA(N0)).main() @ &m : res] =
  Pr[SIG.UF_NMA(H0, HAETAE, N0).main() @ &m : res].
proof.
by apply (SIG.nma_as_cma_exact H0 HAETAE N0 &m).
qed.

end section NoSigningEmbedding.

section.

declare module H <: SIG.Oracle.
declare module A <: SIG.Adversary {-H, -HAETAE}.
declare module N <: SIG.NMA_Adversary {-H, -HAETAE}.
declare module Bmlwe <: MLWE_Reduction.
declare module Bbimodal <: BimodalSelfTargetMSIS_Reduction.
declare module Bsis <: ModuleSIS_Reduction.

lemma euf_cma_game_hop_bound &m :
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
  Pr[SIG.EUF_CMA(H, HAETAE, A).main() @ &m : res] <=
    (Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
      (Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
        bimodal_to_msis_reduction_loss_term)) +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term).
proof.
move=> fs_hop nma_hop bimodal_hop.
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
  (Pr[SIG.UF_NMA(H, HAETAE, N).main() @ &m : res] +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term))).
+ by apply fs_hop.
apply ler_add.
+ by apply h_nma_msis.
+ by rewrite lerr.
qed.

lemma euf_cma_concrete_bound &m :
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
have h_chain := euf_cma_game_hop_bound &m fs_hop nma_hop bimodal_hop.
rewrite haetae_euf_bound_groupedE.
apply (ler_trans
  ((Pr[MLWE_Game(Bmlwe).main() @ &m : res] +
      (Pr[ModuleSIS_Game(Bsis).main() @ &m : res] +
        bimodal_to_msis_reduction_loss_term)) +
    (fs_with_aborts_reprogramming_term +
      fs_with_aborts_min_entropy_term))).
+ by apply h_chain.
apply ler_add.
+ apply ler_add.
  + by apply mlwe_bound.
  apply ler_add.
  + by apply msis_bound.
  + by rewrite lerr.
+ by rewrite lerr.
qed.

end section.

end HAETAE_GameHops.
