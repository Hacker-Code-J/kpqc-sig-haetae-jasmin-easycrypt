require import AllCore Distr StdOrder.
from Jasmin require import JModel_x86.
require import BArray26 SamplerTarget SigmaSpec SigmaCorrectness
  HardenedHyperballTarget HardenedSignerTarget GaussianUniformBytes
  GaussianRetryInputs SigmaConditionalSpec GaussianAcceptanceActual.
import RealOrder.

module GAPHyperball = HardenedHyperballTarget.M.
module GAPSigner = HardenedSignerTarget.M(HardenedSignerTarget.Syscall).

lemma gap_hyperball_sigma_equiv :
  equiv [GAPHyperball.__sample_gauss_sigma76_regs ~ SamplerTarget.M.__sample_gauss_sigma76_regs :
    ={randp} ==> ={res}].
proof. proc; inline *; sim. qed.

lemma gap_signer_sigma_equiv :
  equiv [GAPSigner.__sample_gauss_sigma76_regs ~ SamplerTarget.M.__sample_gauss_sigma76_regs :
    ={randp} ==> ={res}].
proof. proc; inline *; sim. qed.

lemma gap_hyperball_sigma_total (p : BArray26.t) :
  phoare [GAPHyperball.__sample_gauss_sigma76_regs : randp=p ==> res=sigma76_spec p] = 1%r.
proof. by conseq gap_hyperball_sigma_equiv (sigma76_regs_total_correct p) => /#. qed.

lemma gap_signer_sigma_total (p : BArray26.t) :
  phoare [GAPSigner.__sample_gauss_sigma76_regs : randp=p ==> res=sigma76_spec p] = 1%r.
proof. by conseq gap_signer_sigma_equiv (sigma76_regs_total_correct p) => /#. qed.

(* These experiments supply a fresh, fully uniform 26-byte array to the
   actual production helper. No property of a concrete SHAKE seed is assumed. *)
module GaussianAcceptanceProduction = {
  proc hyperball() : int * bool = {
    var bytes : BArray26.t;
    var r : W64.t * W64.t * W64.t * W64.t;
    bytes <$ gbc_candidate;
    r <@ GAPHyperball.__sample_gauss_sigma76_regs(bytes);
    return (W64.to_uint r.`1, r.`4=W64.one);
  }
  proc signer() : int * bool = {
    var bytes : BArray26.t;
    var r : W64.t * W64.t * W64.t * W64.t;
    bytes <$ gbc_candidate;
    r <@ GAPSigner.__sample_gauss_sigma76_regs(bytes);
    return (W64.to_uint r.`1, r.`4=W64.one);
  }
}.

module GaussianAcceptanceByteObserver = {
  proc sample() : int * bool = {
    var bytes : BArray26.t;
    bytes <$ gbc_candidate;
    return gr_candidate_observer bytes;
  }
}.

lemma gap_hyperball_observer_equiv :
  equiv [GaussianAcceptanceProduction.hyperball ~ GaussianAcceptanceByteObserver.sample :
    true ==> ={res}].
proof.
  proc; wp; ecall{1} (gap_hyperball_sigma_total bytes{1}).
  rnd; skip; auto => />; rewrite /gr_candidate_observer.
qed.

lemma gap_signer_observer_equiv :
  equiv [GaussianAcceptanceProduction.signer ~ GaussianAcceptanceByteObserver.sample :
    true ==> ={res}].
proof.
  proc; wp; ecall{1} (gap_signer_sigma_total bytes{1}).
  rnd; skip; auto => />; rewrite /gr_candidate_observer.
qed.

lemma gap_observer_pair_law (p : BArray26.t) (event : int * bool -> bool) &m :
  Pr[GaussianAcceptanceByteObserver.sample() @ &m : event res] =
    mu (sc_actual_pair p) event.
proof.
  byphoare (_ : true ==> event res) => //.
  proc; rnd; skip; auto => />.
  by rewrite -(gbc_candidate_observer_law p) /gbc_candidate /BArray26.darray !dmapE /(\o).
qed.

lemma gap_hyperball_pair_law (p : BArray26.t) (event : int * bool -> bool) &m :
  Pr[GaussianAcceptanceProduction.hyperball() @ &m : event res] =
    mu (sc_actual_pair p) event.
proof.
  rewrite -(gap_observer_pair_law p event &m).
  by byequiv gap_hyperball_observer_equiv.
qed.

lemma gap_signer_pair_law (p : BArray26.t) (event : int * bool -> bool) &m :
  Pr[GaussianAcceptanceProduction.signer() @ &m : event res] =
    mu (sc_actual_pair p) event.
proof.
  rewrite -(gap_observer_pair_law p event &m).
  by byequiv gap_signer_observer_equiv.
qed.

lemma gap_hyperball_rejection &m :
  Pr[GaussianAcceptanceProduction.hyperball() @ &m : !res.`2] < 1%r/20%r.
proof.
  rewrite (gap_hyperball_pair_law (witness<:BArray26.t>) (predC sc_accepted) &m).
  exact (gaa_rejection_upper (witness<:BArray26.t>) &m).
qed.

lemma gap_signer_rejection &m :
  Pr[GaussianAcceptanceProduction.signer() @ &m : !res.`2] < 1%r/20%r.
proof.
  rewrite (gap_signer_pair_law (witness<:BArray26.t>) (predC sc_accepted) &m).
  exact (gaa_rejection_upper (witness<:BArray26.t>) &m).
qed.
