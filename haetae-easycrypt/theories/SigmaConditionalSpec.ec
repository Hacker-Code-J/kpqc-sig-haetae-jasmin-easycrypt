require import AllCore IntDiv Distr DInterval DBool.
from Jasmin require import JModel_x86.
require import SigmaRawNoiseSpec SigmaRejection48Bridge SigmaNoise72Bridge
  SigmaCDT83Patch CDTDistributionBridge Rejection48Spec SigmaJointSpec HalfGaussianSpec.
import HalfGaussianSpec.

op sc_accepted (r : int * bool) : bool = r.`2.
op sc_output (r : int * bool) : int = r.`1.

(* Exact distribution of the previously verified implementation observer.
   The actual sampler connection is a separate checked probability law. *)
op [opaque] sc_actual_pair (p : BArray26.t) : (int * bool) distr =
  dlet (dinter 0 (cdt83_modulus - 1)) (fun u =>
    dlet sr_noise_uniform (fun y =>
      let q = sigma_noise72_patch (sj_cdt83_patch p u) y in
      dmap rejection48_uniform (fun v =>
        (W64.to_uint (sigma_rejection48_rounded q),
          rejection48_word (W64.of_int v) (sigma_rejection48_threshold q)
            (sigma_rejection48_rounded q) = W64.one)))).

(* Independent reference retains the full infinite Gaussian support and
   the unbounded mathematical rounding of the preceding joint theorem. *)
op [opaque] sc_ideal_pair : (int * bool) distr =
  dlet hg16_distr (fun x =>
    dlet sr_noise_uniform (fun y =>
      dmap (Biased.dbiased (sj_acceptance x y))
        (fun b => (sj_round x y, b)))).

op [opaque] sc_actual_conditioned (p : BArray26.t) : int distr =
  dmap (dcond (sc_actual_pair p) sc_accepted) sc_output.

op [opaque] sc_ideal_conditioned : int distr =
  dmap (dcond sc_ideal_pair sc_accepted) sc_output.
