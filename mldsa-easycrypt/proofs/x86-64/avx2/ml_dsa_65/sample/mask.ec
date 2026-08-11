require import AllCore List.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq.

require import Array64 Array256 Array1280.

(* Equiv between the spec ExpandMask.sample and the Jasmin sample____mask.
   Both take a 64-byte seed and an integer domain separator / kappa counter.
   The Jasmin function samples lvec polynomials using domain separators
   [kappa, kappa+1, ..., kappa+lvec-1] and returns the updated domain separator.
   Note: the spec's kappa increment (kappa <- kappa + lvec) is done in the
   outer loop, not inside ExpandMask.sample; the Jasmin increments internally
   and returns the new value. *)
lemma mask_correct _seed _dom :
    equiv [ ExpandMask.sample ~ M.sample____mask :
        arg{1}.`1 = Bytes64.of_list (to_list _seed)
     /\ arg{1}.`2 = W16.to_uint _dom
     /\ arg{2}.`1 = _seed
     /\ arg{2}.`2 = _dom
        ==>
        lifts_wpolylvec (lvec_unflatten256 res{2}.`1) = res{1}
     /\ wpolylvec_srng (lvec_unflatten256 res{2}.`1) (gamma1-1) gamma1
     /\ W16.to_uint res{2}.`2 = W16.to_uint _dom + lvec
    ].
proc.
admitted. (* expand mask (y) *)
