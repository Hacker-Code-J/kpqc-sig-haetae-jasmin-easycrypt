require import AllCore List (* IntDiv RealExp StdBigop *).

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.
(* from JazzEC require import Array32. *)

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq.

(* require import ArrayExtra JWord_extra EclibExtra JWordList. *)

require import Array32 Array64 Array128 Array256 Array1280 Array1952 Array4032 Array7680.

phoare error_vectors_correct _rho :
    [ M.sample____error_vectors : arg = _rho ==>
        lifts_wpolylvec (lvec_unflatten256 res.`1) = (expandS (Bytes64.of_list (to_list _rho))).`1
     /\ wpolylvec_srng (lvec_unflatten256 res.`1) Eta Eta
     /\ lifts_wpolykvec (kvec_unflatten256 res.`2) = (expandS (Bytes64.of_list (to_list _rho))).`2
     /\ wpolykvec_srng (kvec_unflatten256 res.`2) Eta Eta
    ] = 1%r.
admitted. (* sample error vectors *)
