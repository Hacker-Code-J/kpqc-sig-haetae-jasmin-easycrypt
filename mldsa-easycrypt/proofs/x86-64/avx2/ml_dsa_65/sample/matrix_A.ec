require import AllCore List (* IntDiv RealExp StdBigop *).

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.
(* from JazzEC require import Array32. *)

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq.

(* require import ArrayExtra JWord_extra EclibExtra JWordList. *)

require import Array32 Array128 Array256 Array1952 Array4032 Array7680.

phoare matrix_A_correct _rho :
    [ M.sample____matrix_A : arg = _rho ==>
        liftu_wpolymat (mat_unflatten256 res) = expandA (Bytes32.of_list (to_list _rho))
     /\ wpolymat_urng (mat_unflatten256 res) q] = 1%r.
admitted. (* matrixA sampling *)
