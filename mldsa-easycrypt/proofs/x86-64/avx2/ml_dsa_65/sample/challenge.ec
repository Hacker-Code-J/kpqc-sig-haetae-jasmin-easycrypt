require import AllCore List.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq.

require import Array48 Array256.

(* Equiv between the spec SampleInBall (with concrete MLDSA_XOF_SIB) and the
   Jasmin sample____challenge. The seed is the 48-byte commitment hash.

   Post also includes wpoly_srng 1 1 — sampleInBall emits a polynomial whose
   coefficients are in {-1, 0, 1} (with exactly tau nonzero entries), so the
   signed range is tight at [-1, 1]. *)
lemma sample_challenge_correct :
    equiv [ SampleInBall(MLDSA_XOF_SIB).sample ~ M.sample____challenge :
       arg{1} = BytesCT.of_list (to_list arg{2}.`2)
       ==>
       lifts_wpoly res{2} = res{1}.`1 /\
       wpoly_srng 1 1 res{2}
    ].
proc.
admitted. (* sample challenge *)
