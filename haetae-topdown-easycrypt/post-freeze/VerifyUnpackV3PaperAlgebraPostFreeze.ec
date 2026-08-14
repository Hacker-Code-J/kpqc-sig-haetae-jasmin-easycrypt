require import AllCore IntDiv Ring.

require import GFq KeygenM23FinalizeSemantics KgFaithfulAugmentedModel.

theory VerifyUnpackV3PaperAlgebraPostFreeze.

import Zq.

op v3_pre_ntt_head (a b1 : int) : int =
  2 * a - 4 * b1.

op v3_paper_head_modq (a b1 row coeff : int) : coeff =
  incoeff
    (KgFaithfulAugmentedModel.faithful_head_coeff
      (fun _ _ => a) (fun _ _ => b1) row coeff).

op v3_assembled_head_modq (a b1 : int) : coeff =
  incoeff (v3_pre_ntt_head a b1).

lemma v3_pre_ntt_head_formula a b1 :
  2 * (a - 2 * b1) = v3_pre_ntt_head a b1.
proof. rewrite /v3_pre_ntt_head; ring. qed.

lemma v3_pre_ntt_head_bound17 a b1 :
  0 <= a < 64513 =>
  0 <= b1 < 32768 =>
  - (2 ^ 17) <= v3_pre_ntt_head a b1 < 2 ^ 17.
proof. rewrite /v3_pre_ntt_head; smt(). qed.

lemma v3_paper_qj_invisible_modq a b1 row coeff :
  v3_paper_head_modq a b1 row coeff =
  v3_assembled_head_modq a b1.
proof.
rewrite /v3_paper_head_modq /v3_assembled_head_modq /v3_pre_ntt_head
        /KgFaithfulAugmentedModel.faithful_head_coeff
        /KgFaithfulAugmentedModel.faithful_qj_coeff
        /KgFaithfulAugmentedModel.faithful_j_coeff.
apply/eq_incoeff.
rewrite /GFq.q /KeygenM23FinalizeSemantics.q /=.
case (row = 0 /\ coeff = 0); smt().
qed.

end VerifyUnpackV3PaperAlgebraPostFreeze.
