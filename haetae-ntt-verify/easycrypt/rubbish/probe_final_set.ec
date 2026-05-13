require import AllCore IntDiv CoreMap List Distr Ring StdOrder BitEncoding.
require import Array256.
require import GFq Rq.
require import NTT_Fq.

import Zq IntOrder BitReverse.

theory ProbeFinalSet.

op final_mont_array (p : coeff Array256.t) (j : int) : coeff Array256.t =
  Array256.init (fun i => if 0 <= i < j then p.[i] * NTT_Fq.R else p.[i]).

lemma final_mont_array_setE p j :
  0 <= j < 256 =>
  (final_mont_array p j).[j <- p.[j] * NTT_Fq.scale255 * NTT_Fq.R] =
  final_mont_array (p.[j <- p.[j] * NTT_Fq.scale255]) (j + 1).
proof.
move=> hj.
apply/Array256.ext_eq => i hi.
rewrite !Array256.get_set_if /final_mont_array !initiE //=.
case: (i = j) => hij.
+ rewrite hij.
  have hjj : 0 <= j < j + 1 by smt().
  rewrite hjj /=.
  rewrite !Array256.get_set_if /=.
  have -> : 0 <= j < 256 by smt().
  rewrite /=.
  trivial.
rewrite !Array256.get_set_if /=.
rewrite hij /=.
have hsame : (0 <= i < j + 1) = (0 <= i < j) by smt().
rewrite hsame.
by smt().
qed.

end ProbeFinalSet.
