require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import Fq KeygenM23FinalizeSemantics
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.

theory Mode2FaithfulSecurityAcceptedContextClassTraceFeasibilityPostFreeze.

(* Context validity alone cannot remove any of the six scalar final-s2
   classes.  This is a limitation result, not a reachability statement for an
   accepted KeyGen execution.  A useful accepted-context optimization still
   needs a separate theorem relating the singular-score guard to an ordered
   row class-trace domain. *)

op context_class_witness_int (cls : int) : int =
  if cls = 0 then 0
  else if cls = 1 then -1
  else if cls = 2 then 4
  else if cls = 3 then 1
  else if cls = 4 then 2
  else 3.

op context_class_witness_b (cls : int) : W32.t =
  W32.of_int (context_class_witness_int cls).

op context_class_witness_a : W32.t = W32.zero.

lemma context_class_witness_int_range cls :
  0 <= cls <= 5 =>
  -1 <= context_class_witness_int cls <= 4.
proof.
rewrite /context_class_witness_int.
smt().
qed.

lemma context_class_witness_sint cls :
  0 <= cls <= 5 =>
  W32.to_sint (context_class_witness_b cls) =
    context_class_witness_int cls.
proof.
move=> hclass.
have hrange := context_class_witness_int_range cls hclass.
rewrite /context_class_witness_b.
apply W32.to_sintK_small.
smt().
qed.

lemma context_class_witness_valid cls :
  0 <= cls <= 5 =>
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.context_valid
    (context_class_witness_b cls) context_class_witness_a.
proof.
move=> hclass.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.context_valid
  /Fq.bw32 /context_class_witness_a W32.to_uint0
  (context_class_witness_sint cls hclass)
  /KeygenM23FinalizeSemantics.q.
have hrange := context_class_witness_int_range cls hclass.
smt().
qed.

lemma context_class_witness_index cls :
  0 <= cls <= 5 =>
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_class_index
      (context_class_witness_b cls) context_class_witness_a = cls.
proof.
move=> hclass.
have hsint := context_class_witness_sint cls hclass.
rewrite
  /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
    .ideal_final_s2_class_index
  /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.rho
  /context_class_witness_a W32.to_uint0 hsint
  /KeygenM23FinalizeSemantics.q
  /context_class_witness_int.
case (cls = 0) => h0; first smt(@IntDiv).
case (cls = 1) => h1; first smt(@IntDiv).
case (cls = 2) => h2; first smt(@IntDiv).
case (cls = 3) => h3; first smt(@IntDiv).
case (cls = 4) => h4; first smt(@IntDiv).
smt(@IntDiv).
qed.

lemma every_scalar_class_has_a_valid_context cls :
  0 <= cls <= 5 =>
  exists b a,
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.context_valid b a /\
    Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
      .ideal_final_s2_class_index b a = cls.
proof.
move=> hclass.
exists (context_class_witness_b cls) context_class_witness_a.
split.
+ exact (context_class_witness_valid cls hclass).
+ exact (context_class_witness_index cls hclass).
qed.

end Mode2FaithfulSecurityAcceptedContextClassTraceFeasibilityPostFreeze.
