require import AllCore Distr List.
require import HAETAE_Params HAETAE_Algebra.

theory HAETAE_Assumptions.

import HAETAE_Params.
import HAETAE_Algebra.

type mlwe_instance.
type module_sis_instance = matrix * polyveck.
type module_sis_solution = polyvecl.
type bimodal_selftarget_msis_instance = module_sis_instance.
type bimodal_selftarget_msis_solution = module_sis_solution.

op [lossless] dmlwe_real : mode -> mlwe_instance distr.
op [lossless] dmlwe_random : mode -> mlwe_instance distr.
op [lossless] dmodule_sis_instance : mode -> module_sis_instance distr.
op [lossless] dbimodal_selftarget_msis_instance :
  mode -> bimodal_selftarget_msis_instance distr.

op module_sis_eval
   (md : mode) (x : module_sis_instance)
   (sol : module_sis_solution) : polyveck =
  polyveck_sub md (matrix_vec_mul md x.`1 sol) x.`2.

op module_sis_zero_instance (md : mode) : module_sis_instance =
  ([], polyveck_zero md).

op module_sis_solution_wf (md : mode) (sol : module_sis_solution) : bool =
  polyvecl_wf md sol.

op module_sis_valid
   (md : mode) (x : module_sis_instance)
   (sol : module_sis_solution) : bool =
  module_sis_solution_wf md sol /\
  matrix_vec_mul md x.`1 sol = x.`2.

op bimodal_selftarget_msis_valid
   (md : mode) (x : bimodal_selftarget_msis_instance)
   (sol : bimodal_selftarget_msis_solution) : bool =
  module_sis_valid md x sol.

lemma module_sis_eval_zero_instance md sol :
  module_sis_eval md (module_sis_zero_instance md) sol = polyveck_zero md.
proof.
by rewrite /module_sis_eval /module_sis_zero_instance
           /matrix_vec_mul /polyveck_sub /polyveck_add /polyveck_neg.
qed.

lemma module_sis_zero_valid md :
  module_sis_valid md (module_sis_zero_instance md) (polyvecl_zero md).
proof.
rewrite /module_sis_valid /module_sis_solution_wf /module_sis_zero_instance.
split.
+ by apply polyvecl_zero_wf.
by rewrite /matrix_vec_mul.
qed.

lemma module_sis_eval_wf md x sol :
  polyveck_wf md (module_sis_eval md x sol).
proof. by rewrite /module_sis_eval; apply polyveck_sub_wf. qed.

lemma module_sis_valid_target_wf md x sol :
  module_sis_valid md x sol =>
  polyveck_wf md x.`2.
proof.
rewrite /module_sis_valid.
move=> [_ targetE].
by rewrite -targetE; apply matrix_vec_mul_wf.
qed.

op bimodal_to_module_sis_instance :
  mode -> bimodal_selftarget_msis_instance -> module_sis_instance =
  fun (_ : mode) x => x.
op bimodal_to_module_sis_solution :
  mode -> bimodal_selftarget_msis_instance ->
  bimodal_selftarget_msis_solution -> module_sis_solution =
  fun (_ : mode) (_ : bimodal_selftarget_msis_instance) sol => sol.

lemma bimodal_to_module_sis_valid md x sol :
  bimodal_selftarget_msis_valid md x sol =>
  module_sis_valid md
    (bimodal_to_module_sis_instance md x)
    (bimodal_to_module_sis_solution md x sol).
proof.
by rewrite /bimodal_selftarget_msis_valid
           /bimodal_to_module_sis_instance
           /bimodal_to_module_sis_solution.
qed.

module type MLWE_Distinguisher = {
  proc distinguish(x : mlwe_instance) : bool
}.

module MLWE_Real_Game(B : MLWE_Distinguisher) = {
  proc main(md : mode) : bool = {
    var x : mlwe_instance;
    var b : bool;

    x <$ dmlwe_real md;
    b <@ B.distinguish(x);
    return b;
  }
}.

module MLWE_Random_Game(B : MLWE_Distinguisher) = {
  proc main(md : mode) : bool = {
    var x : mlwe_instance;
    var b : bool;

    x <$ dmlwe_random md;
    b <@ B.distinguish(x);
    return b;
  }
}.

module type ModuleSIS_Solver = {
  proc solve(x : module_sis_instance) : module_sis_solution option
}.

module ModuleSIS_Relation_Game(B : ModuleSIS_Solver) = {
  proc main(md : mode) : bool = {
    var x : module_sis_instance;
    var sol : module_sis_solution option;

    x <$ dmodule_sis_instance md;
    sol <@ B.solve(x);
    return sol <> None /\ module_sis_valid md x (oget sol);
  }
}.

module type BimodalSelfTargetMSIS_Solver = {
  proc solve(x : bimodal_selftarget_msis_instance) :
    bimodal_selftarget_msis_solution option
}.

module BimodalSelfTargetMSIS_Relation_Game(
  B : BimodalSelfTargetMSIS_Solver
) = {
  proc main(md : mode) : bool = {
    var x : bimodal_selftarget_msis_instance;
    var sol : bimodal_selftarget_msis_solution option;

    x <$ dbimodal_selftarget_msis_instance md;
    sol <@ B.solve(x);
    return sol <> None /\ bimodal_selftarget_msis_valid md x (oget sol);
  }
}.

op lift_bimodal_solution_option
   (md : mode) (x : bimodal_selftarget_msis_instance)
   (sol : bimodal_selftarget_msis_solution option) :
   module_sis_solution option =
  if sol = None then None
  else Some (bimodal_to_module_sis_solution md x (oget sol)).

op dmodule_sis_from_bimodal (md : mode) : module_sis_instance distr =
  dmap (dbimodal_selftarget_msis_instance md)
    (bimodal_to_module_sis_instance md).

lemma dmodule_sis_from_bimodalE md :
  dmodule_sis_from_bimodal md = dbimodal_selftarget_msis_instance md.
proof.
by rewrite /dmodule_sis_from_bimodal /bimodal_to_module_sis_instance dmap_id.
qed.

lemma dmodule_sis_from_bimodal_lossless md :
  is_lossless (dmodule_sis_from_bimodal md).
proof.
rewrite dmodule_sis_from_bimodalE.
by apply dbimodal_selftarget_msis_instance_ll.
qed.

module BimodalToModuleSIS_Lift_Game(
  B : BimodalSelfTargetMSIS_Solver
) = {
  proc main(md : mode) : bool = {
    var x : bimodal_selftarget_msis_instance;
    var lifted_x : module_sis_instance;
    var sol : bimodal_selftarget_msis_solution option;
    var lifted_sol : module_sis_solution;

    x <$ dbimodal_selftarget_msis_instance md;
    sol <@ B.solve(x);
    lifted_x <- bimodal_to_module_sis_instance md x;
    lifted_sol <- bimodal_to_module_sis_solution md x (oget sol);
    return sol <> None /\ module_sis_valid md lifted_x lifted_sol;
  }
}.

lemma bimodal_lift_successE md x sol :
  (sol <> None /\ bimodal_selftarget_msis_valid md x (oget sol)) =
  (lift_bimodal_solution_option md x sol <> None /\
   module_sis_valid md
     (bimodal_to_module_sis_instance md x)
     (oget (lift_bimodal_solution_option md x sol))).
proof.
case: (sol = None) => sol_none.
+ by rewrite /lift_bimodal_solution_option sol_none.
+ by rewrite /lift_bimodal_solution_option sol_none /bimodal_selftarget_msis_valid
             /bimodal_to_module_sis_instance
             /bimodal_to_module_sis_solution.
qed.

section BimodalSolverLift.

declare module B <: BimodalSelfTargetMSIS_Solver.

lemma bimodal_solver_lift_exact &m md :
  Pr[BimodalSelfTargetMSIS_Relation_Game(B).main(md) @ &m : res] =
  Pr[BimodalToModuleSIS_Lift_Game(B).main(md) @ &m : res].
proof.
byequiv (: ={glob B, md} ==> ={res}) => //.
proc.
wp.
call (: ={glob B, x} ==> ={glob B, res}).
+ by sim.
wp.
rnd.
by auto => />; rewrite /bimodal_selftarget_msis_valid
                  /bimodal_to_module_sis_instance
                  /bimodal_to_module_sis_solution.
qed.

end section BimodalSolverLift.

module type ModuleSIS_ModeSolver = {
  proc solve(md : mode, x : module_sis_instance) :
    module_sis_solution option
}.

module type BimodalSelfTargetMSIS_ModeSolver = {
  proc solve(md : mode, x : bimodal_selftarget_msis_instance) :
    bimodal_selftarget_msis_solution option
}.

module ModuleSIS_ModeRelation_Game(
  B : ModuleSIS_ModeSolver
) = {
  proc main(md : mode) : bool = {
    var x : module_sis_instance;
    var sol : module_sis_solution option;

    x <$ dmodule_sis_instance md;
    sol <@ B.solve(md, x);
    return sol <> None /\ module_sis_valid md x (oget sol);
  }
}.

module BimodalSelfTargetMSIS_ModeRelation_Game(
  B : BimodalSelfTargetMSIS_ModeSolver
) = {
  proc main(md : mode) : bool = {
    var x : bimodal_selftarget_msis_instance;
    var sol : bimodal_selftarget_msis_solution option;

    x <$ dbimodal_selftarget_msis_instance md;
    sol <@ B.solve(md, x);
    return sol <> None /\ bimodal_selftarget_msis_valid md x (oget sol);
  }
}.

module ModuleSIS_LiftedDistribution_Relation_Game(
  B : ModuleSIS_ModeSolver
) = {
  proc main(md : mode) : bool = {
    var x : module_sis_instance;
    var sol : module_sis_solution option;

    x <$ dbimodal_selftarget_msis_instance md;
    sol <@ B.solve(md, x);
    return sol <> None /\ module_sis_valid md x (oget sol);
  }
}.

module BimodalModeSolver_As_ModuleSIS(
  B : BimodalSelfTargetMSIS_ModeSolver
) = {
  proc solve(md : mode, x : module_sis_instance) :
    module_sis_solution option = {
    var sol : bimodal_selftarget_msis_solution option;

    sol <@ B.solve(md, x);
    return sol;
  }
}.

section BimodalModeSolverLiftedDistribution.

declare module B <: BimodalSelfTargetMSIS_ModeSolver.

lemma bimodal_mode_solver_lifted_distribution_exact &m md :
  Pr[BimodalSelfTargetMSIS_ModeRelation_Game(B).main(md) @ &m : res] =
  Pr[ModuleSIS_LiftedDistribution_Relation_Game(
       BimodalModeSolver_As_ModuleSIS(B)).main(md) @ &m : res].
proof.
byequiv (: ={glob B, md} ==> ={res}) => //.
proc.
inline BimodalModeSolver_As_ModuleSIS(B).solve.
wp.
call (: ={glob B, md, x} ==> ={glob B, res}).
+ by sim.
wp.
rnd.
by auto => />; rewrite /bimodal_selftarget_msis_valid.
qed.

end section BimodalModeSolverLiftedDistribution.

module type MLWE_Reduction = {
  proc main() : bool
}.

module type BimodalSelfTargetMSIS_Reduction = {
  proc main() : bool
}.

module type ModuleSIS_Reduction = {
  proc main() : bool
}.

module MLWE_Game(B : MLWE_Reduction) = {
  proc main() : bool = {
    var b : bool;

    b <@ B.main();
    return b;
  }
}.

module BimodalSelfTargetMSIS_Game(B : BimodalSelfTargetMSIS_Reduction) = {
  proc main() : bool = {
    var b : bool;

    b <@ B.main();
    return b;
  }
}.

module ModuleSIS_Game(B : ModuleSIS_Reduction) = {
  proc main() : bool = {
    var b : bool;

    b <@ B.main();
    return b;
  }
}.

module BimodalMSIS_As_ModuleSIS(B : BimodalSelfTargetMSIS_Reduction) = {
  proc main() : bool = {
    var b : bool;

    b <@ B.main();
    return b;
  }
}.

section BimodalModuleSISReduction.

declare module B <: BimodalSelfTargetMSIS_Reduction.

lemma bimodal_msis_as_module_sis_exact &m :
  Pr[BimodalSelfTargetMSIS_Game(B).main() @ &m : res] =
  Pr[ModuleSIS_Game(BimodalMSIS_As_ModuleSIS(B)).main() @ &m : res].
proof.
byequiv (: ={glob B} ==> ={res}) => //.
proc.
inline BimodalMSIS_As_ModuleSIS(B).main.
wp.
call (: ={glob B} ==> ={glob B, res}).
+ by sim.
by auto.
qed.

end section BimodalModuleSISReduction.

end HAETAE_Assumptions.
