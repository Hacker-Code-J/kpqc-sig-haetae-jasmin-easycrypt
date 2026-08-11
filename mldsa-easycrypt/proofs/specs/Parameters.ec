require import AllCore IntDiv List Ring.

(* ML-DSA parameters. Previously this file cloned [DParams] from the dilithium
   submodule; the DParams obligations are now inlined here as axioms on
   concrete parameter ops, scoped under the [MLDSAParams] theory for source
   compatibility with the prior `import MLDSAParams.` convention. *)

abbrev q : int = 8380417.
abbrev n : int = 256.
axiom prime_q : prime q.
abbrev d : int = 13.
op tau : int.                (*    39             49           60      : exact number of 1s in c *)
op lambda : int.             (*   128            192          256      : collision strength of ctilde *)
op gamma1 : int.             (*   2^17           2^19         2^19     : coefficient range of y*)
op gamma2 : int.             (* (q-1)%/88     (q-1)%/32    (q-1)%/32   : low order rounding range *)
(* We have k x l matrices *)
op kvec : int.               (*    4              6             8      : number of rows of A *)
op lvec : int.               (*    4              5             7      : number of columns of A *)
op Eta : int.                (*    2              4             2      : private key range *)
op Beta : int = tau * Eta.   (*   78             196           120     *)
op w_hint : int.             (*   80              55            75     : max number of 1s in the hint *)
op kappa_max : int.          (* abstract bound on rejection sampling iterations *)

axiom param_sets :
   (tau,lambda,gamma1,gamma2,kvec,lvec,Eta,w_hint) \in [ (* (39,128,2^17,(q-1)%/88,4,4,2,80); ub_d Fails! *)
                                                  (49,192,2^19,(q-1)%/32,6,5,4,55);
                                                  (60,256,2^19,(q-1)%/32,8,7,2,75)
                                                ].

theory MLDSAParams.

(* Parameter axioms — inlined from the former DParams clone. *)
lemma gt0_n  : 0 < n   by auto.
lemma gt0_eta : 0 < Eta by smt(param_sets).
lemma gt0_k   : 0 < kvec by smt(param_sets).
lemma gt0_l   : 0 < lvec by smt(param_sets).
lemma gt0_beta : 0 < Beta by smt(param_sets).
lemma tau_bound : 1 <= tau <= n /\ tau <= 64 by smt(param_sets).
lemma gt0_d : 0 < d by auto.
lemma eta_tau_leq_b : Eta * tau <= Beta by smt(param_sets).
lemma gamma2_bound  : 2 <= gamma2 <= q %/ 4 by smt(param_sets).
lemma gamma2_div : 2 * gamma2 %| (q - 1) by smt(param_sets).
lemma beta_gamma2_lt : Beta < gamma2 by smt(param_sets).

lemma ub_d : tau * 2 ^ d <= 2 * gamma2.
proof.
by have  H /=:=param_sets;elim H => /=;rewrite /=;
  move => [#] ->?? -> * /=;do 12!(rewrite expr_pred //=);rewrite expr1 => /=.
qed.

lemma beta_gamma1_lt : Beta < gamma1.
proof.
by rewrite /Beta;
 have  H /=:=param_sets;elim H => /=;rewrite /=;
  move => [#] ->?->??? -> * /=;do 18!(rewrite expr_pred //=);rewrite expr1 => /=.
qed.

end MLDSAParams.
