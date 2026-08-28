require import AllCore Distr IntDiv Real Ring StdOrder.

from Jasmin require import JModel_x86.

require import
  Fq
  KeygenM23FinalizeSpec
  KeygenM23FinalizeSemantics
  KeygenM23FinalizeArraySemantics
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
  Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze.

import RealOrder.

theory Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.

(* This file is purely scalar: one fixed [b,a] context and one ideal eta trit.
   In general the finalized [s2] law is neither mean-zero nor symmetric; the
   mod-1 interior class already has mean [-1/3] and centered third moment
   [16/27].  That skew is intentional and must be exposed before any later tail
   model can safely aggregate words.  This file does not make any array
   independence claim, FFT claim, SHAKE/oracle claim, or actual context
   distribution claim. *)

op context_valid (b a : W32.t) : bool =
  Fq.bw32 b 16 /\ W32.to_uint a < KeygenM23FinalizeSemantics.q.

op rho (b a : W32.t) : int =
  (W32.to_sint b + W32.to_uint a) %% KeygenM23FinalizeSemantics.q.

op math_output (b a : W32.t) (x : int) : int =
  x -
  KeygenM23FinalizeSemantics.vk_low_int
    ((rho b a + x) %% KeygenM23FinalizeSemantics.q).

op ideal_final_s2_distribution (b a : W32.t) : int distr =
  dmap
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (math_output b a).

op ideal_final_s2_class_index (b a : W32.t) : int =
  if rho b a = 0 then 0
  else if rho b a = KeygenM23FinalizeSemantics.q - 1 then 1
  else 2 + rho b a %% 4.

op ideal_final_s2_class_rho0 (b a : W32.t) : bool =
  ideal_final_s2_class_index b a = 0.

op ideal_final_s2_class_rhoq1 (b a : W32.t) : bool =
  ideal_final_s2_class_index b a = 1.

op ideal_final_s2_class_mod0 (b a : W32.t) : bool =
  ideal_final_s2_class_index b a = 2.

op ideal_final_s2_class_mod1 (b a : W32.t) : bool =
  ideal_final_s2_class_index b a = 3.

op ideal_final_s2_class_mod2 (b a : W32.t) : bool =
  ideal_final_s2_class_index b a = 4.

op ideal_final_s2_class_mod3 (b a : W32.t) : bool =
  ideal_final_s2_class_index b a = 5.

op class_output_table (b a : W32.t) (x : int) : int =
  if ideal_final_s2_class_index b a = 0 then
    if x = -1 then -1 else 0
  else if ideal_final_s2_class_index b a = 1 then
    if x = 1 then 1 else 0
  else if ideal_final_s2_class_index b a = 2 then
    0
  else if ideal_final_s2_class_index b a = 3 then
    if x = 1 then 1 else -1
  else if ideal_final_s2_class_index b a = 4 then
    2 * x
  else
    if x = -1 then -1 else 1.

op ideal_final_s2_mean (b a : W32.t) : real =
  ((math_output b a (-1))%r +
   (math_output b a 0)%r +
   (math_output b a 1)%r) / 3%r.

op ideal_final_s2_raw_moment2 (b a : W32.t) : real =
  (((math_output b a (-1))%r)^2 +
   ((math_output b a 0)%r)^2 +
   ((math_output b a 1)%r)^2) / 3%r.

op ideal_final_s2_raw_moment4 (b a : W32.t) : real =
  (((math_output b a (-1))%r)^4 +
   ((math_output b a 0)%r)^4 +
   ((math_output b a 1)%r)^4) / 3%r.

op ideal_final_s2_raw_moment8 (b a : W32.t) : real =
  (((math_output b a (-1))%r)^8 +
   ((math_output b a 0)%r)^8 +
   ((math_output b a 1)%r)^8) / 3%r.

op ideal_final_s2_centered_moment2 (b a : W32.t) : real =
  ((((math_output b a (-1))%r - ideal_final_s2_mean b a)^2) +
   (((math_output b a 0)%r - ideal_final_s2_mean b a)^2) +
   (((math_output b a 1)%r - ideal_final_s2_mean b a)^2)) / 3%r.

op ideal_final_s2_centered_moment3 (b a : W32.t) : real =
  ((((math_output b a (-1))%r - ideal_final_s2_mean b a)^3) +
   (((math_output b a 0)%r - ideal_final_s2_mean b a)^3) +
   (((math_output b a 1)%r - ideal_final_s2_mean b a)^3)) / 3%r.

op ideal_final_s2_centered_moment4 (b a : W32.t) : real =
  ((((math_output b a (-1))%r - ideal_final_s2_mean b a)^4) +
   (((math_output b a 0)%r - ideal_final_s2_mean b a)^4) +
   (((math_output b a 1)%r - ideal_final_s2_mean b a)^4)) / 3%r.

op ideal_final_s2_centered_moment8 (b a : W32.t) : real =
  ((((math_output b a (-1))%r - ideal_final_s2_mean b a)^8) +
   (((math_output b a 0)%r - ideal_final_s2_mean b a)^8) +
   (((math_output b a 1)%r - ideal_final_s2_mean b a)^8)) / 3%r.

lemma rho_range b a :
  0 <= rho b a < KeygenM23FinalizeSemantics.q.
proof.
rewrite /rho.
apply modz_cmp.
rewrite /KeygenM23FinalizeSemantics.q.
done.
qed.

lemma ideal_final_s2_class_range b a :
  0 <= ideal_final_s2_class_index b a <= 5.
proof.
rewrite /ideal_final_s2_class_index.
have hr := rho_range b a.
case (rho b a = 0) => hr0; first smt().
case (rho b a = KeygenM23FinalizeSemantics.q - 1) => hrq1; first smt().
move: hr.
rewrite /KeygenM23FinalizeSemantics.q.
smt(@IntDiv).
qed.

lemma ideal_final_s2_class_exhaustive b a :
  ideal_final_s2_class_rho0 b a \/
  ideal_final_s2_class_rhoq1 b a \/
  ideal_final_s2_class_mod0 b a \/
  ideal_final_s2_class_mod1 b a \/
  ideal_final_s2_class_mod2 b a \/
  ideal_final_s2_class_mod3 b a.
proof.
have hrange := ideal_final_s2_class_range b a.
rewrite /ideal_final_s2_class_rho0
        /ideal_final_s2_class_rhoq1
        /ideal_final_s2_class_mod0
        /ideal_final_s2_class_mod1
        /ideal_final_s2_class_mod2
        /ideal_final_s2_class_mod3.
smt().
qed.

lemma ideal_final_s2_class_rho0E b a :
  ideal_final_s2_class_rho0 b a <=> rho b a = 0.
proof.
rewrite /ideal_final_s2_class_rho0 /ideal_final_s2_class_index.
case (rho b a = 0) => hr0; smt().
qed.

lemma ideal_final_s2_class_rhoq1E b a :
  ideal_final_s2_class_rhoq1 b a <=>
  rho b a = KeygenM23FinalizeSemantics.q - 1.
proof.
rewrite /ideal_final_s2_class_rhoq1 /ideal_final_s2_class_index.
case (rho b a = 0) => hr0; first smt().
case (rho b a = KeygenM23FinalizeSemantics.q - 1) => hr1; smt().
qed.

lemma ideal_final_s2_class_mod0E b a :
  ideal_final_s2_class_mod0 b a <=>
  0 < rho b a < KeygenM23FinalizeSemantics.q - 1 /\ rho b a %% 4 = 0.
proof.
rewrite /ideal_final_s2_class_mod0 /ideal_final_s2_class_index.
have hr := rho_range b a.
case (rho b a = 0) => hr0; first smt().
case (rho b a = KeygenM23FinalizeSemantics.q - 1) => hr1; first smt().
split.
+ move=> hidx.
   have hm : rho b a %% 4 = 0 by smt().
   move: hr hr0 hr1 hm.
   rewrite /KeygenM23FinalizeSemantics.q.
   smt().
move=> [hrint hm].
by rewrite hm.
qed.

lemma ideal_final_s2_class_mod1E b a :
  ideal_final_s2_class_mod1 b a <=>
  0 < rho b a < KeygenM23FinalizeSemantics.q - 1 /\ rho b a %% 4 = 1.
proof.
rewrite /ideal_final_s2_class_mod1 /ideal_final_s2_class_index.
have hr := rho_range b a.
case (rho b a = 0) => hr0; first smt().
case (rho b a = KeygenM23FinalizeSemantics.q - 1) => hr1; first smt().
split.
+ move=> hidx.
   have hm : rho b a %% 4 = 1 by smt().
   move: hr hr0 hr1 hm.
   rewrite /KeygenM23FinalizeSemantics.q.
   smt().
move=> [hrint hm].
by rewrite hm.
qed.

lemma ideal_final_s2_class_mod2E b a :
  ideal_final_s2_class_mod2 b a <=>
  0 < rho b a < KeygenM23FinalizeSemantics.q - 1 /\ rho b a %% 4 = 2.
proof.
rewrite /ideal_final_s2_class_mod2 /ideal_final_s2_class_index.
have hr := rho_range b a.
case (rho b a = 0) => hr0; first smt().
case (rho b a = KeygenM23FinalizeSemantics.q - 1) => hr1; first smt().
split.
+ move=> hidx.
   have hm : rho b a %% 4 = 2 by smt().
   move: hr hr0 hr1 hm.
   rewrite /KeygenM23FinalizeSemantics.q.
   smt().
move=> [hrint hm].
by rewrite hm.
qed.

lemma ideal_final_s2_class_mod3E b a :
  ideal_final_s2_class_mod3 b a <=>
  0 < rho b a < KeygenM23FinalizeSemantics.q - 1 /\ rho b a %% 4 = 3.
proof.
rewrite /ideal_final_s2_class_mod3 /ideal_final_s2_class_index.
have hr := rho_range b a.
case (rho b a = 0) => hr0; first smt().
case (rho b a = KeygenM23FinalizeSemantics.q - 1) => hr1; first smt().
split.
+ move=> hidx.
   have hm : rho b a %% 4 = 3 by smt().
   move: hr hr0 hr1 hm.
   rewrite /KeygenM23FinalizeSemantics.q.
   smt().
move=> [hrint hm].
by rewrite hm.
qed.

lemma vk_low_int_mod4_0 x :
  x %% 4 = 0 =>
  KeygenM23FinalizeSemantics.vk_low_int x = 0.
proof.
move=> hx.
have h2 : x %% 2 = 0 by smt(@IntDiv).
by rewrite /KeygenM23FinalizeSemantics.vk_low_int h2.
qed.

lemma vk_low_int_mod4_1 x :
  x %% 4 = 1 =>
  KeygenM23FinalizeSemantics.vk_low_int x = 1.
proof.
move=> hx.
rewrite KeygenM23FinalizeSemantics.vk_low_int_formula.
have h2 : x %% 2 = 1 by smt(@IntDiv).
have hh : (x %/ 2) %% 2 = 0.
+ have hx4 : x = 4 * (x %/ 4) + 1 by rewrite (divz_eq x 4); smt().
   have hx2 : x %/ 2 = 2 * (x %/ 4) by smt(@IntDiv).
   rewrite hx2.
   smt(@IntDiv).
by rewrite h2 hh.
qed.

lemma vk_low_int_mod4_2 x :
  x %% 4 = 2 =>
  KeygenM23FinalizeSemantics.vk_low_int x = 0.
proof.
move=> hx.
have h2 : x %% 2 = 0 by smt(@IntDiv).
by rewrite /KeygenM23FinalizeSemantics.vk_low_int h2.
qed.

lemma vk_low_int_mod4_3 x :
  x %% 4 = 3 =>
  KeygenM23FinalizeSemantics.vk_low_int x = -1.
proof.
move=> hx.
rewrite KeygenM23FinalizeSemantics.vk_low_int_formula.
have h2 : x %% 2 = 1 by smt(@IntDiv).
have hh : (x %/ 2) %% 2 = 1.
+ pose k := x %/ 4.
  have hx4 : x = 4 * k + 3.
  + rewrite /k (divz_eq x 4).
    smt().
  have hx2 : x %/ 2 = 2 * k + 1.
  + change (x %/ 2 = 2 * k + 1).
    rewrite hx4.
    have -> : 4 * k + 3 = (2 * k + 1) * 2 + 1 by ring.
    rewrite divzMDl 1:/# divz_small 1:/#.
    ring.
  rewrite hx2.
  smt(@IntDiv).
rewrite h2 hh.
ring.
qed.

lemma ideal_trit_to_word_reachable x :
  x \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution =>
  -1 <= W32.to_sint (W32.of_int x) <= 1.
proof.
move=> hx.
rewrite
  (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_centered_trit_to_sint x hx).
rewrite
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_support in hx.
smt().
qed.

lemma raw_residue_math_arg b a x :
  x \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution =>
  KeygenM23FinalizeArraySemantics.raw_residue b (W32.of_int x) a =
  (rho b a + x) %% KeygenM23FinalizeSemantics.q.
proof.
move=> hx.
rewrite /KeygenM23FinalizeArraySemantics.raw_residue
        /KeygenM23FinalizeArraySemantics.raw_sum_int
        /rho.
rewrite
  (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_centered_trit_to_sint x hx).
smt(@IntDiv).
qed.

lemma finalize_s2_word_decode_math_output b a x :
  context_valid b a =>
  x \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution =>
  W32.to_sint (KeygenM23FinalizeSpec.finalize_s2_word b (W32.of_int x) a) =
  math_output b a x.
proof.
move=> [hb ha] hx.
have hreach :
    KeygenM23FinalizeArraySemantics.reachable_word_inputs
      b (W32.of_int x) a.
+ rewrite /KeygenM23FinalizeArraySemantics.reachable_word_inputs.
   split; first exact hb.
   split.
   + exact (ideal_trit_to_word_reachable x hx).
   exact ha.
have [_ hs2] :=
  KeygenM23FinalizeArraySemantics.reachable_finalize_words_decode
    b (W32.of_int x) a hreach.
rewrite
  (Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
    .ideal_eta_centered_trit_to_sint x hx) in hs2.
rewrite /math_output (raw_residue_math_arg b a x hx) in hs2.
exact hs2.
qed.

lemma rho_wrap_minus1 b a :
  rho b a = 0 =>
  (rho b a - 1) %% KeygenM23FinalizeSemantics.q =
  KeygenM23FinalizeSemantics.q - 1.
proof.
move=> ->.
rewrite /KeygenM23FinalizeSemantics.q.
trivial.
qed.

lemma rho_wrap_plus1 b a :
  rho b a = KeygenM23FinalizeSemantics.q - 1 =>
  (rho b a + 1) %% KeygenM23FinalizeSemantics.q = 0.
proof.
move=> ->.
rewrite /KeygenM23FinalizeSemantics.q.
trivial.
qed.

lemma rho_interior_minus1 b a :
  0 < rho b a < KeygenM23FinalizeSemantics.q - 1 =>
  (rho b a - 1) %% KeygenM23FinalizeSemantics.q = rho b a - 1.
proof.
move=> hr.
apply modz_small.
rewrite /KeygenM23FinalizeSemantics.q in hr.
smt().
qed.

lemma rho_interior_zero b a :
  0 < rho b a < KeygenM23FinalizeSemantics.q - 1 =>
  rho b a %% KeygenM23FinalizeSemantics.q = rho b a.
proof.
move=> hr.
apply modz_small.
rewrite /KeygenM23FinalizeSemantics.q in hr.
smt().
qed.

lemma rho_interior_plus1 b a :
  0 < rho b a < KeygenM23FinalizeSemantics.q - 1 =>
  (rho b a + 1) %% KeygenM23FinalizeSemantics.q = rho b a + 1.
proof.
move=> hr.
apply modz_small.
rewrite /KeygenM23FinalizeSemantics.q in hr.
smt().
qed.

lemma math_output_rho0_triple b a :
  ideal_final_s2_class_rho0 b a =>
  math_output b a (-1) = -1 /\
  math_output b a 0 = 0 /\
  math_output b a 1 = 0.
proof.
move=> hclass.
have hrho : rho b a = 0 by
  rewrite -ideal_final_s2_class_rho0E.
have hargm1 : ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) %% 4 = 0.
+ move: hrho.
  rewrite /KeygenM23FinalizeSemantics.q.
  smt(@IntDiv).
have harg0 : ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) %% 4 = 0.
+ move: hrho.
  rewrite /KeygenM23FinalizeSemantics.q.
  smt(@IntDiv).
have harg1 : ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) %% 4 = 1.
+ move: hrho.
  rewrite /KeygenM23FinalizeSemantics.q.
  smt(@IntDiv).
have hlowm1 := vk_low_int_mod4_0
  ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) hargm1.
have hlow0 := vk_low_int_mod4_0
  ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) harg0.
have hlow1 := vk_low_int_mod4_1
  ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) harg1.
rewrite /math_output hlowm1 hlow0 hlow1.
smt().
qed.

lemma math_output_mod0_triple b a :
  ideal_final_s2_class_mod0 b a =>
  math_output b a (-1) = 0 /\
  math_output b a 0 = 0 /\
  math_output b a 1 = 0.
proof.
move=> hclass.
have [hrange hmod] : 0 < rho b a < KeygenM23FinalizeSemantics.q - 1 /\
                     rho b a %% 4 = 0 by
  rewrite -ideal_final_s2_class_mod0E.
have hargm1 : ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) %% 4 = 3.
+ rewrite rho_interior_minus1 1:hrange.
  smt(modzDml).
have harg0 : ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) %% 4 = 0.
+ have hrhoq := rho_interior_zero b a hrange.
  smt().
have harg1 : ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) %% 4 = 1.
+ rewrite rho_interior_plus1 1:hrange.
  smt(modzDml).
have hlowm1 := vk_low_int_mod4_3
  ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) hargm1.
have hlow0 := vk_low_int_mod4_0
  ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) harg0.
have hlow1 := vk_low_int_mod4_1
  ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) harg1.
rewrite /math_output hlowm1 hlow0 hlow1.
smt().
qed.

lemma math_output_rhoq1_triple b a :
  ideal_final_s2_class_rhoq1 b a =>
  math_output b a (-1) = 0 /\
  math_output b a 0 = 0 /\
  math_output b a 1 = 1.
proof.
move=> hclass.
have hrho : rho b a = KeygenM23FinalizeSemantics.q - 1 by
  rewrite -ideal_final_s2_class_rhoq1E.
have hargm1 : ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) %% 4 = 3.
+ move: hrho.
  rewrite /KeygenM23FinalizeSemantics.q.
  smt(@IntDiv).
have harg0 : ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) %% 4 = 0.
+ move: hrho.
  rewrite /KeygenM23FinalizeSemantics.q.
  smt(@IntDiv).
have harg1 : ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) %% 4 = 0.
+ move: hrho.
  rewrite /KeygenM23FinalizeSemantics.q.
  smt(@IntDiv).
have hlowm1 := vk_low_int_mod4_3
  ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) hargm1.
have hlow0 := vk_low_int_mod4_0
  ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) harg0.
have hlow1 := vk_low_int_mod4_0
  ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) harg1.
rewrite /math_output hlowm1 hlow0 hlow1.
smt().
qed.

lemma math_output_mod1_triple b a :
  ideal_final_s2_class_mod1 b a =>
  math_output b a (-1) = -1 /\
  math_output b a 0 = -1 /\
  math_output b a 1 = 1.
proof.
move=> hclass.
have [hrange hmod] : 0 < rho b a < KeygenM23FinalizeSemantics.q - 1 /\
                     rho b a %% 4 = 1 by
  rewrite -ideal_final_s2_class_mod1E.
have hargm1 : ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) %% 4 = 0.
+ rewrite rho_interior_minus1 1:hrange.
  smt(modzDml).
have harg0 : ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) %% 4 = 1.
+ have hrhoq := rho_interior_zero b a hrange.
  smt().
have harg1 : ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) %% 4 = 2.
+ rewrite rho_interior_plus1 1:hrange.
  smt(modzDml).
have hlowm1 := vk_low_int_mod4_0
  ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) hargm1.
have hlow0 := vk_low_int_mod4_1
  ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) harg0.
have hlow1 := vk_low_int_mod4_2
  ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) harg1.
rewrite /math_output hlowm1 hlow0 hlow1.
smt().
qed.

lemma math_output_mod2_triple b a :
  ideal_final_s2_class_mod2 b a =>
  math_output b a (-1) = -2 /\
  math_output b a 0 = 0 /\
  math_output b a 1 = 2.
proof.
move=> hclass.
have [hrange hmod] : 0 < rho b a < KeygenM23FinalizeSemantics.q - 1 /\
                     rho b a %% 4 = 2 by
  rewrite -ideal_final_s2_class_mod2E.
have hargm1 : ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) %% 4 = 1.
+ rewrite rho_interior_minus1 1:hrange.
  smt(modzDml).
have harg0 : ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) %% 4 = 2.
+ have hrhoq := rho_interior_zero b a hrange.
  smt().
have harg1 : ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) %% 4 = 3.
+ rewrite rho_interior_plus1 1:hrange.
  smt(modzDml).
have hlowm1 := vk_low_int_mod4_1
  ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) hargm1.
have hlow0 := vk_low_int_mod4_2
  ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) harg0.
have hlow1 := vk_low_int_mod4_3
  ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) harg1.
rewrite /math_output hlowm1 hlow0 hlow1.
smt().
qed.

lemma math_output_mod3_triple b a :
  ideal_final_s2_class_mod3 b a =>
  math_output b a (-1) = -1 /\
  math_output b a 0 = 1 /\
  math_output b a 1 = 1.
proof.
move=> hclass.
have [hrange hmod] : 0 < rho b a < KeygenM23FinalizeSemantics.q - 1 /\
                     rho b a %% 4 = 3 by
  rewrite -ideal_final_s2_class_mod3E.
have hargm1 : ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) %% 4 = 2.
+ rewrite rho_interior_minus1 1:hrange.
  smt(modzDml).
have harg0 : ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) %% 4 = 3.
+ have hrhoq := rho_interior_zero b a hrange.
  smt().
have harg1 : ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) %% 4 = 0.
+ rewrite rho_interior_plus1 1:hrange.
  smt(modzDml).
have hlowm1 := vk_low_int_mod4_2
  ((rho b a + (-1)) %% KeygenM23FinalizeSemantics.q) hargm1.
have hlow0 := vk_low_int_mod4_3
  ((rho b a + 0) %% KeygenM23FinalizeSemantics.q) harg0.
have hlow1 := vk_low_int_mod4_0
  ((rho b a + 1) %% KeygenM23FinalizeSemantics.q) harg1.
rewrite /math_output hlowm1 hlow0 hlow1.
smt().
qed.

lemma class_output_table_eq b a x :
  x \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution =>
  math_output b a x = class_output_table b a x.
proof.
move=> hx.
have hxcase :
    x = -1 \/ x = 0 \/ x = 1 by
  rewrite Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
            .ideal_eta_centered_trit_support in hx.
have hexh := ideal_final_s2_class_exhaustive b a.
move: hexh.
rewrite
  /ideal_final_s2_class_rho0
  /ideal_final_s2_class_rhoq1
  /ideal_final_s2_class_mod0
  /ideal_final_s2_class_mod1
  /ideal_final_s2_class_mod2
  /ideal_final_s2_class_mod3.
move=> [h0 | [h1 | [h2 | [h3 | [h4 | h5]]]]].
+ have htriple := math_output_rho0_triple b a h0.
  case: hxcase => [-> | [-> | ->]];
    move: htriple; rewrite /class_output_table h0; smt().
+ have htriple := math_output_rhoq1_triple b a h1.
  have hneq0 : ideal_final_s2_class_index b a <> 0 by smt().
  case: hxcase => [-> | [-> | ->]];
    move: htriple;
    rewrite /class_output_table ifF 1:/# h1; smt().
+ have htriple := math_output_mod0_triple b a h2.
  have hneq0 : ideal_final_s2_class_index b a <> 0 by smt().
  have hneq1 : ideal_final_s2_class_index b a <> 1 by smt().
  case: hxcase => [-> | [-> | ->]];
    move: htriple;
    rewrite /class_output_table ifF 1:/# ifF 1:/# h2; smt().
+ have htriple := math_output_mod1_triple b a h3.
  have hneq0 : ideal_final_s2_class_index b a <> 0 by smt().
  have hneq1 : ideal_final_s2_class_index b a <> 1 by smt().
  have hneq2 : ideal_final_s2_class_index b a <> 2 by smt().
  case: hxcase => [-> | [-> | ->]];
    move: htriple;
    rewrite /class_output_table ifF 1:/# ifF 1:/# ifF 1:/# h3; smt().
+ have htriple := math_output_mod2_triple b a h4.
  have hneq0 : ideal_final_s2_class_index b a <> 0 by smt().
  have hneq1 : ideal_final_s2_class_index b a <> 1 by smt().
  have hneq2 : ideal_final_s2_class_index b a <> 2 by smt().
  have hneq3 : ideal_final_s2_class_index b a <> 3 by smt().
  case: hxcase => [-> | [-> | ->]];
    move: htriple;
    rewrite /class_output_table ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# h4;
    smt().
have htriple := math_output_mod3_triple b a h5.
have hneq0 : ideal_final_s2_class_index b a <> 0 by smt().
have hneq1 : ideal_final_s2_class_index b a <> 1 by smt().
have hneq2 : ideal_final_s2_class_index b a <> 2 by smt().
have hneq3 : ideal_final_s2_class_index b a <> 3 by smt().
have hneq4 : ideal_final_s2_class_index b a <> 4 by smt().
case: hxcase => [-> | [-> | ->]];
  move: htriple;
  rewrite /class_output_table
          ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#;
  smt().
qed.

lemma ideal_final_s2_distribution_class_table b a :
  ideal_final_s2_distribution b a =
  dmap
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (class_output_table b a).
proof.
rewrite /ideal_final_s2_distribution.
apply eq_dmap_in => x hx.
exact (class_output_table_eq b a x hx).
qed.

lemma ideal_final_s2_distribution_lossless b a :
  is_lossless (ideal_final_s2_distribution b a).
proof.
rewrite /ideal_final_s2_distribution.
apply dmap_ll.
exact
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_lossless.
qed.

lemma ideal_final_s2_distribution_support b a y :
  y \in ideal_final_s2_distribution b a <=>
  exists x,
    x \in
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution /\
    y = math_output b a x.
proof.
rewrite /ideal_final_s2_distribution supp_dmap.
trivial.
qed.

lemma mean_rho0 b a :
  ideal_final_s2_class_rho0 b a =>
  ideal_final_s2_mean b a = -1%r / 3%r.
proof.
move=> hclass.
have [hneg [hzero hone]] := math_output_rho0_triple b a hclass.
rewrite /ideal_final_s2_mean hneg hzero hone.
ring.
qed.

lemma moments_rho0 b a :
  ideal_final_s2_class_rho0 b a =>
  ideal_final_s2_raw_moment2 b a = 1%r / 3%r /\
  ideal_final_s2_raw_moment4 b a = 1%r / 3%r /\
  ideal_final_s2_raw_moment8 b a = 1%r / 3%r /\
  ideal_final_s2_centered_moment2 b a = 2%r / 9%r /\
  ideal_final_s2_centered_moment3 b a = -2%r / 27%r /\
  ideal_final_s2_centered_moment4 b a = 2%r / 27%r /\
  ideal_final_s2_centered_moment8 b a = 86%r / 6561%r.
proof.
move=> hclass.
have hmean := mean_rho0 b a hclass.
have [hneg [hzero hone]] := math_output_rho0_triple b a hclass.
rewrite /ideal_final_s2_raw_moment2 /ideal_final_s2_raw_moment4
        /ideal_final_s2_raw_moment8
        /ideal_final_s2_centered_moment2
        /ideal_final_s2_centered_moment3
        /ideal_final_s2_centered_moment4
        /ideal_final_s2_centered_moment8
        hneg hzero hone hmean.
split.
+ field; trivial.
+ split.
  + field; trivial.
  + split.
    + field; trivial.
    + split.
      + field; trivial.
      + split.
        + field; trivial.
        + split.
          + field; trivial.
          + field; trivial.
qed.

lemma mean_mod0 b a :
  ideal_final_s2_class_mod0 b a =>
  ideal_final_s2_mean b a = 0%r.
proof.
move=> hclass.
have [hm1 [h0 h1]] := math_output_mod0_triple b a hclass.
rewrite /ideal_final_s2_mean hm1 h0 h1.
ring.
qed.

lemma moments_mod0 b a :
  ideal_final_s2_class_mod0 b a =>
  ideal_final_s2_raw_moment2 b a = 0%r /\
  ideal_final_s2_raw_moment4 b a = 0%r /\
  ideal_final_s2_raw_moment8 b a = 0%r /\
  ideal_final_s2_centered_moment2 b a = 0%r /\
  ideal_final_s2_centered_moment3 b a = 0%r /\
  ideal_final_s2_centered_moment4 b a = 0%r /\
  ideal_final_s2_centered_moment8 b a = 0%r.
proof.
move=> hclass.
have hmean := mean_mod0 b a hclass.
have [hm1 [h0 h1]] := math_output_mod0_triple b a hclass.
rewrite /ideal_final_s2_raw_moment2 /ideal_final_s2_raw_moment4
        /ideal_final_s2_raw_moment8
        /ideal_final_s2_centered_moment2
        /ideal_final_s2_centered_moment3
        /ideal_final_s2_centered_moment4
        /ideal_final_s2_centered_moment8
        hm1 h0 h1 hmean.
split.
+ field; trivial.
+ split.
  + field; trivial.
  + split.
    + field; trivial.
    + split.
      + field; trivial.
      + split.
        + field; trivial.
        + split.
          + field; trivial.
          + field; trivial.
qed.

lemma mean_rhoq1 b a :
  ideal_final_s2_class_rhoq1 b a =>
  ideal_final_s2_mean b a = 1%r / 3%r.
proof.
move=> hclass.
have [hm1 [h0 h1]] := math_output_rhoq1_triple b a hclass.
rewrite /ideal_final_s2_mean hm1 h0 h1.
ring.
qed.

lemma moments_rhoq1 b a :
  ideal_final_s2_class_rhoq1 b a =>
  ideal_final_s2_raw_moment2 b a = 1%r / 3%r /\
  ideal_final_s2_raw_moment4 b a = 1%r / 3%r /\
  ideal_final_s2_raw_moment8 b a = 1%r / 3%r /\
  ideal_final_s2_centered_moment2 b a = 2%r / 9%r /\
  ideal_final_s2_centered_moment3 b a = 2%r / 27%r /\
  ideal_final_s2_centered_moment4 b a = 2%r / 27%r /\
  ideal_final_s2_centered_moment8 b a = 86%r / 6561%r.
proof.
move=> hclass.
have hmean := mean_rhoq1 b a hclass.
have [hm1 [h0 h1]] := math_output_rhoq1_triple b a hclass.
rewrite /ideal_final_s2_raw_moment2 /ideal_final_s2_raw_moment4
        /ideal_final_s2_raw_moment8
        /ideal_final_s2_centered_moment2
        /ideal_final_s2_centered_moment3
        /ideal_final_s2_centered_moment4
        /ideal_final_s2_centered_moment8
        hm1 h0 h1 hmean.
split.
+ field; trivial.
+ split.
  + field; trivial.
  + split.
    + field; trivial.
    + split.
      + field; trivial.
      + split.
        + field; trivial.
        + split.
          + field; trivial.
          + field; trivial.
qed.

lemma mean_mod1 b a :
  ideal_final_s2_class_mod1 b a =>
  ideal_final_s2_mean b a = -1%r / 3%r.
proof.
move=> hclass.
have [hm1 [h0 h1]] := math_output_mod1_triple b a hclass.
rewrite /ideal_final_s2_mean hm1 h0 h1.
ring.
qed.

lemma moments_mod1 b a :
  ideal_final_s2_class_mod1 b a =>
  ideal_final_s2_raw_moment2 b a = 1%r /\
  ideal_final_s2_raw_moment4 b a = 1%r /\
  ideal_final_s2_raw_moment8 b a = 1%r /\
  ideal_final_s2_centered_moment2 b a = 8%r / 9%r /\
  ideal_final_s2_centered_moment3 b a = 16%r / 27%r /\
  ideal_final_s2_centered_moment4 b a = 32%r / 27%r /\
  ideal_final_s2_centered_moment8 b a = 22016%r / 6561%r.
proof.
move=> hclass.
have hmean := mean_mod1 b a hclass.
have [hm1 [h0 h1]] := math_output_mod1_triple b a hclass.
rewrite /ideal_final_s2_raw_moment2 /ideal_final_s2_raw_moment4
        /ideal_final_s2_raw_moment8
        /ideal_final_s2_centered_moment2
        /ideal_final_s2_centered_moment3
        /ideal_final_s2_centered_moment4
        /ideal_final_s2_centered_moment8
        hm1 h0 h1 hmean.
split.
+ field; trivial.
+ split.
  + field; trivial.
  + split.
    + field; trivial.
    + split.
      + field; trivial.
      + split.
        + field; trivial.
        + split.
          + field; trivial.
          + field; trivial.
qed.

lemma mean_mod2 b a :
  ideal_final_s2_class_mod2 b a =>
  ideal_final_s2_mean b a = 0%r.
proof.
move=> hclass.
have [hm1 [h0 h1]] := math_output_mod2_triple b a hclass.
rewrite /ideal_final_s2_mean hm1 h0 h1.
ring.
qed.

lemma moments_mod2 b a :
  ideal_final_s2_class_mod2 b a =>
  ideal_final_s2_raw_moment2 b a = 8%r / 3%r /\
  ideal_final_s2_raw_moment4 b a = 32%r / 3%r /\
  ideal_final_s2_raw_moment8 b a = 512%r / 3%r /\
  ideal_final_s2_centered_moment2 b a = 8%r / 3%r /\
  ideal_final_s2_centered_moment3 b a = 0%r /\
  ideal_final_s2_centered_moment4 b a = 32%r / 3%r /\
  ideal_final_s2_centered_moment8 b a = 512%r / 3%r.
proof.
move=> hclass.
have hmean := mean_mod2 b a hclass.
have [hm1 [h0 h1]] := math_output_mod2_triple b a hclass.
rewrite /ideal_final_s2_raw_moment2 /ideal_final_s2_raw_moment4
        /ideal_final_s2_raw_moment8
        /ideal_final_s2_centered_moment2
        /ideal_final_s2_centered_moment3
        /ideal_final_s2_centered_moment4
        /ideal_final_s2_centered_moment8
        hm1 h0 h1 hmean.
split.
+ field; trivial.
+ split.
  + field; trivial.
  + split.
    + field; trivial.
    + split.
      + field; trivial.
      + split.
        + field; trivial.
        + split.
          + field; trivial.
          + field; trivial.
qed.

lemma mean_mod3 b a :
  ideal_final_s2_class_mod3 b a =>
  ideal_final_s2_mean b a = 1%r / 3%r.
proof.
move=> hclass.
have [hm1 [h0 h1]] := math_output_mod3_triple b a hclass.
rewrite /ideal_final_s2_mean hm1 h0 h1.
ring.
qed.

lemma moments_mod3 b a :
  ideal_final_s2_class_mod3 b a =>
  ideal_final_s2_raw_moment2 b a = 1%r /\
  ideal_final_s2_raw_moment4 b a = 1%r /\
  ideal_final_s2_raw_moment8 b a = 1%r /\
  ideal_final_s2_centered_moment2 b a = 8%r / 9%r /\
  ideal_final_s2_centered_moment3 b a = -16%r / 27%r /\
  ideal_final_s2_centered_moment4 b a = 32%r / 27%r /\
  ideal_final_s2_centered_moment8 b a = 22016%r / 6561%r.
proof.
move=> hclass.
have hmean := mean_mod3 b a hclass.
have [hm1 [h0 h1]] := math_output_mod3_triple b a hclass.
rewrite /ideal_final_s2_raw_moment2 /ideal_final_s2_raw_moment4
        /ideal_final_s2_raw_moment8
        /ideal_final_s2_centered_moment2
        /ideal_final_s2_centered_moment3
        /ideal_final_s2_centered_moment4
        /ideal_final_s2_centered_moment8
        hm1 h0 h1 hmean.
split.
+ field; trivial.
+ split.
  + field; trivial.
  + split.
    + field; trivial.
    + split.
      + field; trivial.
      + split.
        + field; trivial.
        + split.
          + field; trivial.
          + field; trivial.
qed.

lemma ideal_final_s2_mean_abs_le_one_third b a :
  context_valid b a =>
  `|ideal_final_s2_mean b a| <= 1%r / 3%r.
proof.
move=> _.
have hexh := ideal_final_s2_class_exhaustive b a.
move: hexh => [h0 | [h1 | [h2 | [h3 | [h4 | h5]]]]].
+ rewrite (mean_rho0 b a h0) normrN.
   by rewrite ger0_norm 1:/#.
+ rewrite (mean_rhoq1 b a h1).
   by rewrite ger0_norm 1:/#.
+ rewrite (mean_mod0 b a h2).
   rewrite normr0; smt().
+ rewrite (mean_mod1 b a h3) normrN.
   by rewrite ger0_norm 1:/#.
+ rewrite (mean_mod2 b a h4).
   rewrite normr0; smt().
rewrite (mean_mod3 b a h5).
by rewrite ger0_norm 1:/#.
qed.

lemma ideal_final_s2_moment_bounds b a :
  context_valid b a =>
  ideal_final_s2_raw_moment2 b a <= 8%r / 3%r /\
  ideal_final_s2_centered_moment2 b a <= 8%r / 3%r /\
  ideal_final_s2_raw_moment4 b a <= 32%r / 3%r /\
  ideal_final_s2_centered_moment4 b a <= 32%r / 3%r /\
  ideal_final_s2_raw_moment8 b a <= 512%r / 3%r /\
  ideal_final_s2_centered_moment8 b a <= 512%r / 3%r.
proof.
move=> _.
have hexh := ideal_final_s2_class_exhaustive b a.
move: hexh => [h0 | [h1 | [h2 | [h3 | [h4 | h5]]]]].
+ have hm := moments_rho0 b a h0.
   move: hm; smt().
+ have hm := moments_rhoq1 b a h1.
   move: hm; smt().
+ have hm := moments_mod0 b a h2.
   move: hm; smt().
+ have hm := moments_mod1 b a h3.
   move: hm; smt().
+ have hm := moments_mod2 b a h4.
   move: hm; smt().
have hm := moments_mod3 b a h5.
move: hm; smt().
qed.

lemma ideal_final_s2_mean_zero_false_mod1 b a :
  ideal_final_s2_class_mod1 b a =>
  ideal_final_s2_mean b a = -1%r / 3%r /\
  ideal_final_s2_centered_moment3 b a = 16%r / 27%r.
proof.
move=> hclass.
split.
+ exact (mean_mod1 b a hclass).
have hm := moments_mod1 b a hclass.
move: hm; smt().
qed.

lemma ideal_final_s2_context_counterexample :
  context_valid W32.zero W32.one /\
  ideal_final_s2_class_mod1 W32.zero W32.one /\
  ideal_final_s2_mean W32.zero W32.one = -1%r / 3%r /\
  ideal_final_s2_centered_moment3 W32.zero W32.one = 16%r / 27%r.
proof.
have hz : W32.to_sint W32.zero = 0.
+ rewrite W32.to_sintE /W32.smod /=; trivial.
have hu : W32.to_uint W32.one = 1 by done.
have hctx : context_valid W32.zero W32.one.
+ rewrite /context_valid /Fq.bw32 hz hu
          /KeygenM23FinalizeSemantics.q /=.
   smt().
have hrho :
    rho W32.zero W32.one = 1.
+ rewrite /rho hz hu.
   rewrite /KeygenM23FinalizeSemantics.q.
   trivial.
have hclass : ideal_final_s2_class_mod1 W32.zero W32.one.
+ rewrite ideal_final_s2_class_mod1E hrho /KeygenM23FinalizeSemantics.q.
   split; first smt().
   trivial.
have hmom := ideal_final_s2_mean_zero_false_mod1 W32.zero W32.one hclass.
move: hmom => [hmean hskew].
split.
+ exact hctx.
+ split.
  + exact hclass.
  + split.
    + exact hmean.
    + exact hskew.
qed.

end Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.
