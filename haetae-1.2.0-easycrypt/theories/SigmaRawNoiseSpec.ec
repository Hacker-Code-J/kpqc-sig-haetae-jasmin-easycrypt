require import AllCore IntDiv List Distr DInterval StdOrder.
import IntOrder RealOrder RField.

(* Explicit ideal 72-bit noise experiment.  The CDT integer is held fixed;
   this definition does not identify a concrete SHAKE stream with this law. *)
op sr_noise_uniform : int distr = DInterval.dinter 0 4722366482869645213695.

op sr_noise_mismatch (x y : int) : bool = x = 0 /\ 1 <= y < 32768.

op sr_noise_raw_factor (x y : int) : real =
  if y + 4722366482869645213696 * x = 0 then 1%r / 2%r else 1%r.

op sr_noise_rounded_factor (x y : int) : real =
  if x = 0 /\ 0 <= y < 32768 then 1%r / 2%r else 1%r.

lemma sr_noise_uniform_ll : is_lossless sr_noise_uniform.
proof. rewrite /sr_noise_uniform; apply DInterval.dinter_ll; trivial. qed.

lemma sr_noise_uniform_support y :
  (y \in sr_noise_uniform) = (0 <= y < 4722366482869645213696).
proof. rewrite /sr_noise_uniform DInterval.supp_dinter; smt(). qed.

lemma sr_noise_raw_zero x y : 0 <= y < 4722366482869645213696 =>
  (y + 4722366482869645213696 * x = 0) = (x = 0 /\ y = 0).
proof. smt(). qed.

lemma sr_noise_factor_difference x y : 0 <= y < 4722366482869645213696 =>
  sr_noise_raw_factor x y - sr_noise_rounded_factor x y =
    if sr_noise_mismatch x y then 1%r / 2%r else 0%r.
proof.
move=> hy.
rewrite /sr_noise_raw_factor /sr_noise_rounded_factor /sr_noise_mismatch
  sr_noise_raw_zero 1:hy.
smt().
qed.

lemma sr_noise_factor_absolute_difference x y : 0 <= y < 4722366482869645213696 =>
  `|sr_noise_rounded_factor x y - sr_noise_raw_factor x y| =
    if sr_noise_mismatch x y then 1%r / 2%r else 0%r.
proof.
move=> hy.
rewrite distrC sr_noise_factor_difference 1:hy.
case (sr_noise_mismatch x y); smt().
qed.

lemma sr_noise_small_nonzero_count :
  count (fun y => 1 <= y < 32768) (range 0 4722366482869645213696) = 32767.
proof.
rewrite (range_ltn 0 4722366482869645213696) 1:// /=.
rewrite (range_cat 32768 1 4722366482869645213696) 1:// 1:// count_cat.
have hh : count (fun y => 1 <= y < 32768) (range 1 32768) = 32767.
+ rewrite count_predT_eq_in.
  - by move=> y; rewrite mem_range.
  by rewrite size_range /max /=.
have ht : count (fun y => 1 <= y < 32768) (range 32768 4722366482869645213696) = 0.
+ apply count_pred0_eq_in => y; rewrite mem_range; smt().
by rewrite hh ht /=.
qed.

lemma sr_noise_mismatch_probability x :
  mu sr_noise_uniform (fun y => sr_noise_mismatch x y) =
    if x = 0 then 32767%r / 4722366482869645213696%r else 0%r.
proof.
rewrite /sr_noise_uniform DInterval.dinterE /max /= size_filter /sr_noise_mismatch.
case (x = 0) => hx.
+ by rewrite sr_noise_small_nonzero_count.
by rewrite count_pred0_eq 1:/#.
qed.

lemma sr_noise_half_effect x :
  (1%r / 2%r) * mu sr_noise_uniform (fun y => sr_noise_mismatch x y) =
    if x = 0 then 32767%r / 9444732965739290427392%r else 0%r.
proof.
rewrite sr_noise_mismatch_probability.
case (x = 0); try field; trivial.
qed.

lemma sr_noise_half_effect_lt x :
  (1%r / 2%r) * mu sr_noise_uniform (fun y => sr_noise_mismatch x y) <
    1%r / 288230376151711744%r.
proof. rewrite sr_noise_half_effect; case (x = 0); smt(). qed.

lemma sr_noise_factor_gap_expectation x :
  Distr.E sr_noise_uniform (fun y => sr_noise_raw_factor x y - sr_noise_rounded_factor x y) =
    if x = 0 then 32767%r / 9444732965739290427392%r else 0%r.
proof.
have he : Distr.E sr_noise_uniform
    (fun y => sr_noise_raw_factor x y - sr_noise_rounded_factor x y) =
    Distr.E sr_noise_uniform (fun y => if sr_noise_mismatch x y then 1%r / 2%r else 0%r).
+ apply eq_exp => y; rewrite sr_noise_uniform_support => hy.
  exact (sr_noise_factor_difference x y hy).
by rewrite he expC_cond sr_noise_half_effect.
qed.

lemma sr_noise_factor_absolute_expectation x :
  Distr.E sr_noise_uniform
    (fun y => `|sr_noise_rounded_factor x y - sr_noise_raw_factor x y|) =
    if x = 0 then 32767%r / 9444732965739290427392%r else 0%r.
proof.
have he : Distr.E sr_noise_uniform
    (fun y => `|sr_noise_rounded_factor x y - sr_noise_raw_factor x y|) =
    Distr.E sr_noise_uniform (fun y => if sr_noise_mismatch x y then 1%r / 2%r else 0%r).
+ apply eq_exp => y; rewrite sr_noise_uniform_support => hy.
  exact (sr_noise_factor_absolute_difference x y hy).
by rewrite he expC_cond sr_noise_half_effect.
qed.

lemma sr_noise_factor_absolute_expectation_lt x :
  Distr.E sr_noise_uniform
    (fun y => `|sr_noise_rounded_factor x y - sr_noise_raw_factor x y|) <
    1%r / 288230376151711744%r.
proof. rewrite sr_noise_factor_absolute_expectation; case (x = 0); smt(). qed.
