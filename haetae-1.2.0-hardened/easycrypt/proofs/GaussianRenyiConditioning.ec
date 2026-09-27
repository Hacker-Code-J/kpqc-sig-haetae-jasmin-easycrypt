require import AllCore List Real Distr DBool Finite RealSeries StdRing StdOrder.
require import FiniteExpectationError.
import RField RealOrder.

op grk_relative_error : real = 84%r/281474976710656%r.
op grk_delta : real = 1%r/549755813888%r.

op grk_pair ['a 'b] (d : 'a distr) (kernel : 'a -> real) (output : 'a -> 'b) :
    ('b * bool) distr =
  dlet d (fun x => dmap (Biased.dbiased (kernel x)) (fun accepted => (output x,accepted))).
op grk_output ['a 'b] (d : 'a distr) (kernel : 'a -> real) (output : 'a -> 'b) : 'b distr =
  dmap (dcond (grk_pair d kernel output) (fun (r : 'b * bool) => r.`2))
    (fun (r : 'b * bool) => r.`1).
op grk_normalizer ['a] (d : 'a distr) (kernel : 'a -> real) : real = E d kernel.
op grk_mass ['a 'b] (d : 'a distr) (kernel : 'a -> real) (output : 'a -> 'b) (y : 'b) : real =
  E d (fun x => kernel x*b2r (output x=y)).
op grk_kernel_conditions ['a] (d : 'a distr) (a b : 'a -> real) : bool =
  forall x, x \in d =>
    0%r<=a x<=1%r /\ 0%r<b x<=1%r /\
    `|a x-b x|<=grk_relative_error*b x.

lemma grk_constants :
  0%r<grk_relative_error<1%r/2%r /\ 0%r<grk_delta<1%r.
proof. rewrite /grk_relative_error /grk_delta; smt(). qed.

lemma grk_error_margin :
  2%r*grk_relative_error/(1%r-grk_relative_error)<=4%r*grk_relative_error /\
  4%r*grk_relative_error<grk_delta.
proof. rewrite /grk_relative_error /grk_delta; smt(). qed.

lemma grk_ratio_margin :
  1%r+grk_relative_error <= (1%r+grk_delta)*(1%r-grk_relative_error).
proof. rewrite /grk_relative_error /grk_delta; smt(). qed.

lemma grk_finite_map ['a 'b] (d : 'a distr) (f : 'a -> 'b) :
  is_finite (Distr.support d) => is_finite (Distr.support (dmap d f)).
proof.
  move=> hd; rewrite /dmap; apply finite_dlet => // x hx; exact (finite_dunit (f x)).
qed.

lemma grk_bool_finite (d : bool distr) : is_finite (Distr.support d).
proof. apply mkfinite; exists [true;false] => b _; by case b. qed.

lemma grk_pair_finite ['a 'b] (d : 'a distr) (kernel : 'a -> real) (output : 'a -> 'b) :
  is_finite (Distr.support d) => is_finite (Distr.support (grk_pair d kernel output)).
proof.
  move=> hd; rewrite /grk_pair; apply finite_dlet => // x hx.
  apply grk_finite_map; exact (grk_bool_finite (Biased.dbiased (kernel x))).
qed.

lemma grk_output_finite ['a 'b] (d : 'a distr) (kernel : 'a -> real) (output : 'a -> 'b) :
  is_finite (Distr.support d) => is_finite (Distr.support (grk_output d kernel output)).
proof.
  move=> hd; rewrite /grk_output; apply grk_finite_map; apply finite_dcond.
  exact (grk_pair_finite d kernel output hd).
qed.

lemma grk_pair_ll ['a 'b] (d : 'a distr) (kernel : 'a -> real) (output : 'a -> 'b) :
  is_lossless d => is_lossless (grk_pair d kernel output).
proof.
  move=> hd; rewrite /grk_pair; apply dlet_ll => // x hx.
  apply dmap_ll; exact (Biased.dbiased_ll (kernel x)).
qed.

lemma grk_pair_joint ['a 'b] (d : 'a distr) (kernel : 'a -> real)
    (output : 'a -> 'b) (event : 'b -> bool) :
  (forall x, x \in d => 0%r<=kernel x<=1%r) =>
  mu (grk_pair d kernel output) (fun (r : 'b * bool) => r.`2 /\ event r.`1) =
    E d (fun x => kernel x*b2r (event (output x))).
proof.
  move=> hk; rewrite /grk_pair dletE /E; apply RealSeries.eq_sum => x /=.
  case (x \in d) => hx.
  + rewrite dmapE /(\o) /= Biased.dbiasedE /= (Biased.clamp_id (kernel x) (hk x hx)).
    rewrite /b2r; case (event (output x)) => he /=; smt().
  have hz : mu1 d x=0%r by move: hx; rewrite supportPn.
  by rewrite hz /=.
qed.

lemma grk_pair_acceptance ['a 'b] (d : 'a distr) (kernel : 'a -> real)
    (output : 'a -> 'b) :
  (forall x, x \in d => 0%r<=kernel x<=1%r) =>
  mu (grk_pair d kernel output) (fun (r : 'b * bool) => r.`2)=grk_normalizer d kernel.
proof.
  move=> hk; have h := grk_pair_joint d kernel output (fun _ => true) hk.
  by move: h; rewrite /b2r /grk_normalizer /=.
qed.

lemma grk_output_mass ['a 'b] (d : 'a distr) (kernel : 'a -> real)
    (output : 'a -> 'b) (y : 'b) :
  (forall x, x \in d => 0%r<=kernel x<=1%r) =>
  mu1 (grk_output d kernel output) y = grk_mass d kernel output y/grk_normalizer d kernel.
proof.
  move=> hk; rewrite /grk_output dmapE dcondE /predI /(\o) /=.
  rewrite (grk_pair_joint d kernel output (pred1 y) hk)
    (grk_pair_acceptance d kernel output hk).
  by rewrite /grk_mass /pred1.
qed.

lemma grk_normalizer_positive ['a] (d : 'a distr) (kernel : 'a -> real) :
  is_finite (Distr.support d) => is_lossless d =>
  (forall x, x \in d => 0%r<kernel x) => 0%r<grk_normalizer d kernel.
proof.
  move=> hf hd hk.
  have hn : mu d predT<>0%r by rewrite hd.
  have [x [hx _]] := neq0_mu d predT hn.
  have hp : 0%r<mu1 d x by have h := ge0_mu d (pred1 x); have h0 := supportP d x; smt().
  have h := finite_expectation_le d (fun z => if z=x then kernel x else 0%r) kernel hf _.
  + move=> z hz; have hpos := hk z hz; case (z=x); smt().
  rewrite expC_cond -/(pred1 x) in h.
  have hprod : 0%r<kernel x*mu1 d x by apply mulr_gt0; [exact (hk x hx)|exact hp].
  rewrite /grk_normalizer; smt().
qed.

lemma grk_output_ll ['a 'b] (d : 'a distr) (kernel : 'a -> real) (output : 'a -> 'b) :
  is_finite (Distr.support d) => is_lossless d =>
  (forall x, x \in d => 0%r<kernel x<=1%r) => is_lossless (grk_output d kernel output).
proof.
  move=> hf hd hk.
  have hr : forall x, x \in d => 0%r<=kernel x<=1%r by move=> x hx; have h := hk x hx; smt().
  have hp : forall x, x \in d => 0%r<kernel x by move=> x hx; have h := hk x hx; smt().
  rewrite /grk_output; apply dmap_ll; apply dcond_ll.
  rewrite (grk_pair_acceptance d kernel output hr).
  exact (grk_normalizer_positive d kernel hf hd hp).
qed.

lemma grk_kernel_bounds ['a] (d : 'a distr) (a b : 'a -> real) x :
  grk_kernel_conditions d a b => x \in d =>
  0%r<a x /\ (1%r-grk_relative_error)*b x<=a x<=(1%r+grk_relative_error)*b x.
proof.
  move=> hc hx; have [ha [hb he]] := hc x hx.
  move: he; rewrite ler_norml => he.
  have [heps _] := grk_constants.
  move: ha hb he heps; rewrite /grk_relative_error; smt().
qed.

lemma grk_mass_nonnegative ['a 'b] (d : 'a distr) (kernel : 'a -> real)
    (output : 'a -> 'b) (y : 'b) :
  (forall x, x \in d => 0%r<=kernel x) => 0%r<=grk_mass d kernel output y.
proof.
  move=> hk; rewrite /grk_mass; apply exp_ge0 => x hx.
  apply mulr_ge0; [exact (hk x hx)|exact (b2r_ge0 (output x=y))].
qed.

lemma grk_mass_bounds ['a 'b] (d : 'a distr) (a b : 'a -> real) (output : 'a -> 'b) y :
  is_finite (Distr.support d) => grk_kernel_conditions d a b =>
  (1%r-grk_relative_error)*grk_mass d b output y <= grk_mass d a output y <=
    (1%r+grk_relative_error)*grk_mass d b output y.
proof.
  move=> hf hc.
  have hlo := finite_expectation_le d
    (fun x => (1%r-grk_relative_error)*(b x*b2r (output x=y)))
    (fun x => a x*b2r (output x=y)) hf _.
  + move=> x hx; have [_ hb] := grk_kernel_bounds d a b x hc hx.
    rewrite /b2r; case (output x=y); smt().
  have hhi := finite_expectation_le d
    (fun x => a x*b2r (output x=y))
    (fun x => (1%r+grk_relative_error)*(b x*b2r (output x=y))) hf _.
  + move=> x hx; have [_ hb] := grk_kernel_bounds d a b x hc hx.
    rewrite /b2r; case (output x=y); smt().
  move: hlo; rewrite expZ => hlo.
  move: hhi; rewrite expZ => hhi.
  rewrite /grk_mass; split; first exact hlo.
  by move=> _; exact hhi.
qed.

lemma grk_normalizer_bounds ['a] (d : 'a distr) (a b : 'a -> real) :
  is_finite (Distr.support d) => grk_kernel_conditions d a b =>
  (1%r-grk_relative_error)*grk_normalizer d b <= grk_normalizer d a <=
    (1%r+grk_relative_error)*grk_normalizer d b.
proof.
  move=> hf hc; have h := grk_mass_bounds d a b (fun _ => true) true hf hc.
  by move: h; rewrite /grk_mass /grk_normalizer /b2r /=.
qed.

lemma grk_div_comparison (x y u v : real) : 0%r<u => 0%r<v =>
  (x/u<=y/v)=(x*v<=y*u).
proof.
  move=> hu hv; rewrite ler_pdivr_mulr 1:hu.
  have he : y/v*u=(y*u)/v by field; smt().
  by rewrite he ler_pdivl_mulr 1:hv.
qed.

(* Numerators may vanish. Only the two total acceptance masses are
   divided by; their strict positivity is a separately proved premise. *)
lemma grk_normalized_bounds (m n za zb : real) :
  0%r<za => 0%r<zb => 0%r<=m => 0%r<=n =>
  (1%r-grk_relative_error)*n<=m<=(1%r+grk_relative_error)*n =>
  (1%r-grk_relative_error)*zb<=za<=(1%r+grk_relative_error)*zb =>
  ((1%r-grk_delta)*(n/zb)<=m/za<=(1%r+grk_delta)*(n/zb)) /\
  ((1%r-grk_delta)*(m/za)<=n/zb<=(1%r+grk_delta)*(m/za)).
proof.
  move=> hza hzb hm hn [hml hmh] [hzl hzh].
  have hzb0 : 0%r<=zb by smt().
  have hC : 0%r<=1%r+grk_delta by have [_ h] := grk_constants; smt().
  have hnzb : 0%r<=n*zb by apply mulr_ge0.
  have hmid := ler_wpmul2r (n*zb) hnzb _ _ grk_ratio_margin.
  have hmb := ler_wpmul2r zb hzb0 _ _ hmh.
  have hnza := ler_wpmul2l n hn _ _ hzl.
  have hnzac := ler_wpmul2l (1%r+grk_delta) hC _ _ hnza.
  have hcross1 : m*zb<=((1%r+grk_delta)*n)*za by smt().
  have hnzahi := ler_wpmul2l n hn _ _ hzh.
  have hmzb := ler_wpmul2r zb hzb0 _ _ hml.
  have hmzbc := ler_wpmul2l (1%r+grk_delta) hC _ _ hmzb.
  have hcross2 : n*za<=((1%r+grk_delta)*m)*zb by smt().
  have hu : m/za<=(1%r+grk_delta)*(n/zb).
  + have he : (1%r+grk_delta)*(n/zb)=((1%r+grk_delta)*n)/zb by field; smt().
    rewrite he (grk_div_comparison _ _ za zb hza hzb); exact hcross1.
  have hv : n/zb<=(1%r+grk_delta)*(m/za).
  + have he : (1%r+grk_delta)*(m/za)=((1%r+grk_delta)*m)/za by field; smt().
    rewrite he (grk_div_comparison _ _ zb za hzb hza); exact hcross2.
  have hp : 0%r<=m/za by apply divr_ge0; smt().
  have hq : 0%r<=n/zb by apply divr_ge0; smt().
  move: hu hv hp hq; rewrite /grk_delta; smt().
qed.

lemma grk_positive_ranges ['a] (d : 'a distr) (a b : 'a -> real) :
  grk_kernel_conditions d a b =>
  (forall x, x \in d => 0%r<a x<=1%r) /\
  (forall x, x \in d => 0%r<b x<=1%r).
proof.
  move=> hc; split => x hx.
  + have [hpos _] := grk_kernel_bounds d a b x hc hx.
    have [hr _] := hc x hx; smt().
  have [_ [hr _]] := hc x hx; exact hr.
qed.

lemma grk_outputs_ll ['a 'b] (d : 'a distr) (a b : 'a -> real) (output : 'a -> 'b) :
  is_finite (Distr.support d) => is_lossless d => grk_kernel_conditions d a b =>
  is_lossless (grk_output d a output) /\ is_lossless (grk_output d b output).
proof.
  move=> hf hd hc; have [ha hb] := grk_positive_ranges d a b hc.
  split; first exact (grk_output_ll d a output hf hd ha).
  exact (grk_output_ll d b output hf hd hb).
qed.

lemma grk_output_bounds ['a 'b] (d : 'a distr) (a b : 'a -> real) (output : 'a -> 'b) y :
  is_finite (Distr.support d) => is_lossless d => grk_kernel_conditions d a b =>
  ((1%r-grk_delta)*mu1 (grk_output d b output) y <= mu1 (grk_output d a output) y <=
    (1%r+grk_delta)*mu1 (grk_output d b output) y) /\
  ((1%r-grk_delta)*mu1 (grk_output d a output) y <= mu1 (grk_output d b output) y <=
    (1%r+grk_delta)*mu1 (grk_output d a output) y).
proof.
  move=> hf hd hc; have [ha hb] := grk_positive_ranges d a b hc.
  have hap : forall x, x \in d => 0%r<a x by move=> x hx; have h := ha x hx; smt().
  have hbp : forall x, x \in d => 0%r<b x by move=> x hx; have h := hb x hx; smt().
  have har : forall x, x \in d => 0%r<=a x<=1%r by move=> x hx; have h := ha x hx; smt().
  have hbr : forall x, x \in d => 0%r<=b x<=1%r by move=> x hx; have h := hb x hx; smt().
  have han : forall x, x \in d => 0%r<=a x by move=> x hx; have h := ha x hx; smt().
  have hbn : forall x, x \in d => 0%r<=b x by move=> x hx; have h := hb x hx; smt().
  rewrite (grk_output_mass d a output y har) (grk_output_mass d b output y hbr).
  exact (grk_normalized_bounds _ _ _ _
    (grk_normalizer_positive d a hf hd hap) (grk_normalizer_positive d b hf hd hbp)
    (grk_mass_nonnegative d a output y han) (grk_mass_nonnegative d b output y hbn)
    (grk_mass_bounds d a b output y hf hc) (grk_normalizer_bounds d a b hf hc)).
qed.

lemma grk_output_support ['a 'b] (d : 'a distr) (a b : 'a -> real) (output : 'a -> 'b) y :
  is_finite (Distr.support d) => is_lossless d => grk_kernel_conditions d a b =>
  (y \in grk_output d a output)=(y \in grk_output d b output).
proof.
  move=> hf hd hc; have h := grk_output_bounds d a b output y hf hd hc.
  have hp := ge0_mu (grk_output d a output) (pred1 y).
  have hq := ge0_mu (grk_output d b output) (pred1 y).
  rewrite !supportP; smt().
qed.
