require import AllCore IntDiv List Real StdRing StdOrder StdBigop.
require import ExpIntervalSpec.
import RField RealOrder.

(* Generic certificate bridges. All numerical requirements are explicit;
   no sampler, implementation table, or analytic assumption is imported. *)
lemma gi_ratio_interval_sound (D R : int) (a z p : ei_interval) (x Z : real) :
  ei_contains D a x => ei_contains D z Z =>
  0 < z.`1 => 0 < R => 0 <= p.`1 => 0 <= p.`2 =>
  p.`1 * z.`2 <= R * a.`1 => R * a.`2 <= p.`2 * z.`1 =>
  ei_contains R p (x / Z).
proof.
  move=> ha hz hc hR hp0 hp1 hlo hhi.
  rewrite /ei_contains in ha.
  rewrite /ei_contains in hz.
  have hDr : 0%r < D%r by rewrite lt_fromint; smt().
  have hRr : 0%r < R%r by rewrite lt_fromint.
  have hcr : 0%r < z.`1%r by rewrite lt_fromint.
  have hp0r : 0%r <= p.`1%r by rewrite le_fromint.
  have hp1r : 0%r <= p.`2%r by rewrite le_fromint.
  have hZ : 0%r < Z by smt().
  have hx : 0%r <= x by smt().
  have hlr : p.`1%r * z.`2%r <= R%r * a.`1%r.
  + by rewrite -!fromintM le_fromint.
  have hhr : R%r * a.`2%r <= p.`2%r * z.`1%r.
  + by rewrite -!fromintM le_fromint.
  have hl : p.`1%r * Z <= R%r * x by smt().
  have hh : R%r * x <= p.`2%r * Z by smt().
  have hquot : Z * (x / Z) = x by field; smt().
  have hnonneg : 0%r <= x / Z by apply divr_ge0; smt().
  rewrite /ei_contains; smt().
qed.

lemma gi_ratio_interval_division (D R : int) (a z p : ei_interval) (x Z : real) :
  ei_contains D a x => ei_contains D z Z =>
  0 < z.`1 => 0 < R => 0 <= p.`1 => 0 <= p.`2 =>
  p.`1 * z.`2 <= R * a.`1 => R * a.`2 <= p.`2 * z.`1 =>
  p.`1%r / R%r <= x / Z /\ x / Z <= p.`2%r / R%r.
proof.
  move=> ha hz hc hR hp0 hp1 hlo hhi.
  have h := gi_ratio_interval_sound D R a z p x Z ha hz hc hR hp0 hp1 hlo hhi.
  have hRr : 0%r < R%r by rewrite lt_fromint.
  have hl : R%r * (p.`1%r / R%r) = p.`1%r by field; smt().
  have hh : R%r * (p.`2%r / R%r) = p.`2%r by field; smt().
  move: h; rewrite /ei_contains; smt().
qed.

(* The analytic tail theorem supplies w/(1-r). This lemma only converts its
   interval inputs and one integer inequality into an outward upper bound. *)
lemma gi_geometric_tail_interval_sound (D tail_units : int)
    (wb rb : ei_interval) (w r : real) :
  ei_contains D wb w => ei_contains D rb r =>
  rb.`2 < D => 0 <= tail_units =>
  wb.`2 * D <= tail_units * (D - rb.`2) =>
  ei_contains D (0, tail_units) (w / (1%r - r)).
proof.
  move=> hw hr hrhi ht hcheck.
  rewrite /ei_contains in hw.
  rewrite /ei_contains in hr.
  have hD : 0 < D by smt().
  have hDr : 0%r < D%r by rewrite lt_fromint.
  have ht0 : 0%r <= tail_units%r by rewrite le_fromint.
  have hrhir : rb.`2%r < D%r by rewrite lt_fromint.
  have hgap : 0%r < 1%r-r by smt().
  have hcheckr : wb.`2%r * D%r <= tail_units%r * (D%r - rb.`2%r).
  + by rewrite -fromintB -!fromintM le_fromint.
  have hupper : D%r * w <= tail_units%r * (1%r-r) by smt().
  have hquot : (1%r-r) * (w / (1%r-r)) = w by field; smt().
  have hnonneg : 0%r <= w / (1%r-r) by apply divr_ge0; smt().
  rewrite /ei_contains /=; smt().
qed.

lemma gi_geometric_tail_upper (D tail_units : int)
    (wb rb : ei_interval) (w r : real) :
  ei_contains D wb w => ei_contains D rb r =>
  rb.`2 < D => 0 <= tail_units =>
  wb.`2 * D <= tail_units * (D - rb.`2) =>
  0%r <= w / (1%r-r) /\ w / (1%r-r) <= tail_units%r / D%r.
proof.
  move=> hw hr hrhi ht hcheck.
  have h := gi_geometric_tail_interval_sound D tail_units wb rb w r hw hr hrhi ht hcheck.
  have hD : 0 < D by move: hw; rewrite /ei_contains; smt().
  have hDr : 0%r < D%r by rewrite lt_fromint.
  have hdiv : D%r * (tail_units%r / D%r) = tail_units%r by field; smt().
  move: h; rewrite /ei_contains /=; smt().
qed.

lemma gi_interval_add_sound (D : int) (a b : ei_interval) (x y : real) :
  ei_contains D a x => ei_contains D b y =>
  ei_contains D (a.`1 + b.`1, a.`2 + b.`2) (x+y).
proof.
  rewrite /ei_contains /= !fromintD; smt().
qed.

lemma gi_prefix_sum_cast (f : int -> int) (n : int) :
  (Bigint.BIA.bigi predT f 0 n)%r =
    Bigreal.BRA.bigi predT (fun i => (f i)%r) 0 n.
proof. exact (Bigreal.sumr_ofint predT f (range 0 n)). qed.

(* n is exclusive: n=256 sums indices 0,...,255, even when the supplied
   certificate also contains the endpoint at index 256. *)
lemma gi_prefix_sum_interval_sound (D n : int)
    (bounds : int -> ei_interval) (f : int -> real) :
  0 < D => 0 <= n =>
  (forall i, 0 <= i < n => ei_contains D (bounds i) (f i)) =>
  ei_contains D
    (Bigint.BIA.bigi predT (fun i => (bounds i).`1) 0 n,
     Bigint.BIA.bigi predT (fun i => (bounds i).`2) 0 n)
    (Bigreal.BRA.bigi predT f 0 n).
proof.
  move=> hD hn; elim: n hn => [|n hn ih] hterms.
  + rewrite !Bigint.BIA.big_geq 1..2:// Bigreal.BRA.big_geq 1://.
    by rewrite /ei_contains /=; smt().
  have hprevious : forall i, 0 <= i < n => ei_contains D (bounds i) (f i)
    by move=> i hi; apply hterms; smt().
  have hp := ih hprevious.
  have hnth := hterms n _; first smt().
  rewrite !Bigint.BIA.big_int_recr 1..2:hn Bigreal.BRA.big_int_recr 1:hn /=.
  exact (gi_interval_add_sound D _ _ _ _ hp hnth).
qed.

lemma gi_weight_prefix_sum_interval_sound (D n : int)
    (chain : ei_weight_state list) (f : int -> real) :
  0 < D => 0 <= n <= size chain =>
  (forall i, 0 <= i < n => ei_contains D (nth witness chain i).`1 (f i)) =>
  ei_contains D
    (Bigint.BIA.bigi predT (fun i => (nth witness chain i).`1.`1) 0 n,
     Bigint.BIA.bigi predT (fun i => (nth witness chain i).`1.`2) 0 n)
    (Bigreal.BRA.bigi predT f 0 n).
proof.
  move=> hD hn hterms.
  have hn0 : 0 <= n by smt().
  exact (gi_prefix_sum_interval_sound D n (fun i => (nth witness chain i).`1) f hD hn0 hterms).
qed.
