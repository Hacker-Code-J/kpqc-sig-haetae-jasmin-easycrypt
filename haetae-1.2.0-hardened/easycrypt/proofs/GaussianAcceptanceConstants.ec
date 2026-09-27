require import AllCore Real StdRing StdOrder.
require import ExpIntervalSpec HalfGaussianSpec CDTGaussianCertificate
  CDTGaussianEnclosure.
import RField RealOrder HalfGaussianSpec.

(* Reuse the previously certified enclosure; no new numerical data or
   assumption about the infinite Gaussian normalizer is introduced. *)
lemma gac_normalizer_certificate :
  0 < gi_scale /\ 41*gi_scale <= 2*gi_normalizer_bounds.`1.
proof. by rewrite /gi_scale /gi_normalizer_bounds /=. qed.

lemma gac_normalizer_lower : 41%r/2%r <= hg16_normalizer.
proof.
  have [hscale hbound] := gac_normalizer_certificate.
  have hs : 0%r < gi_scale%r by rewrite lt_fromint.
  have hb : 41%r*gi_scale%r <= 2%r*gi_normalizer_bounds.`1%r
    by rewrite -!fromintM le_fromint.
  have h := gi_normalizer_interval.
  move: h; rewrite /ei_contains; smt().
qed.

lemma gac_normalizer_positive : 0%r < hg16_normalizer.
proof. have h := gac_normalizer_lower; smt(). qed.

lemma gac_acceptance_margin :
  19%r/20%r < 951%r/1000%r - 1%r/8796093022208%r.
proof. smt(). qed.
