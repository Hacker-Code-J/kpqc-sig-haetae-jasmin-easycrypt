require import AllCore StdRing StdOrder.
import RField RealOrder.

(* The numerator and normalizer may each change by epsilon. The bound
   keeps the first normalizer p explicit and uses only real arithmetic. *)
lemma conditional_ratio_error (a b p q epsilon : real) :
  0%r < p => 0%r < q => 0%r <= a <= p => 0%r <= b <= q =>
  `|a-b| <= epsilon => `|p-q| <= epsilon =>
  `|a/p - b/q| <= 2%r * epsilon / p.
proof.
  move=> hp hq ha [hb0 hbq] hab hpq.
  have hepsilon : 0%r <= epsilon by have h := normr_ge0 (a-b); smt().
  have hq0 : 0%r <= q by smt().
  have hqp : `|q-p| <= epsilon by rewrite distrC.
  have hcross : a*q - b*p = (a-b)*q + b*(q-p) by ring.
  have htriangle := ler_norm_add ((a-b)*q) (b*(q-p)).
  rewrite -hcross !normrM (ger0_norm q hq0) (ger0_norm b hb0) in htriangle.
  have hleft := ler_wpmul2r q hq0 `|a-b| epsilon hab.
  have hright := ler_wpmul2l b hb0 `|q-p| epsilon hqp.
  have hmass := ler_wpmul2r epsilon hepsilon b q hbq.
  have hbound : `|a*q-b*p| <= 2%r*epsilon*q by smt().
  have hden : 0%r < p*q by apply mulr_gt0.
  have hratio : a/p-b/q = (a*q-b*p)/(p*q) by field; smt().
  rewrite hratio normrM normrV (ger0_norm (p*q)) 1:/#.
  rewrite ler_pdivr_mulr 1:hden.
  have hcancel : 2%r*epsilon/p * (p*q) = 2%r*epsilon*q by field; smt().
  by rewrite hcancel.
qed.

lemma conditional_ratio_error_lower (a b p q epsilon lower : real) :
  0%r < lower => lower <= p => 0%r < q =>
  0%r <= a <= p => 0%r <= b <= q =>
  `|a-b| <= epsilon => `|p-q| <= epsilon =>
  `|a/p-b/q| <= 2%r*epsilon/lower.
proof.
  move=> hl hlp hq ha hb hab hpq.
  have hp : 0%r < p by smt().
  have hepsilon : 0%r <= epsilon by have h := normr_ge0 (a-b); smt().
  have htwo : 0%r <= 2%r*epsilon by smt().
  have hinv : inv p <= inv lower by rewrite lef_pinv 1:hl 1:hp.
  have hscale := ler_wpmul2l (2%r*epsilon) htwo (inv p) (inv lower) hinv.
  have hratio := conditional_ratio_error a b p q epsilon hp hq ha hb hab hpq.
  exact (ler_trans _ _ _ hratio hscale).
qed.
