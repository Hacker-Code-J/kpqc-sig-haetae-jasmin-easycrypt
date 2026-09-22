require import AllCore Distr StdRing StdOrder.
import RField RealOrder.

abstract theory IndependentSign.

type input.
type output.
type sign.

module type Sampler = {
  proc sample(x : input) : output
}.

(* F may diverge. The independent sign is sampled only after F returns. *)
module Wrapper(F : Sampler) = {
  proc sample(x : input, d : sign distr) : sign * output = {
    var out : output;
    var bits : sign;
    out <@ F.sample(x);
    bits <$ d;
    return (bits,out);
  }
}.

lemma rectangle (F <: Sampler) (x0 : input) (d0 : sign distr)
    (S : sign -> bool) (T : output -> bool) &m :
  Pr[Wrapper(F).sample(x0,d0) @ &m : S res.`1 /\ T res.`2] =
    mu d0 S * Pr[F.sample(x0) @ &m : T res].
proof.
  rewrite (mulrC (mu d0 S)).
  byphoare (_ : glob F = (glob F){m} /\ x=x0 /\ d=d0
    ==> S res.`1 /\ T res.`2) => //.
  pose p := Pr[F.sample(x0) @ &m : T res].
  proc.
  seq 1 : (T out) p (mu d0 S) _ 0%r (d=d0) => //.
  + by call (_ : true); auto.
  + call (_ : glob F = (glob F){m} /\ x=x0 ==> T res) => //.
    bypr => &m0 @/p [#] eq_globs ->.
    byequiv (_ : ={glob F, x} ==> ={glob F, res}) => //=.
    by proc true.
  + by rnd S; skip => />.
  by hoare; auto => />.
qed.

lemma output_weighted_marginal (F <: Sampler) (x0 : input) (d0 : sign distr)
    (T : output -> bool) &m :
  Pr[Wrapper(F).sample(x0,d0) @ &m : T res.`2] =
    weight d0 * Pr[F.sample(x0) @ &m : T res].
proof.
  have h := rectangle F x0 d0 predT T &m.
  by move: h; rewrite /predT /=.
qed.

lemma output_marginal (F <: Sampler) (x0 : input) (d0 : sign distr)
    (T : output -> bool) &m :
  is_lossless d0 =>
  Pr[Wrapper(F).sample(x0,d0) @ &m : T res.`2] = Pr[F.sample(x0) @ &m : T res].
proof.
  move=> hd; by rewrite (output_weighted_marginal F x0 d0 T &m) hd /=.
qed.

end IndependentSign.
