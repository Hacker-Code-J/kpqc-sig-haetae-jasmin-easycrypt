require import AllCore IntDiv List Ring BitEncoding.
require import Array256.

require import GFq Parameters.
import Round ZModQ Zq .


(******************************************************)
(* Representations of polynomials in Zq[X]/(X^256+1)  *)
(******************************************************)

import PolyReduce.

type poly  = coeff Array256.t.
type apoly = polyXnD1.

op poly2prealg (p : poly) : prepoly =
  fun i => if 0 <= i < n then p.[i] else Zq.zero.

op poly2alg (p : poly) : apoly =
  pinject (to_polyd (poly2prealg p)).

op alg2poly (p : apoly) : poly =
  init (fun i => p.[i]).

lemma ispoly_poly2prealg (p : poly) : ispoly (poly2prealg p).
proof. by (split; last exists 256); smt(). qed.

lemma poly2algiE (p : poly) (i : int) :
  0 <= i < 256 => (poly2alg p).[i] = p.[i].
proof.
move=> rgi @/"_.[_]" @/poly2alg; rewrite piK.
- apply/reducedP/deg_leP => // j lt_ji.
  rewrite coeffE 1:&(ispoly_poly2prealg).
  by rewrite /poly2prealg ifF //#.
- rewrite to_polydK 1:ispoly_poly2prealg.
  by rewrite /poly2prealg ifT.
qed.

lemma alg2polyiE (p : apoly) (i : int) :
  0 <= i < 256 => (alg2poly p).[i] = p.[i].
proof. by move=> ? @/alg2poly; rewrite initiE. qed.

lemma alg2polyK : cancel poly2alg alg2poly.
proof.
move=> p; apply/Array256.ext_eq => i rgi.
by rewrite alg2polyiE // poly2algiE.
qed.

lemma poly2algK : cancel alg2poly poly2alg.
proof.
move=> p; apply: polyXnD1_eqP => i rgi.
by rewrite poly2algiE // alg2polyiE.
qed.

op (&*) (a b : poly) = alg2poly (( * ) (poly2alg a) (poly2alg b)).
op (&+) (a b : poly) = alg2poly (( + ) (poly2alg a) (poly2alg b)).
op (&-) (a   : poly) = alg2poly (PolyReduce.([-]) (poly2alg a)).
op poly_zero : poly = create Zq.zero.


(**************************************************)
(**************************************************)

(* The NTT operation over ring elements *)

op zroot = incoeff 1753.

op br = BitEncoding.BitReverse.bsrev 8.


op ntt(p : poly) : poly.

op invntt(p : poly) : poly. 

(* The base multiplication in the NTT domain pointwise. *)

op basemul(a b : poly) :  poly = init (fun i => a.[i] * b.[i]).

op poly_Power2Round(p : poly) : poly * poly = 
     (init (fun i => (Power2Round p.[i]).`1), 
      init (fun i => (Power2Round p.[i]).`2)).

op poly_UseHint(h : poly, r : poly) : poly = 
     init (fun ii => UseHint (!h.[ii] = Zq.zero) r.[ii]).

op poly_MakeHint(p1 : poly, p2 : poly) : poly =
     init (fun ii => incoeff (b2i (MakeHint p1.[ii] p2.[ii]))).

op poly_MakeHintImpl(p1 : poly, p2 : poly) : poly =
     init (fun ii => incoeff (b2i (MakeHintImpl p1.[ii] p2.[ii]))).

op poly_HighBits(p : poly) : poly = 
     init (fun ii => incoeff (HighBits p.[ii])).

op poly_LowBits(p : poly) : poly =
     init (fun ii => incoeff (LowBits p.[ii])).

op infnorm_lt (p : poly) (bound : int) : bool =
  all (fun j => `|p.[j]| < bound) (iota_ 0 256).

lemma Rq_addC : forall (a b : poly), a &+ b = b &+ a by admit. (* ring addition commutative *)

(* Componentwise indexing for poly-level +/- and the zero element. *)
lemma poly_addE (a b : poly) (i : int) :
  0 <= i < 256 => (a &+ b).[i] = a.[i] + b.[i].
proof. by move => Hi; rewrite /(&+) alg2polyiE // rcoeffD !poly2algiE. qed.

lemma poly_negE (a : poly) (i : int) :
  0 <= i < 256 => ((&-) a).[i] = - a.[i].
proof. by move => Hi; rewrite /(&-) alg2polyiE // -rcoeffN poly2algiE. qed.

lemma poly_zeroE (i : int) :
  0 <= i < 256 => poly_zero.[i] = Zq.zero.
proof. by move => Hi; rewrite /poly_zero Array256.createiE. qed.
