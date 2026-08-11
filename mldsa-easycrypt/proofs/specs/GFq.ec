require import AllCore IntDiv.
require ZqRounding.

require import Parameters.
import MLDSAParams.

clone import ZqRounding as Round with
  op q <- q,
  op n <- n
  proof prime_q by exact prime_q
  proof gt0_n  by exact gt0_n
  rename "zmod"   as "coeff"
         "inzmod" as "incoeff"
         "ZMF"    as "Zq".

import Round ZModQ Zq.

(* Signed representation *)

op smod(n d : int) : int = if ((d + 1) %/2 <= n %% d) then n %% d - d else n %% d.

op Power2Round(x : coeff) : coeff * coeff = 
    let rplus = asint x in
    let rzero = smod rplus 2^d
    in (incoeff ((rplus - rzero) %/ 2^d), incoeff rzero).

op Decompose(r : coeff) : int * int = 
   let rplus = asint r in
   let rzero = smod rplus (2*gamma2) in
   if (rplus - rzero = q-1) 
   then (0,rzero - 1)
   else ((rplus - rzero) %/ (2*gamma2),rzero).

op HighBits(r : coeff) = (Decompose r).`1.

op LowBits(r : coeff) = (Decompose r).`2.

op MakeHint(z r : coeff) : bool =
   let r1 = HighBits(r) in
   let v1 = HighBits(r+z) in
      r1 <> v1.

(* Implementation convention: high = w1 = HighBits(w), low = r0+ct0 = LowBits(w)-cs2+ct0.
   Computes whether adding low to high*2*gamma2 changes the high bits. *)
op MakeHintImpl(high low : coeff) : bool =
  MakeHint (Zq.zero - low) (incoeff (asint high * 2 * gamma2) + low).

op UseHint(h : bool, r : coeff) : coeff = 
    let m = (q-1) %/ (2*gamma2) in
    let (r1,r0) = Decompose r in
    if h && 0 < r0
    then incoeff ((r1 + 1) %% m)
    else if (h && r0 <= 0)
         then incoeff ((r1 - 1) %% m)
         else incoeff r1.

(* Key equivalence: MakeHintImpl with (HighBits(w), LowBits(w)-cs2+ct0) equals
   MakeHint(-ct0, w-cs2+ct0), connecting the eager/impl convention to FIPS 204.
   The cs2 bound (`|asint cs2| <= Beta`) implies no 2*gamma2 boundary crossing,
   so HighBits(w-cs2) = HighBits(w) and LowBits reconstruction holds. *)
lemma MakeHintImpl_MakeHint_equiv (w cs2 ct0 : coeff) :
    `|cs2| <= Beta =>
    MakeHintImpl (incoeff (HighBits w)) (incoeff (LowBits w) - cs2 + ct0) =
    MakeHint (Zq.zero - ct0) (w - cs2 + ct0).
proof. admit. qed. (* FIXME: PY *)

(* Coefficient-level synchronization for the bz norm check:
   when |cs2| <= Beta, the infnorm check on LowBits(a - cs2) and on LowBits(a) - cs2
   agree at threshold gamma2 - Beta.
   - No 2*gamma2 crossing case: LowBits(a - cs2) = LowBits(a) - cs2 (as coeffs).
   - Crossing case: |LowBits(a) - cs2| >= gamma2 > gamma2 - Beta, and likewise
     |LowBits(a - cs2)| >= gamma2 - Beta (since LowBits is bounded but cs2 was the
     boundary-crosser). Both checks fail. *)
lemma LowBits_sub_sync (a cs2 : coeff) :
    `|cs2| <= Beta =>
    (`|incoeff (LowBits (a - cs2))| < gamma2 - Beta) =
    (`|incoeff (LowBits a) - cs2| < gamma2 - Beta).
proof. admit. qed. (* FIXME: PY *)

