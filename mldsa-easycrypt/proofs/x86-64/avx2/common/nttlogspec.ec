(**
  This theory provides a high-level, algebraic specification of the Number
  Theoretic Transform (NTT).

  This specification abstracts away from algorithmic structure and
  implementation concerns, focusing solely on the mathematical meaning of
  the transform.

  It is intended to serve as an intermediate, clean algebraic layer:
  on one side, it can be related to the official NIST specification, and
  on the other side, it provides the reference model against which the
  low-level (machine-level) implementation is connected and verified.
*)

(* -------------------------------------------------------------------- *)
require import AllCore CoreUtils List IntDiv BitEncoding.
(*---*) import BS2Int.

(* -------------------------------------------------------------------- *)
(* Should come from somewhere else                                      *)
op q : int = 8380417.

(* -------------------------------------------------------------------- *)
op zeta_ : int = 1753.

op bitrev8 (i : int) : int =
  bs2int (rev (int2bs 8 i)).

op zpow (i : int) = (zeta_ ^ bitrev8 i) %% q.

op qcenter (x : int) : int =    (* FIXME: factor out *)
  let x = x %% q in
  if q %/ 2 < x then x - q else x.

op mrepr (x : int) : int =
  (x * 2^32) %% q.

op [opaque] zetaL (i : int) =
  if 0 <= i < 8 then
    mkseq (fun j => qcenter (mrepr (zpow (j + 2^(7-i))))) (2^(7-i))
  else [].
