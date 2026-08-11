(* -------------------------------------------------------------------- *)
require import AllCore List IntMin.

(* -------------------------------------------------------------------- *)
type ('a, 'b) xof = 'a -> int -> 'b.

(* -------------------------------------------------------------------- *)
op slice ['a, 'b] (xof : ('a, 'b) xof) (input : 'a) (base len : int) : 'b list =
  mkseq (fun i => xof input (base + i)) len.

(* -------------------------------------------------------------------- *)
op group ['a 'b] (len : int) (xof : ('a, 'b) xof) : ('a, 'b list) xof =
  fun (input : 'a) (i : int) => slice xof input (i * len) len.
  
(* -------------------------------------------------------------------- *)
op map ['a 'b 'c] (f : 'b -> 'c) (xof : ('a, 'b) xof) : ('a, 'c) xof =
  fun input i => f (xof input i).

(* -------------------------------------------------------------------- *)
op filter ['a 'b] (f : 'b -> bool) (xof : ('a, 'b) xof) : ('a, 'b) xof =
  fun input i =>
    let j =
      argmin
        (fun j => slice xof input 0 j)
        (fun s => i <= size (filter f s)) in
    xof input j.
