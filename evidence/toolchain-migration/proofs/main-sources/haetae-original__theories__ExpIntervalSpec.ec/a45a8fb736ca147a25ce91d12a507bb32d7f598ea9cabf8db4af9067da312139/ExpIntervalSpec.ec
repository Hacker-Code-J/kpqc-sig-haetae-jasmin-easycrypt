require import AllCore IntDiv List Real.

type ei_interval = int * int.
type ei_weight_state = ei_interval * ei_interval.

(* Scaled bounds avoid divisions in the certificate checker. The division
   interpretation is established in ExpIntervalCorrectness. *)
op ei_contains (D : int) (b : ei_interval) (x : real) : bool =
  0 < D /\ 0 <= b.`1 /\ 0%r <= x /\
  b.`1%r <= D%r * x /\ D%r * x <= b.`2%r.

op ei_mul (D : int) (a b : ei_interval) : ei_interval =
  (a.`1 * b.`1 %/ D, (a.`2 * b.`2 + D - 1) %/ D).

op ei_seed_ok (D d : int) (b : ei_interval) : bool =
  0 < D /\ 1 < d /\ 0 <= b.`1 /\
  b.`1 * d <= D * (d - 1) /\ D * d <= b.`2 * (d + 1).

op ei_square_steps_check (D : int) (current : ei_interval) (steps : ei_interval list) : bool =
  with steps = [] => true
  with steps = next :: tail =>
    next = ei_mul D current current /\ ei_square_steps_check D next tail.

(* The initial interval is the first list element, so 128 squarings use
   a certificate with exactly 129 intervals. *)
op ei_square_check (D : int) (chain : ei_interval list) : bool =
  with chain = [] => false
  with chain = first :: rest => ei_square_steps_check D first rest.

op ei_weight_step (D : int) (q2 : ei_interval) (state : ei_weight_state) : ei_weight_state =
  (ei_mul D state.`1 state.`2, ei_mul D state.`2 q2).

op ei_weight_steps_check (D : int) (q2 : ei_interval)
    (current : ei_weight_state) (steps : ei_weight_state list) : bool =
  with steps = [] => true
  with steps = next :: tail =>
    next = ei_weight_step D q2 current /\ ei_weight_steps_check D q2 next tail.

op ei_weights_check (D : int) (q : ei_interval) (chain : ei_weight_state list) : bool =
  with chain = [] => false
  with chain = first :: rest =>
    first = ((D,D),q) /\ ei_weight_steps_check D (ei_mul D q q) first rest.
