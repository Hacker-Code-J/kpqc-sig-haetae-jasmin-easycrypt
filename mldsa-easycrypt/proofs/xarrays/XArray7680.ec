(* -------------------------------------------------------------------- *)
require import AllCore JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array7680.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
export Array7680.Array7680.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 7680,
  theory A    <- Array7680.Array7680.

(* -------------------------------------------------------------------- *)
clone BSA as BSA7680 with
      op size <- 7680,
  theory A    <- Array7680.Array7680

  proof gt0_size by done.
