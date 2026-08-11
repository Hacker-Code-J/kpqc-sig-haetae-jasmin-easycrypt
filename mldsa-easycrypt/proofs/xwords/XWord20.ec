(* -------------------------------------------------------------------- *)
require import AllCore.

(* -------------------------------------------------------------------- *)
from Jasmin require import JWord.

require import JWordExtra CircuitBindings.

clone BitWordSH as W20 with
      op size <- 20

  rename "_XX" as "_20"

  proof gt0_size    by done
  proof size_le_256 by done.

clone WE as WE20 with
      op size <- 20,
  theory W    <- W20 { rename "_XX" as "_20" }.

clone BSW as BSW20 with
      op size <- 20,
  theory W    <- W20  { rename "_XX" as "_20" },
  theory WE   <- WE20.

(* -------------------------------------------------------------------- *)
clone BS_WB_WS_U as BS_W32_W20_U with
        op sizeS <- 20,
        op sizeB <- 32,
    theory WS    <- W20  { rename "_XX" as "_20" },
    theory WSE   <- WE20,
    theory WB    <- W32  { rename "_XX" as "_32" },
    theory WBE   <- WE32,
    theory BSWS  <- BSW20,
    theory BSWB  <- BSW32

    rename "'S" as "20"
    rename "'B" as "32"

    proof le_size by done, *.
