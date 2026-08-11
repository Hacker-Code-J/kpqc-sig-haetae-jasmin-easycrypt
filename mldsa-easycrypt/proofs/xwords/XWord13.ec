(* -------------------------------------------------------------------- *)
require import AllCore.

(* -------------------------------------------------------------------- *)
from Jasmin require import JWord.

require import JWordExtra CircuitBindings.

(* -------------------------------------------------------------------- *)
clone export BitWordSH as W13 with
    op size <- 13
    rename "_XX" as "_13"
    proof gt0_size by done,
          size_le_256 by done.

clone WE as WE13 with
  op     size <- 13,
  theory W    <- W13 { rename "_XX" as "_13" }.
  
clone BSW as BSW13 with
  op     size <- 13,
  theory W    <- W13  { rename "_XX" as "_13" },
  theory WE   <- WE13 { rename "_XX" as "_13" }.

clone BS_WB_WS_U as BS_W32_W13_U with
        op sizeS <- 13,
        op sizeB <- 32,
    theory WS    <- W13  { rename "_XX" as "_13" },
    theory WSE   <- WE13,
    theory WB    <- W32  { rename "_XX" as "_32" },
    theory WBE   <- WE32,
    theory BSWS  <- BSW13,
    theory BSWB  <- BSW32

    rename "'S" as "13"
    rename "'B" as "32"

    proof le_size by done, *.
