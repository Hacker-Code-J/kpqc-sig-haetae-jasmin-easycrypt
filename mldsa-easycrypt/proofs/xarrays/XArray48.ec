(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array48.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 48,
  theory A    <- Array48.Array48.

(* -------------------------------------------------------------------- *)
clone BSA as BSA48 with
      op size <- 48,
  theory A    <- Array48.Array48

  proof gt0_size by done.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_48u8 with
      op asize <- 48,
      op bsize <- 8,
  theory A     <- Array48.Array48,
  theory BSA   <- BSA48,
  theory W     <- W8 { rename "_XX" as "_8" },
  theory WE    <- WE8,
  theory BSW   <- BSW8
  proof *.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_48u8_128 with
      op asize   <- 48,
      op bsize   <- 8,
      op ssize   <- 128,
  theory A       <- Array48.Array48,
  theory BSA     <- BSA48,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W128  { rename "_XX" as "_128" },
  theory WES     <- WE128,
  theory BSWS    <- BSW128,
  theory BSWA    <- BSWA_48u8

  proof le_size by done.

require import WArray48 BitEncoding.
import Array48 BitChunking.

lemma BSWAS_48u8_128_slicegetE o (p : W8.t Array48.t):
    0 <= o*8 <= 48*8-128 =>
     get128_direct (WArray48.init8 (fun (i_0 : int) => p.[i_0])) o = BSWAS_48u8_128.sliceget p (o * 8).
proof.
move => Ho.
rewrite /get128_direct /pack16_t;apply W128.wordP => k kb.
have //= := BSWAS_48u8_128.BVA_asliceget_Top_CircuitBindings_BSWAS_WB_t_Top_CircuitBindings_BSWAS_WS_t_Top_CircuitBindings_BSWAS_A_t.bvaslicegetP p (o * 8) _; 1: by smt().
move => -> //; rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
rewrite nth_take 1,2:/# nth_drop 1,2:/#  (nth_flatten false 8).
+ rewrite allP /= => x; rewrite mapP => He; elim He;smt(W8.size_w2bits).
rewrite (nth_map witness); 1: by rewrite size_to_list; smt().
by rewrite get_to_list get_w2bits /#.
qed.
