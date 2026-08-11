(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array16.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
export Array16.Array16.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 16,
  theory A    <- Array16.Array16.

(* -------------------------------------------------------------------- *)
clone BSA as BSA16 with
      op size <- 16,
  theory A    <- Array16.Array16

  proof gt0_size by done.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_16u8 with
      op asize <- 16,
      op bsize <- 8,
  theory A     <- Array16.Array16,
  theory BSA   <- BSA16,
  theory W     <- W8 { rename "_XX" as "_8" },
  theory WE    <- WE8,
  theory BSW   <- BSW8
  proof *.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_16u8_128 with
      op asize   <- 16,
      op bsize   <- 8,
      op ssize   <- 128,
  theory A       <- Array16.Array16,
  theory BSA     <- BSA16,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W128  { rename "_XX" as "_128" },
  theory WES     <- WE128,
  theory BSWS    <- BSW128,
  theory BSWA    <- BSWA_16u8

  proof le_size by done.


require import WArray16 BitEncoding.
import Array16 BitChunking.

lemma BSWAS_16u8_128_slicesetE (t : W8.t Array16.t) o (s : W128.t) :
  0 <= (o*8) <= 8 * 16 - 128 =>    
   BSWAS_16u8_128.sliceset t (o*8) s =
      Array16.init (get8 (set128_direct (WArray16.init8 (fun (i_0 : int) => t.[i_0])) o s)).
proof. 
move => Ho.
rewrite tP => k kb.
rewrite wordP => i ib;rewrite initiE 1:/# /=.
have //= := BSWAS_16u8_128.BVA_asliceset_Top_CircuitBindings_BSWAS_WB_t_Top_CircuitBindings_BSWAS_WS_t_Top_CircuitBindings_BSWAS_A_t.bvaslicesetP t (o*8) s _ (k*8+i) _;1,2:by smt().
rewrite (nth_flatten false 8).
+ rewrite allP /= => x; rewrite mapP => He; elim He;smt(W8.size_w2bits).
rewrite (nth_map witness); 1: by rewrite size_to_list; smt().
rewrite get_to_list get_w2bits (: (k * 8 + i) %/ 8 = k) 1:/# (: (k * 8 + i) %% 8 = i) 1:/# => -> .
rewrite (nth_flatten false 8).
+ rewrite allP /= => x; rewrite mapP => He; elim He;smt(W8.size_w2bits).
rewrite (nth_map witness); 1: by rewrite size_to_list; smt().
rewrite get_w2bits get_to_list /get8 /set128_direct initiE 1:/# /= /(\bits8) initiE 1:/# /=.
by smt(W8.initiE).
qed.
