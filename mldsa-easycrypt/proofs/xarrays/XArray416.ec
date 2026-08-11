(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array416.
require import XWord13 JWordExtra.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 416,
  theory A    <- Array416.Array416.

(* -------------------------------------------------------------------- *)
clone BSA as BSA416 with
      op size <- 416,
  theory A    <- Array416.Array416

  proof gt0_size by done.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_416u8 with
      op asize <- 416,
      op bsize <- 8,
  theory A     <- Array416.Array416,
  theory BSA   <- BSA416,
  theory W     <- W8 { rename "_XX" as "_8" },
  theory WE    <- WE8,
  theory BSW   <- BSW8
  proof *.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_416u8_13 with
      op asize   <- 416,
      op bsize   <- 8,
      op ssize   <- 13,
  theory A       <- Array416.Array416,
  theory BSA     <- BSA416,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W13  { rename "_XX" as "_13" },
  theory WES     <- WE13,
  theory BSWS    <- BSW13,
  theory BSWA    <- BSWA_416u8

  proof le_size by done.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_416u8_128 with
      op asize   <- 416,
      op bsize   <- 8,
      op ssize   <- 128,
  theory A       <- Array416.Array416,
  theory BSA     <- BSA416,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W128  { rename "_XX" as "_128" },
  theory WES     <- WE128,
  theory BSWS    <- BSW128,
  theory BSWA    <- BSWA_416u8

  proof le_size by done.

require import WArray416 BitEncoding.
import Array416 BitChunking.

lemma BSWAS_416u8_128_slicesetE (t : W8.t Array416.t) o (s : W128.t) :
  0 <= (o*8) <= 8 * 416 - 128 =>    
   BSWAS_416u8_128.sliceset t (o*8) s =
      Array416.init (get8 (set128_direct (WArray416.init8 (fun (i_0 : int) => t.[i_0])) o s)).
proof. 
move => Ho.
rewrite tP => k kb.
rewrite wordP => i ib;rewrite initiE 1:/# /=.
have //= := BSWAS_416u8_128.BVA_asliceset_Top_CircuitBindings_BSWAS_WB_t_Top_CircuitBindings_BSWAS_WS_t_Top_CircuitBindings_BSWAS_A_t.bvaslicesetP t (o*8) s _ (k*8+i) _;1,2:by smt().
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

lemma BSWAS_416u8_128_slicegetE  o (p : W8.t Array416.t):
    0 <= o*8 <= 416*8-128 =>
     get128_direct (WArray416.init8 (fun (i_0 : int) => p.[i_0])) o = BSWAS_416u8_128.sliceget p (o * 8).
  proof.
  move => Ho.
  rewrite /get128_direct /pack16_t;apply W128.wordP => k kb.
  have //= := BSWAS_416u8_128.BVA_asliceget_Top_CircuitBindings_BSWAS_WB_t_Top_CircuitBindings_BSWAS_WS_t_Top_CircuitBindings_BSWAS_A_t.bvaslicegetP p (o * 8) _; 1: by smt().
  move => -> //; rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  rewrite nth_take 1,2:/# nth_drop 1,2:/#  (nth_flatten false 8).
  + rewrite allP /= => x; rewrite mapP => He; elim He;smt(W8.size_w2bits).
  rewrite (nth_map witness); 1: by rewrite size_to_list; smt().
  by rewrite get_to_list get_w2bits /#.
 qed. 
