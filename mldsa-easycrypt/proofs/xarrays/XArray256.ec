(* -------------------------------------------------------------------- *)
require import AllCore List JWordExtra JArrayExtra CircuitBindings IntDiv.
require (*--*) Array256.
require import XWord13 XWord4 XWord10 XWord20.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
export Array256.Array256.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 256,
  theory A    <- Array256.Array256.

(* -------------------------------------------------------------------- *)
clone BSA as BSA256 with
      op size <- 256,
  theory A    <- Array256.Array256

  proof gt0_size by done.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_256u32 with
      op asize <- 256,
      op bsize <- 32,
  theory A     <- Array256.Array256,
  theory BSA   <- BSA256,
  theory W     <- W32 { rename "_XX" as "_32" },
  theory WE    <- WE32,
  theory BSW   <- BSW32.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_256u4 with
      op asize <- 256,
      op bsize <- 4,
  theory A     <- Array256.Array256,
  theory BSA   <- BSA256,
  theory W     <- W4 { rename "_XX" as "_4" },
  theory WE    <- WE4,
  theory BSW   <- BSW4.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_256u10 with
      op asize <- 256,
      op bsize <- 10,
  theory A     <- Array256.Array256,
  theory BSA   <- BSA256,
  theory W     <- W10 { rename "_XX" as "_10" },
  theory WE    <- WE10,
  theory BSW   <- BSW10.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_256u20 with
      op asize <- 256,
      op bsize <- 20,
  theory A     <- Array256.Array256,
  theory BSA   <- BSA256,
  theory W     <- W20 { rename "_XX" as "_20" },
  theory WE    <- WE20,
  theory BSW   <- BSW20.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_256u13 with
      op asize <- 256,
      op bsize <- 13,
  theory A     <- Array256.Array256,
  theory BSA   <- BSA256,
  theory W     <- W13 { rename "_XX" as "_13" },
  theory WE    <- WE13,
  theory BSW   <- BSW13.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_256u32_256 with
      op asize   <- 256,
      op bsize   <- 32,
      op ssize   <- 256,
  theory A       <- Array256.Array256,
  theory BSA     <- BSA256,
  theory WB      <- W32  { rename "_XX" as "_32" },
  theory WEB     <- WE32,
  theory BSWB    <- BSW32,
  theory WS      <- W256  { rename "_XX" as "_256" },
  theory WES     <- WE256,
  theory BSWS    <- BSW256,
  theory BSWA    <- BSWA_256u32

  proof le_size by done.

require import WArray1024 BitEncoding.
import Array256 BitChunking.

lemma BSWAS_256u32_256_slicesetE (t : W32.t Array256.t) o (s : W256.t) :
  0 <= (o*8) <= 32 * 256 - 256 =>    
   BSWAS_256u32_256.sliceset t (o*8) s =
      Array256.init (get32 (set256_direct (WArray1024.init32 (fun (i_0 : int) => t.[i_0])) o s)).
proof. 
move => Ho.
rewrite tP => k kb.
rewrite wordP => i ib;rewrite initiE 1:/# /=.
have //= := BSWAS_256u32_256.BVA_asliceset_Top_CircuitBindings_BSWAS_WB_t_Top_CircuitBindings_BSWAS_WS_t_Top_CircuitBindings_BSWAS_A_t.bvaslicesetP t (o*8) s _ (k*32+i) _;1,2:by smt().
rewrite (nth_flatten false 32).
+ rewrite allP /= => x; rewrite mapP => He; elim He;smt(W32.size_w2bits).
rewrite (nth_map witness); 1: by rewrite size_to_list; smt().
rewrite get_to_list get_w2bits (: (k * 32 + i) %/ 32 = k) 1:/# (: (k * 32 + i) %% 32 = i) 1:/# => -> .
rewrite (nth_flatten false 32).
+ rewrite allP /= => x; rewrite mapP => He; elim He;smt(W32.size_w2bits).
rewrite (nth_map witness); 1: by rewrite size_to_list; smt().
rewrite get_w2bits get_to_list /get32_direct /set256_direct pack4E initiE 1:/# /= /(\bits8) initiE 1:/# /= initiE 1:/# /= /init32 initiE 1:/# /=.
by smt(W8.initiE).
qed.


lemma BSWAS_256u32_256_slicegetE o (p : W32.t Array256.t):
    0 <= o*8 <= 256*32-256 =>
     get256_direct (WArray1024.init32 (fun (i_0 : int) => p.[i_0])) o = BSWAS_256u32_256.sliceget p (o * 8).
  proof.
  move => Ho.
  rewrite /get256_direct /pack32_t;apply W256.wordP => k kb.
  have //= := BSWAS_256u32_256.BVA_asliceget_Top_CircuitBindings_BSWAS_WB_t_Top_CircuitBindings_BSWAS_WS_t_Top_CircuitBindings_BSWAS_A_t.bvaslicegetP p (o * 8) _; 1: by smt().
  move => -> //; rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= /(\bits8) initiE 1:/# /=.
  rewrite nth_take 1,2:/# nth_drop 1,2:/#  (nth_flatten false 32).
  + rewrite allP /= => x; rewrite mapP => He; elim He;smt(W32.size_w2bits).
  rewrite (nth_map witness); 1: by rewrite size_to_list; smt().
  by rewrite get_to_list get_w2bits /#.
 qed. 
  
