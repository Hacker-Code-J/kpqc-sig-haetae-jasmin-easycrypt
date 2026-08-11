require import AllCore BitEncoding List RealExp IntDiv.
from Jasmin require import JWord.
require import Array256.

require import Parameters.
require import GFq.
import Round ZModQ Zq MLDSAParams.
require import Rq.
require import VecMat.
import PolyLVec.
import PolyKVec.
import PolyMat.

op IntegerToBits(x alpha : int) : bool list = BS2Int.int2bs alpha x. 
op BitsToInteger(y : bool list) : int = BS2Int.bs2int y.

op BitsToBytes(y : bool list) : W8.t list = map W8.bits2w (BitChunking.chunk 8 y).
op BytesToBits(x : W8.t list) : bool list = flatten (map W8.w2bits x).

op IntegerToBytes(x alpha : int) : W8.t list = take alpha (BitsToBytes (IntegerToBits x (alpha*8))).

lemma size_BytesToBits (l : W8.t list) : size (BytesToBits l) = 8 * size l by
     rewrite size_flatten /= StdBigop.Bigint.sumzE /= -map_comp /(\o) /=;
     rewrite !StdBigop.Bigint.BIA.big_mapT /= /(\o) /=;
     rewrite !StdBigop.Bigint.big_constz /=;
     rewrite !count_predT /= /= /#.

op CoeffFromThreeBytes(b0 b1 b2 : W8.t) : int option = 
   let b2 = if 127 < to_uint b2 then b2 - W8.of_int 128 else b2 in
   let z = 2^16*to_uint b2 + 2^8 * to_uint b1 + to_uint b0 in
   if z < q then Some z else None.

op CoeffFromHalfByte(b : int) : int option =
   if Eta = 2 && b < 15 
   then Some (2 - (b %% 5))
   else if Eta = 4 && b < 9 
        then Some (4 - b)
        else None.

op SimpleBitPack(w : poly, b : int) : W8.t list = 
   let blen_b = ilog 2 b + 1 in
     BitsToBytes (flatten (map (fun wi => IntegerToBits (asint wi) blen_b) (to_list w))).

op BitPack(w : poly, a b : int) : W8.t list = 
   let blen_ab = ilog 2 (a + b) + 1 in
     BitsToBytes (flatten (map (fun wi => IntegerToBits (b - crepr wi) blen_ab) (to_list w))).

op SimpleBitUnpack(v : W8.t list, b : int) : poly =
   let c = ilog 2 b + 1 in
   let z = BytesToBits(v) in
     init (fun i => nth witness (map (fun co => incoeff (BitsToInteger co)) (BitChunking.chunk c z)) i).

op BitUnpack(v : W8.t list, a b : int) : poly =
   let c = ilog 2 (a + b) + 1 in
   let z = BytesToBits(v) in
     init (fun i => nth witness (map (fun co => incoeff (b - BitsToInteger co)) (BitChunking.chunk c z)) i).

(* Validity predicate for byte-encoded eta-bounded polynomials at the spec level.
   Each (ilog 2 (2*Eta) + 1)-bit chunk of v represents an integer in [0, 2*Eta],
   matching valid_eta_bytes from the implementation proofs. *)
op valid_eta_bytes (v : W8.t list) : bool =
    forall i, 0 <= i < n =>
       BitsToInteger (nth witness
                          (BitChunking.chunk (ilog 2 (Eta + Eta) + 1) (BytesToBits v))
                          i) <= 2*Eta.

(* Each coefficient of BitUnpack v Eta Eta lies in [-Eta, Eta], so infnorm < Eta+1.
   Requires v has valid size and each nibble is in [0, 2*Eta] (valid_eta_bytes). *)
lemma BitUnpack_infnorm (v : W8.t list) :
    size v = (n * (ilog 2 (Eta + Eta) + 1)) %/ 8 =>
    valid_eta_bytes v =>
    infnorm_lt (BitUnpack v Eta Eta) (Eta + 1).
proof.
move => Hs Hval.
have ? : 8 * (n * (ilog 2 (Eta + Eta) + 1) %/ 8) %/ (ilog 2 (Eta + Eta) + 1) = n.
+ have hk : 0 < ilog 2 (Eta + Eta) + 1 by smt(ilog_ge0 param_sets).
  have h8nk : 8 %| n * (ilog 2 (Eta + Eta) + 1) by rewrite dvdz_mulr.
  by rewrite mulrC divzK // mulzK 1:/#.
rewrite /infnorm_lt /BitUnpack allP => k; rewrite mem_iota /= => kb.
rewrite initiE 1:/# (nth_map witness) /=.
+ rewrite BitChunking.size_chunk /=; 1: smt(ilog_ge0 param_sets).
  rewrite size_BytesToBits Hs /= /#.
pose x := (BitChunking.chunk (ilog 2 (Eta + Eta) + 1) (BytesToBits v)).
suff : 0 <= BitsToInteger (nth witness<:bool list> x k) <= 2*Eta.
+ rewrite -incoeffK_centered;  smt(abs_zp_small gamma2_bound param_sets).
split; first by rewrite /BitsToInteger; smt(BS2Int.bs2int_ge0).
by move => _; apply Hval; smt().
qed.

module HintPackUnpack = {
   proc hintBitPack(h : polykvec) : W8.t list = {
     var index : int;
     var y : W8.t list;
     var i,j;
     y <- mkseq (fun _ => W8.zero) (kvec + w_hint);
     index <- 0;
     i <- 0;
     while (i < kvec) {
        j <- 0;
        while (j < 256) {
           if (h.[i].[j] = Zq.one) {
              y <- put y index (W8.of_int j);
              index <- index + 1;
           }
           j <- j + 1;
        }
        y <- put y (w_hint + i) (W8.of_int index);
        i <- i + 1;
     }
     return y;
   }

   proc hintBitUnpack(y : W8.t list) : polykvec option = {
     var h : polykvec;
     var index : int;
     var error : bool;
     var _first : int;
     var i;
     h <- witness;
     index <- 0;
     error <- false;
     i <- 0;
     while (i < kvec && !error) {
       h.[i] <- Array256.init (fun k => Zq.zero);
       if (to_uint (nth witness y (w_hint+i)) < index || 
                   w_hint < to_uint (nth witness y (w_hint+i))) {
           error <- true; 
       }
       else {
          _first <- index;
          while (index < to_uint (nth witness y (w_hint+i)) && !error) {
             if (_first < index /\ to_uint (nth witness y (index)) <= to_uint (nth witness y (index-1))) {
                error <- true;
             }
             else {
                h.[i] <- h.[i].[to_uint (nth witness y index) <- Zq.one];
                index <- index + 1;
             }
          }
          if (!error) {
              i <- i + 1;
          }
       }       
     }
     while (index < w_hint && !error) {
       if (to_uint (nth witness y index) <> 0) {
         error <- true;
       }
       else {
         index <- index + 1;
       }
     }
     return if error then None else Some h;
   }
}.


