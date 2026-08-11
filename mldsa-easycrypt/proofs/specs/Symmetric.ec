require import AllCore List IntDiv.
from Jasmin require import JByte_array JWord.

require import Parameters GFq Rq VecMat Conversion Serialization.
import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq MLDSAParams.

from CryptoSpecs require import Keccak1600_Spec.

abbrev gamma1m1_bits = 19.
lemma gamma1_bitlen :  2^(gamma1m1_bits-1) < gamma1-1 (* signed range *) <= 2^(gamma1m1_bits)
  by  have/= H := param_sets; elim H => /> ??->???? /=.

clone import JArray.MonoArray as Bytes66 with op size <= 66, type elem <= W8.t, op dfl <= witness.
clone import JArray.MonoArray as Bytes34 with op size <= 34, type elem <= W8.t, op dfl <= witness.
clone import JArray.MonoArray as Bytes8 with op size <= 8, type elem <= W8.t, op dfl <= witness.
clone import JArray.MonoArray as Bytes3 with op size <= 3, type elem <= W8.t, op dfl <= witness.
clone import JArray.MonoArray as BytesV with op size <= n * (gamma1m1_bits + 1) %/ 8, type elem <= W8.t, op dfl <= witness.

(*  H = SHAKE256, G = SHAKE128 *)

(* H_sib: first 8 bytes (= 64 bits) of SHAKE256 on BytesCT input.
   Used in SampleInBall; XOF_SIB covers the continuation of the same stream. *)
op H_sib (ct : BytesCT.t) : Bytes8.t =
  Bytes8.of_list (SHAKE256 (BytesCT.to_list ct) 8).

module type XOF_SIB = {  (* bytes after 64 prefix of SHAKE256 on CTBytes  (48 or 64) input *)
  proc init(rho : BytesCT.t) : unit
  proc next() : W8.t
}.

module type XOF_RejNTTPoly = {  (* SHAKE128 on 32 bytes input *)
  proc init(rho : Bytes34.t) : unit
  proc next() : Bytes3.t
}.

module type XOF_RejBPoly = {  (* SHAKE256 on 66 bytes input *)
  proc init(rho : Bytes66.t) : unit
  proc next() : W8.t
}.

(* H_seed: SHAKE256(seed, 128), split into (rho=32, rho'=64, K=32).
   First 32 bytes are secret (PRG). *)
op H_seed (seed : Bytes34.t) : Bytes32.t * Bytes64.t * Bytes32.t =
  let l = SHAKE256 (Bytes34.to_list seed) 128 in
  ( Bytes32.of_list (take 32 l)
  , Bytes64.of_list (take 64 (drop 32 l))
  , Bytes32.of_list (drop 96 l) ).

(* H_tr: SHAKE256(pk, 64). *)
op H_tr (pk : BytesPK.t) : Bytes64.t =
  Bytes64.of_list (SHAKE256 (BytesPK.to_list pk) 64).

(* H_mu: SHAKE256(tr || msg, 64). *)
op H_mu (tr : Bytes64.t) (msg : W8.t list) : Bytes64.t =
  Bytes64.of_list (SHAKE256 (Bytes64.to_list tr ++ msg) 64).

type rnd_. (* either 0 or 32 bytes *)
op rnd_to_list : rnd_ -> W8.t list.

(* H_rhopp: SHAKE256(K || rnd || mu, 64). First input is secret (PRF). *)
op H_rhopp (K : Bytes32.t) (r : rnd_) (mu : Bytes64.t) : Bytes64.t =
  Bytes64.of_list (SHAKE256 (Bytes32.to_list K ++ rnd_to_list r ++ Bytes64.to_list mu) 64).

(* H_ct: SHAKE256(mu || w1encode, lambda/4). *)
op H_ct (mu : Bytes64.t) (w1 : BytesW1.t) : BytesCT.t =
  BytesCT.of_list (SHAKE256 (Bytes64.to_list mu ++ BytesW1.to_list w1) (lambda %/ 4)).

(* H_v: SHAKE256(seed, outlen) where outlen = n*(gamma1_bits+1)/8. First 64 bytes are secret (PRF). *)
op H_v (seed : Bytes66.t) : BytesV.t =
  BytesV.of_list (SHAKE256 (Bytes66.to_list seed) (n * (gamma1m1_bits + 1) %/ 8)).

(* Concrete XOF modules using the functional Keccak view.
   Each stores the seed and current stream position so that successive next()
   calls return consecutive bytes of the SHAKE output. Correctness relies on
   the prefix property: SHAKE256 m n = take n (SHAKE256 m N) for n <= N
   (SQUEEZE1600_ext). *)

module MLDSA_XOF_SIB : XOF_SIB = {
  var seed : BytesCT.t
  var pos  : int

  proc init(ct : BytesCT.t) : unit = {
    seed <- ct;
    pos  <- 8;  (* bytes 0–7 are consumed by H_sib *)
  }

  proc next() : W8.t = {
    var b : W8.t;
    b <- nth witness (SHAKE256 (BytesCT.to_list seed) (pos + 1)) pos;
    pos <- pos + 1;
    return b;
  }
}.

module MLDSA_XOFA : XOF_RejNTTPoly = {
  var seed : Bytes34.t
  var pos  : int

  proc init(rho : Bytes34.t) : unit = {
    seed <- rho;
    pos  <- 0;
  }

  proc next() : Bytes3.t = {
    var b : Bytes3.t;
    b <- Bytes3.of_list (take 3 (drop pos (SHAKE128 (Bytes34.to_list seed) (pos + 3))));
    pos <- pos + 3;
    return b;
  }
}.

module MLDSA_XOFS : XOF_RejBPoly = {
  var seed : Bytes66.t
  var pos  : int

  proc init(rho : Bytes66.t) : unit = {
    seed <- rho;
    pos  <- 0;
  }

  proc next() : W8.t = {
    var b : W8.t;
    b <- nth witness (SHAKE256 (Bytes66.to_list seed) (pos + 1)) pos;
    pos <- pos + 1;
    return b;
  }
}.

(* NOTE: Strictly speaking ML-DSA is a big mess when it comes to using SHAKE256.
  There are several points where inputs with the same size can occur, due to the
  variable size input of the message hashing.
  When part of the input is secret, one can argue for domain separation.
  However, Hmu can be used with inputs of the same size as  Hct and Htr,
  but still we need to make Hmu and Htr independent random oracles.
  For Htr vs Hmu one can argue that game would need to sample
  a pk such that HashPK is a prefix of PK.
  For Hct vs Hmu one can argue that game would need to sample 
  a pk such that Hash(HashPK) = HashPK.  *)
