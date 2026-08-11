require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat Symmetric Sampling MLDSA_W32_Rep MLDSA.
import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq.

require import Array2 Array26 Array32 Array48 Array64 Array66 Array128 Array136 Array768 Array1952.
require import WArray2 Array7 WArray32 WArray48 WArray64 WArray66 WArray128 WArray136 WArray208 WArray768 WArray1952.
from CryptoSpecs require import JWordList.

(****************************************************************************)
(* Establish that M's keccak primitives equal Keccak1600_Jazz.M             *)
(****************************************************************************)

from Keccak require import Keccak1600_avx2.
from Keccak require import Keccakf1600_avx2.

equiv state_init_avx2_eq:
 M.__state_init_avx2 ~ Keccak1600_Jazz.M.__state_init_avx2
 : ={arg} ==> ={res}
 by sim.

equiv keccakf1600_avx2_eq:
 M._keccakf1600_avx2 ~ Keccak1600_Jazz.M._keccakf1600_avx2
 : ={arg} ==> ={res}
 by sim.

equiv keccakf1600_st25_avx2_eq:
 M._keccakf1600_st25_avx2 ~ Keccak1600_Jazz.M._keccakf1600_st25_avx2
 : ={arg} ==> ={res}
 by sim.

(****************************************************************************)
(* Clone KeccakArrayAvx2 for each array size used in hashing.jinc           *)
(****************************************************************************)

from Keccak require import Keccak1600_fixedsizes_avx2.
from Keccak require import Keccak1600_updstate_avx2.

clone KeccakArrayAvx2 as A2avx2
 with op _ASIZE <- 2,
      theory A <- Array2,
      theory WA <- WArray2
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A32avx2
 with op _ASIZE <- 32,
      theory A <- Array32,
      theory WA <- WArray32
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A48avx2
 with op _ASIZE <- 48,
      theory A <- Array48,
      theory WA <- WArray48
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A64avx2
 with op _ASIZE <- 64,
      theory A <- Array64,
      theory WA <- WArray64
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A128avx2
 with op _ASIZE <- 128,
      theory A <- Array128,
      theory WA <- WArray128
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A136avx2
 with op _ASIZE <- 136,
      theory A <- Array136,
      theory WA <- WArray136
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A768avx2
 with op _ASIZE <- 768,
      theory A <- Array768,
      theory WA <- WArray768
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A1952avx2
 with op _ASIZE <- 1952,
      theory A <- Array1952,
      theory WA <- WArray1952
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakUpdstateAvx2 as A64updstate
 with op _ASIZE <- 64,
      theory A <- Array64,
      theory WA <- WArray64
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakUpdstateAvx2 as A66updstate
 with op _ASIZE <- 66,
      theory A <- Array66,
      theory WA <- WArray66
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

(****************************************************************************)
(* Equiv lemmas: M.primitive ~ KeccakArray.MM.primitive                     *)
(****************************************************************************)

equiv a2__absorb_avx2_eq:
 M.a2____absorb_avx2 ~ A2avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a32__absorb_avx2_eq:
 M.a32____absorb_avx2 ~ A32avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a_COMMITMENT_HASH__absorb_avx2_eq:
 M.a_COMMITMENT_HASH____absorb_avx2 ~ A48avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a_COMMITMENT_HASH__dumpstate_avx2_eq:
 M.a_COMMITMENT_HASH____dumpstate_avx2 ~ A48avx2.MM.__dumpstate_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a64__absorb_avx2_eq:
 M.a64____absorb_avx2 ~ A64avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a64__dumpstate_avx2_eq:
 M.a64____dumpstate_avx2 ~ A64avx2.MM.__dumpstate_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a128__absorb_avx2_eq:
 M.a128____absorb_avx2 ~ A128avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a128__dumpstate_avx2_eq:
 M.a128____dumpstate_avx2 ~ A128avx2.MM.__dumpstate_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a136__dumpstate_avx2_eq:
 M.a136____dumpstate_avx2 ~ A136avx2.MM.__dumpstate_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a_ENCODED_COMMITMENT__absorb_avx2_eq:
 M.a_ENCODED_COMMITMENT____absorb_avx2 ~ A768avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}.
 proc. 
by  sim; auto => />.
qed.

equiv a_VERIFICATION_KEY__absorb_avx2_eq:
 M.a_VERIFICATION_KEY____absorb_avx2 ~ A1952avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}.
proc.
by  sim; auto => />.
qed.

equiv init_updstate_avx2_eq:
 M._init_updstate_avx2 ~ Keccak1600_Jazz.M._init_updstate_avx2
 : ={arg} ==> ={res}
 by sim.

equiv finish_updstate_avx2_eq:
 M._finish_updstate_avx2 ~ Keccak1600_Jazz.M._finish_updstate_avx2
 : ={arg} ==> ={res}
 by sim.

equiv absorb_m_updstate_avx2_eq:
 M._absorb_m_updstate_avx2 ~ Keccak1600_Jazz.M._absorb_m_updstate_avx2
 : ={arg, Glob.mem} ==> ={res, Glob.mem}
 by sim.

equiv a64_squeeze_updstate_avx2_eq:
 M.a64___squeeze_updstate_avx2 ~ A64updstate.MM._squeeze_updstate_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a66_update_updstate_avx2_eq:
 M.a66___update_updstate_avx2 ~ A66updstate.MM._update_updstate_avx2
 : ={arg} ==> ={res}
 by sim.

(****************************************************************************)
(* Module K: keccak-library wrapper mirroring M's hashing procedures        *)
(****************************************************************************)

module K = {

  proc shake256_absorb_34 (seed:W8.t Array32.t, extra:W8.t Array2.t) :
  W256.t Array7.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    var  _1:int;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A32avx2.MM.__absorb_avx2 (state, 0, seed, 0, 136);
    (state,  _1) <@ A2avx2.MM.__absorb_avx2 (state, 32, extra, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    return state;
  }

  proc shake256_absorb_66 (rho_prime:W8.t Array64.t, domain_separator:W16.t) :
  W256.t Array7.t = {
    var state:W256.t Array7.t;
    var ds:W8.t Array2.t;
    var  _0:int;
    var  _1:int;
    ds <- witness;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A64avx2.MM.__absorb_avx2 (state, 0, rho_prime, 0, 136);
    ds <-
    (Array2.init
    (WArray2.get8
    (WArray2.set16 (WArray2.init8 (fun i => ds.[i])) 0 domain_separator)));
    (state,  _1) <@ A2avx2.MM.__absorb_avx2 (state, 64, ds, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    return state;
  }

  proc shake256_absorb_128 (block:W8.t Array128.t) :
  W256.t Array7.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A128avx2.MM.__absorb_avx2 (state, 0, block, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    return state;
  }

  proc shake256_absorb_commitment_hash (hash:W8.t Array48.t) :
  W256.t Array7.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A48avx2.MM.__absorb_avx2 (state, 0, hash, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    return state;
  }

  proc squeeze_128_bytes (array:W8.t Array128.t, state:W256.t Array7.t) :
  W8.t Array128.t = {
    var  _0:int;
    (array,  _0) <@ A128avx2.MM.__dumpstate_avx2 (array, 0, 128, state);
    return array;
  }

  proc shake256_squeeze_block (block:W8.t Array136.t, state:W256.t Array7.t) :
  W8.t Array136.t = {
    var  _0:int;
    (block,  _0) <@ A136avx2.MM.__dumpstate_avx2 (block, 0, 136, state);
    return block;
  }

  proc squeeze_64_bytes (array:W8.t Array64.t, state:W256.t Array7.t) :
  W8.t Array64.t = {
    var  _0:int;
    (array,  _0) <@ A64avx2.MM.__dumpstate_avx2 (array, 0, 64, state);
    return array;
  }

  proc squeeze_commitment_hash_bytes (array:W8.t Array48.t, state:W256.t Array7.t) :
  W8.t Array48.t = {
    var  _0:int;
    (array,  _0) <@ A48avx2.MM.__dumpstate_avx2 (array, 0, 48, state);
    return array;
  }

  proc hash_verification_key (verification_key_hash:W8.t Array64.t,
                              verification_key:W8.t Array1952.t) :
  W8.t Array64.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A1952avx2.MM.__absorb_avx2 (state, 0, verification_key, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    (verification_key_hash,  _0) <@ A64avx2.MM.__dumpstate_avx2 (
    verification_key_hash, 0, 64, state);
    return verification_key_hash;
  }

  proc __derive_commitment_hash (message_representative:W8.t Array64.t,
                                 encoded_commitment:W8.t Array768.t) :
  W8.t Array48.t = {
    var commitment_hash:W8.t Array48.t;
    var state:W256.t Array7.t;
    var  _0:int;
    var  _1:int;
    commitment_hash <- witness;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A64avx2.MM.__absorb_avx2 (state, 0, message_representative, 0, 136);
    (state,  _1) <@ A768avx2.MM.__absorb_avx2 (state, 64, encoded_commitment, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    (commitment_hash,  _0) <@ A48avx2.MM.__dumpstate_avx2 (commitment_hash, 0, 48, state);
    return commitment_hash;
  }

  (* Absorbs (randomness || [6; 5]) via SHAKE256 and squeezes 128 bytes,
     corresponding to the keygen PRF expansion step in __keygen_internal. *)
  proc __keygen_prf (prf_output:W8.t Array128.t, randomness:W8.t Array32.t) : W8.t Array128.t = {
    var state:W256.t Array7.t;
    var extra:W8.t Array2.t;
    extra <- witness;
    state <- witness;
    extra.[0] <- W8.of_int 6;
    extra.[1] <- W8.of_int 5;
    state <@ shake256_absorb_34(randomness, extra);
    prf_output <@ squeeze_128_bytes(prf_output, state);
    return prf_output;
  }

  proc derive_seed_for_mask (k:W8.t Array32.t, randomness:W8.t Array32.t,
                             message_representative:W8.t Array64.t,
                             seed_for_mask:W8.t Array64.t) : W8.t Array64.t = {
    var copied_32_bytes:W256.t;
    var block:W8.t Array128.t;
    var state:W256.t Array7.t;
    block <- witness;
    state <- witness;
    copied_32_bytes <- (get256_direct (WArray32.init8 (fun i => k.[i])) 0);
    block <- (Array128.init (WArray128.get8 (WArray128.set256_direct (WArray128.init8 (fun i => block.[i])) 0 copied_32_bytes)));
    copied_32_bytes <- (get256_direct (WArray32.init8 (fun i => randomness.[i])) 0);
    block <- (Array128.init (WArray128.get8 (WArray128.set256_direct (WArray128.init8 (fun i => block.[i])) 32 copied_32_bytes)));
    copied_32_bytes <- (get256_direct (WArray64.init8 (fun i => message_representative.[i])) 0);
    block <- (Array128.init (WArray128.get8 (WArray128.set256_direct (WArray128.init8 (fun i => block.[i])) 64 copied_32_bytes)));
    copied_32_bytes <- (get256_direct (WArray64.init8 (fun i => message_representative.[i])) 32);
    block <- (Array128.init (WArray128.get8 (WArray128.set256_direct (WArray128.init8 (fun i => block.[i])) 96 copied_32_bytes)));
    state <@ shake256_absorb_128(block);
    seed_for_mask <@ squeeze_64_bytes(seed_for_mask, state);
    return seed_for_mask;
  }

  (* __derive_message_representative uses the streaming updstate interface
     (variable-length absorb via memory pointers). K calls Keccak1600_Jazz.M
     directly for the size-independent updstate procs and the size-dependent
     A{64,66}updstate.MM clones for the parametric ones. *)
  proc __derive_message_representative (verification_key_hash:W8.t Array64.t,
                                        context_pointer:int, context_size:int,
                                        message_pointer:int, message_size:int) :
  W8.t Array64.t = {
    var message_representative:W8.t Array64.t;
    var copied_32_bytes:W256.t;
    var prefix:W8.t Array66.t;
    var trailb:W8.t;
    var state:W64.t Array26.t;
    var rate64:int;
    var len:int;
    var buf:int;
    message_representative <- witness;
    prefix <- witness;
    state <- witness;
    copied_32_bytes <-
    (get256_direct (WArray64.init8 (fun i => verification_key_hash.[i])) 0);
    prefix <-
    (Array66.init
    (WArray66.get8
    (WArray66.set256_direct (WArray66.init8 (fun i => prefix.[i])) 0
    copied_32_bytes)));
    copied_32_bytes <-
    (get256_direct (WArray64.init8 (fun i => verification_key_hash.[i])) 32);
    prefix <-
    (Array66.init
    (WArray66.get8
    (WArray66.set256_direct (WArray66.init8 (fun i => prefix.[i])) 32
    copied_32_bytes)));
    prefix.[64] <- (W8.of_int 0);
    prefix.[65] <- (truncateu8 (W64.of_int context_size));
    rate64 <- 17;
    trailb <- (W8.of_int 31);
    state <@ Keccak1600_Jazz.M._init_updstate_avx2 (state, rate64, trailb);
    len <- 66;
    state <@ A66updstate.MM._update_updstate_avx2 (state, prefix, len);
    buf <- context_pointer;
    len <- context_size;
    state <@ Keccak1600_Jazz.M._absorb_m_updstate_avx2 (state, buf, len);
    buf <- message_pointer;
    len <- message_size;
    state <@ Keccak1600_Jazz.M._absorb_m_updstate_avx2 (state, buf, len);
    state <@ Keccak1600_Jazz.M._finish_updstate_avx2 (state);
    len <- 64;
    (state, message_representative) <@ A64updstate.MM._squeeze_updstate_avx2 (state,
    message_representative, len);
    return message_representative;
  }

}.

(****************************************************************************)
(* Equiv lemmas: M.proc ~ K.proc                                            *)
(****************************************************************************)

equiv shake256_absorb_34_eq:
 M.shake256_absorb_34 ~ K.shake256_absorb_34
 : ={arg} ==> ={res}.
  proc. 
by inline *;sim; auto => />.
qed.


equiv shake256_absorb_66_eq:
 M.shake256_absorb_66 ~ K.shake256_absorb_66
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv shake256_absorb_128_eq:
 M.shake256_absorb_128 ~ K.shake256_absorb_128
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv shake256_absorb_commitment_hash_eq:
 M.shake256_absorb_commitment_hash ~ K.shake256_absorb_commitment_hash
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv squeeze_128_bytes_eq:
 M.squeeze_128_bytes ~ K.squeeze_128_bytes
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv shake256_squeeze_block_eq:
 M.shake256_squeeze_block ~ K.shake256_squeeze_block
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv squeeze_64_bytes_eq:
 M.squeeze_64_bytes ~ K.squeeze_64_bytes
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv squeeze_commitment_hash_bytes_eq:
 M.squeeze_commitment_hash_bytes ~ K.squeeze_commitment_hash_bytes
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv hash_verification_key_eq:
 M.hash_verification_key ~ K.hash_verification_key
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />;sim.
qed.

equiv derive_commitment_hash_eq:
 M.__derive_commitment_hash ~ K.__derive_commitment_hash
 : ={arg} ==> ={res}.
proc. 
seq 4 4 : (={encoded_commitment,state,commitment_hash}); 1: by inline *;sim.
seq 1 1 : (={encoded_commitment,state,commitment_hash}); 2: by inline *;sim.
inline {1} 1; inline {2} 1.
by sim; auto => />.
qed.

equiv derive_message_representative_eq:
 M.__derive_message_representative ~ K.__derive_message_representative
 : ={arg, Glob.mem} ==> ={res, Glob.mem}
 by sim.

equiv keygen_prf_eq:
 M.__keygen_prf ~ K.__keygen_prf
 : ={arg} ==> ={res}.
proc.
inline *; sim; auto => />.
qed.

equiv derive_seed_for_mask_eq:
 M.derive_seed_for_mask ~ K.derive_seed_for_mask
 : ={arg} ==> ={res}.
proc.
by inline *; sim; auto => />.
qed.

(****************************************************************************)
(* Correctness lemmas (absorbed-state characterization)                     *)
(****************************************************************************)

hoare shake256_absorb_34_h' _seed _extra :
 K.shake256_absorb_34
 : arg.`1 = _seed /\ arg.`2 = _extra
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _seed ++ to_list _extra))).
proof.
proc.
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A2avx2.absorb_avx2_h (to_list seed) extra 31 136).
wp; ecall (A32avx2.absorb_avx2_h [<:W8.t>] seed 0 136).
wp; call (state_init_avx2_h 136).
auto => |> st0 ? [st1 x2] ??; split; 1: by smt(Array32.size_to_list).
move => ? [st2 x3] /= -> /=; split; 1: by rewrite  stavx2_from_st25K.
by move => ->; rewrite !stavx2_from_st25K.
qed.

lemma shake256_absorb_34_ll: islossless K.shake256_absorb_34.
proof.
proc.
call keccakf1600_avx2_ll.
call A2avx2.absorb_avx2_ll.
call A32avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare shake256_absorb_34_ph' _seed _extra :
 [ K.shake256_absorb_34
 : arg.`1 = _seed /\ arg.`2 = _extra
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _seed ++ to_list _extra)))
 ] = 1%r.
proof.
by conseq shake256_absorb_34_ll (shake256_absorb_34_h' _seed _extra).
qed.

phoare shake256_absorb_34_ph _seed _extra :
 [ M.shake256_absorb_34
 : arg.`1 = _seed /\ arg.`2 = _extra
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _seed ++ to_list _extra)))
 ] = 1%r.
proof.
by conseq shake256_absorb_34_eq (shake256_absorb_34_ph' _seed _extra) => // /#.
qed.

(* ---------- shake256_absorb_66 ---------- *)

hoare shake256_absorb_66_h' _rho_prime _ds :
 K.shake256_absorb_66
 : arg.`1 = _rho_prime /\ arg.`2 = _ds
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136
      (to_list _rho_prime ++ to_list _ds))).
proof.
proc.
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A2avx2.absorb_avx2_h (to_list rho_prime) ds 31 136).
wp.
ecall (A64avx2.absorb_avx2_h [<:W8.t>] rho_prime 0 136).
wp; call (state_init_avx2_h 136).
auto => |> st0 ? [st1 x2] ??; split; 1: by smt(Array64.size_to_list).
move => ? [st2 x3] /= -> /=; split; 1: by rewrite stavx2_from_st25K.
move => ->; rewrite !stavx2_from_st25K /=;do !congr.
apply (eq_from_nth witness); 1: by rewrite size_to_list /=.
move => i; rewrite size_to_list /= => ib.
by rewrite initiE 1:/# get8_set16_directE //= /#.
qed.

lemma shake256_absorb_66_ll: islossless K.shake256_absorb_66.
proof.
proc.
call keccakf1600_avx2_ll.
call A2avx2.absorb_avx2_ll.
wp.
call A64avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare shake256_absorb_66_ph' _rho_prime _ds :
 [ K.shake256_absorb_66
 : arg.`1 = _rho_prime /\ arg.`2 = _ds
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136
      (to_list _rho_prime ++ to_list _ds)))
 ] = 1%r.
proof.
by conseq shake256_absorb_66_ll (shake256_absorb_66_h' _rho_prime _ds).
qed.

phoare shake256_absorb_66_ph _rho_prime _ds :
 [ M.shake256_absorb_66
 : arg.`1 = _rho_prime /\ arg.`2 = _ds
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136
      (to_list _rho_prime ++ to_list _ds)))
 ] = 1%r.
proof.
by conseq shake256_absorb_66_eq (shake256_absorb_66_ph' _rho_prime _ds) => // /#.
qed.

(* ---------- shake256_absorb_128 ---------- *)

hoare shake256_absorb_128_h' _block :
 K.shake256_absorb_128
 : arg = _block
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _block))).
proof.
proc.
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A128avx2.absorb_avx2_h [<:W8.t>] block 31 136).
wp; call (state_init_avx2_h 136).
auto => |> st0 ? [st1 x2]; rewrite /absorb_spec_avx2  => H; split; 1: by rewrite stavx2_to_st25K /=; smt( stavx2INV_from_st25).
by move => /= ->; rewrite H !stavx2_from_st25K.
qed.

lemma shake256_absorb_128_ll: islossless K.shake256_absorb_128.
proof.
proc.
call keccakf1600_avx2_ll.
call A128avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare shake256_absorb_128_ph' _block :
 [ K.shake256_absorb_128
 : arg = _block
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _block)))
 ] = 1%r.
proof.
by conseq shake256_absorb_128_ll (shake256_absorb_128_h' _block).
qed.

phoare shake256_absorb_128_ph _block :
 [ M.shake256_absorb_128
 : arg = _block
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _block)))
 ] = 1%r.
proof.
by conseq shake256_absorb_128_eq (shake256_absorb_128_ph' _block) => // /#.
qed.

(* ---------- shake256_absorb_commitment_hash ---------- *)

hoare shake256_absorb_commitment_hash_h' _hash :
 K.shake256_absorb_commitment_hash
 : arg = _hash
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _hash))).
proof.
proc.
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A48avx2.absorb_avx2_h [<:W8.t>] hash 31 136).
wp; call (state_init_avx2_h 136).
auto => |> st0 ? [st1 x2]; rewrite /absorb_spec_avx2 => H; split; 1: by rewrite stavx2_to_st25K /=; smt(stavx2INV_from_st25).
by move => /= ->; rewrite H !stavx2_from_st25K.
qed.

lemma shake256_absorb_commitment_hash_ll: islossless K.shake256_absorb_commitment_hash.
proof.
proc.
call keccakf1600_avx2_ll.
call A48avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare shake256_absorb_commitment_hash_ph' _hash :
 [ K.shake256_absorb_commitment_hash
 : arg = _hash
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _hash)))
 ] = 1%r.
proof.
by conseq shake256_absorb_commitment_hash_ll (shake256_absorb_commitment_hash_h' _hash).
qed.

phoare shake256_absorb_commitment_hash_ph _hash :
 [ M.shake256_absorb_commitment_hash
 : arg = _hash
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _hash)))
 ] = 1%r.
proof.
by conseq shake256_absorb_commitment_hash_eq (shake256_absorb_commitment_hash_ph' _hash) => // /#.
qed.


(****************************************************************************)
(* Correctness lemmas (squeeze operations)                                  *)
(****************************************************************************)

(* ---------- squeeze_64_bytes ---------- *)

hoare squeeze_64_bytes_h' _arr _m :
 K.squeeze_64_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array64.of_list witness (SHAKE256 _m 64).
proof.
proc.
ecall (A64avx2.dumpstate_avx2_h _arr 0 64 state).
auto => |> [rr1 rr2] -> ?.
rewrite stavx2_from_st25K.
apply Array64.tP => i Hi /=.
rewrite Array64.get_of_list 1://.
rewrite /SHAKE256 /KECCAK1600 /SQUEEZE1600 /squeezeblocks /squeezestate_i /st_i /squeezestate /SHAKE_DS_BYTE /c512_r8.
have -> : (64 - 1) %/ 136 + 1 = 1 by done.
rewrite -iotaredE /= fillE initiE 1:/# /= Hi /= nth_take 1,2:/# flatten1 nth_take 1,2:/#.
rewrite iter1 /= (nth_change_dfl W8.zero witness); 1: by rewrite size_state2bytes /= /#.
by rewrite state2bytesE.
qed.

lemma squeeze_64_bytes_ll : islossless K.squeeze_64_bytes.
proof.
proc.
call A64avx2.dumpstate_avx2_ll.
by auto.
qed.

phoare squeeze_64_bytes_ph' _arr _m :
 [ K.squeeze_64_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array64.of_list witness (SHAKE256 _m 64)
 ] = 1%r.
proof.
by conseq squeeze_64_bytes_ll (squeeze_64_bytes_h' _arr _m).
qed.

phoare squeeze_64_bytes_correct _arr _m :
 [ M.squeeze_64_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array64.of_list witness (SHAKE256 _m 64)
 ] = 1%r.
proof.
by conseq squeeze_64_bytes_eq (squeeze_64_bytes_ph' _arr _m) => // /#.
qed.

(* ---------- squeeze_128_bytes ---------- *)

(* Given a state that results from absorbing _m with SHAKE256 padding,
   squeeze_128_bytes produces the first 128 bytes of SHAKE256(_m). *)

hoare squeeze_128_bytes_h' _arr _m :
 K.squeeze_128_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array128.of_list witness (SHAKE256 _m 128).
proof.
proc.
ecall (A128avx2.dumpstate_avx2_h _arr 0 128 state).
auto => |> [rr1 rr2] -> ?.
rewrite stavx2_from_st25K.
apply Array128.tP => i Hi /=.
rewrite Array128.get_of_list 1://.
rewrite /SHAKE256 /KECCAK1600 /SQUEEZE1600 /squeezeblocks /squeezestate_i /st_i /squeezestate /SHAKE_DS_BYTE /c512_r8.
have -> : (128 - 1) %/ 136 + 1 = 1 by done.
rewrite -iotaredE /= fillE initiE 1:/# /= Hi /= nth_take 1,2:/# flatten1 nth_take 1,2:/#.
rewrite iter1 /= (nth_change_dfl W8.zero witness); 1: by rewrite size_state2bytes /= /#.
by rewrite state2bytesE.
qed.

lemma squeeze_128_bytes_ll : islossless K.squeeze_128_bytes.
proof.
proc.
call A128avx2.dumpstate_avx2_ll.
by auto.
qed.

phoare squeeze_128_bytes_ph' _arr _m :
 [ K.squeeze_128_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array128.of_list witness (SHAKE256 _m 128)
 ] = 1%r.
proof.
by conseq squeeze_128_bytes_ll (squeeze_128_bytes_h' _arr _m).
qed.

phoare squeeze_128_bytes_correct _arr _m :
 [ M.squeeze_128_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array128.of_list witness (SHAKE256 _m 128)
 ] = 1%r.
proof.
by conseq squeeze_128_bytes_eq (squeeze_128_bytes_ph' _arr _m) => // /#.
qed.

(****************************************************************************)
(* Correctness lemmas (complete hash operations)                            *)
(****************************************************************************)
require import Mldsa_65_prelude.
hoare hash_verification_key_h' _vk :
 K.hash_verification_key
 : arg.`2 = _vk
 ==> res = Array64.of_list witness (Bytes64.to_list (H_tr (BytesPK.of_list (to_list _vk)))).
proof.
proc.
ecall (A64avx2.dumpstate_avx2_h verification_key_hash 0 64 state).
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A1952avx2.absorb_avx2_h [<:W8.t>] verification_key 31 136).
wp; call (state_init_avx2_h 136).
auto => |> &hr st0 ? [st1 x1]; rewrite /absorb_spec_avx2 => Hab; split.
+ by rewrite stavx2_to_st25K; smt(stavx2INV_from_st25).
move => -> [rr1 rr2] /= -> ?.
rewrite Hab !stavx2_from_st25K.
apply Array64.tP => i Hi /=.
rewrite Array64.get_of_list 1://.
rewrite Bytes64.get_to_list /H_tr.
rewrite Bytes64.get_of_list 1://.
rewrite BytesPK.of_listK 1:Array1952.size_to_list; 1: by rewrite mldsa65_kvec /=.
rewrite /SHAKE256 /KECCAK1600 /SQUEEZE1600 /squeezeblocks /squeezestate_i /st_i /squeezestate /SHAKE_DS_BYTE /c512_r8.
have -> : (64 - 1) %/ 136 + 1 = 1 by done.
rewrite -iotaredE /= fillE initiE 1:/# /= Hi /= nth_take 1,2:/# flatten1 nth_take 1,2:/#.
rewrite iter1 /= (nth_change_dfl W8.zero witness); 1: by rewrite size_state2bytes /= /#.
by rewrite state2bytesE. 
qed.

lemma hash_verification_key_ll : islossless K.hash_verification_key.
proof.
proc.
call A64avx2.dumpstate_avx2_ll.
call keccakf1600_avx2_ll.
call A1952avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare hash_verification_key_ph' _vk :
 [ K.hash_verification_key
 : arg.`2 = _vk
 ==> res = Array64.of_list witness (Bytes64.to_list (H_tr (BytesPK.of_list (to_list _vk))))
 ] = 1%r.
proof.
by conseq hash_verification_key_ll (hash_verification_key_h' _vk).
qed.

phoare hash_verification_key_correct _vk :
 [ M.hash_verification_key
 : arg.`2 = _vk
 ==> res = Array64.of_list witness (Bytes64.to_list (H_tr (BytesPK.of_list (to_list _vk))))
 ] = 1%r.
proof.
by conseq hash_verification_key_eq (hash_verification_key_ph' _vk) => // /#.
qed.

hoare derive_commitment_hash_h' _mu _w1 :
 K.__derive_commitment_hash
 : arg.`1 = _mu /\ arg.`2 = _w1
 ==> res = Array48.of_list witness (BytesCT.to_list (H_ct (Bytes64.of_list (to_list _mu)) (BytesW1.of_list (to_list _w1)))).
proof.
proc.
ecall (A48avx2.dumpstate_avx2_h commitment_hash 0 48 state).
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A768avx2.absorb_avx2_h (to_list message_representative) encoded_commitment 31 136).
wp; ecall (A64avx2.absorb_avx2_h [<:W8.t>] message_representative 0 136).
wp; call (state_init_avx2_h 136).
auto => |> st0 ? [st1 x1] ??; split; 1: by smt(Array64.size_to_list).
move => ? [st2 x2]; rewrite /absorb_spec_avx2 => Hab; split.
+ by rewrite stavx2_to_st25K; smt(stavx2INV_from_st25).
move => -> [rr1 rr2] /= -> ?.
rewrite Hab !stavx2_from_st25K.
apply Array48.tP => i Hi /=.
rewrite Array48.get_of_list 1://.
rewrite BytesCT.get_to_list /H_ct.
rewrite BytesCT.get_of_list 1:// mldsa65_lambda 1:/#.
rewrite Bytes64.of_listK 1:Array64.size_to_list // BytesW1.of_listK 1:Array768.size_to_list; 1: by  rewrite mldsa65_kvec.
rewrite /SHAKE256 /KECCAK1600 /SQUEEZE1600 /squeezeblocks /squeezestate_i /st_i /squeezestate /SHAKE_DS_BYTE /c512_r8.
have -> : (48 - 1) %/ 136 + 1 = 1 by done.
rewrite -iotaredE /= fillE initiE 1:/# /= Hi /= nth_take 1,2:/# flatten1 nth_take 1,2:/#.
rewrite iter1 /= (nth_change_dfl W8.zero witness); 1: by rewrite size_state2bytes /= /#.
by rewrite state2bytesE.
qed.

lemma derive_commitment_hash_ll : islossless K.__derive_commitment_hash.
proof.
proc.
call A48avx2.dumpstate_avx2_ll.
call keccakf1600_avx2_ll.
call A768avx2.absorb_avx2_ll.
call A64avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare derive_commitment_hash_ph' _mu _w1 :
 [ K.__derive_commitment_hash
 : arg.`1 = _mu /\ arg.`2 = _w1
 ==> res = Array48.of_list witness (BytesCT.to_list (H_ct (Bytes64.of_list (to_list _mu)) (BytesW1.of_list (to_list _w1))))
 ] = 1%r.
proof.
by conseq derive_commitment_hash_ll (derive_commitment_hash_h' _mu _w1).
qed.

phoare derive_commitment_hash_ph _mu _w1 :
 [ M.__derive_commitment_hash
 : arg.`1 = _mu /\ arg.`2 = _w1
 ==> res = Array48.of_list witness (BytesCT.to_list (H_ct (Bytes64.of_list (to_list _mu)) (BytesW1.of_list (to_list _w1))))
 ] = 1%r.
proof.
by conseq derive_commitment_hash_eq (derive_commitment_hash_ph' _mu _w1) => // /#.
qed.

(* ---------- __keygen_prf ---------- *)

(* Absorbs (randomness || [W8.of_int 6; W8.of_int 5]) with SHAKE256 and
   squeezes 128 bytes. The 6 and 5 are the ML-DSA-65 matrix dimensions
   ROWS_IN_MATRIX_A and COLUMNS_IN_MATRIX_A. *)

hoare keygen_prf_h' _seed :
 K.__keygen_prf
 : arg.`2 = _seed
 ==> res = Array128.of_list witness (SHAKE256 (to_list _seed ++ [W8.of_int 6; W8.of_int 5]) 128).
proof.
proc. 
ecall (squeeze_128_bytes_h' prf_output (to_list _seed ++ [W8.of_int 6; W8.of_int 5])).
ecall (shake256_absorb_34_h' _seed (Array2.of_list witness [W8.of_int 6; W8.of_int 5])).
wp; skip => /> *; split;1: by 
 by smt(Array2.tP Array2.get_of_list Array2.get_setE).
by move => ? /=; congr;congr;congr;congr;rewrite of_listK //=.
qed.

lemma keygen_prf_ll : islossless K.__keygen_prf.
proof.
proc.
call squeeze_128_bytes_ll.
call shake256_absorb_34_ll.
by auto.
qed.

phoare keygen_prf_ph' _seed :
 [ K.__keygen_prf
 : arg.`2 = _seed
 ==> res = Array128.of_list witness (SHAKE256 (to_list _seed ++ [W8.of_int 6; W8.of_int 5]) 128)
 ] = 1%r.
proof.
by conseq keygen_prf_ll (keygen_prf_h' _seed).
qed.

phoare keygen_prf_correct _seed :
 [ M.__keygen_prf
 : arg.`2 = _seed
 ==> res = Array128.of_list witness (SHAKE256 (to_list _seed ++ [W8.of_int 6; W8.of_int 5]) 128)
 ] = 1%r.
proof.
by conseq keygen_prf_eq (keygen_prf_ph' _seed) => // /#.
qed.

lemma K_derive_message_representative_ll : islossless K.__derive_message_representative.
proof.
proc.
call A64updstate.squeeze_updstate_avx2_ll.
wp;call finish_updstate_avx2_ll.
call absorb_m_updstate_avx2_ll.
wp;call absorb_m_updstate_avx2_ll.
wp;call A66updstate.update_updstate_avx2_ll.
wp;call init_updstate_avx2_ll.
by auto.
qed.

hoare K_derive_message_representative_h' _vk_hash _ctx _msg :
  K.__derive_message_representative :
    arg.`1 = _vk_hash /\
    arg.`3 = List.size _ctx /\
    memread Glob.mem arg.`2 arg.`3 = _ctx /\
    arg.`5 = List.size _msg /\
    memread Glob.mem arg.`4 arg.`5 = _msg /\
    arg.`2 + List.size _ctx < W64.modulus /\
    arg.`4 + List.size _msg < W64.modulus
    ==>
    res = Array64.of_list witness (SHAKE256
      (to_list _vk_hash ++ [W8.zero; truncateu8 (W64.of_int (List.size _ctx))]
       ++ _ctx ++ _msg) 64).
proof.
proc.
(* Ecall chain in reverse program order. The strengthened update_h gives us
   rate/trailb invariance, which we need to track ststatus_r8 = 136 through
   to the squeeze precondition. *)
ecall (A64updstate.squeeze_updstate_avx2_h message_representative state 136 len).
wp; ecall (finish_updstate_avx2_h state).
wp; ecall (absorb_m_updstate_avx2_h Glob.mem state buf len).
wp; ecall (absorb_m_updstate_avx2_h Glob.mem state buf len).
wp; ecall (A66updstate.update_updstate_avx2_h [] prefix len state).
wp; ecall (init_updstate_avx2_h state rate64 trailb).
wp; skip => />.
move=> &hr Hctx Hmsg Hctx_bnd Hmsg_bnd.
pose prefix_built := (Array66.init (get8 (set256_direct (WArray66.init8 ("_.[_]" (Array66.init (get8 (set256_direct (WArray66.init8 ("_.[_]" witness<:W8.t Array66.t>)) 0 (get256_direct (WArray64.init8 ("_.[_]" _vk_hash)) 0)))))) 32 (get256_direct (WArray64.init8 ("_.[_]" _vk_hash)) 32)))).[64 <- zero].[65 <- truncateu8 (W64.of_int (size _ctx))].
have prefix_first66 :
  take 66 (to_list prefix_built)
    = to_list _vk_hash ++ [W8.zero; truncateu8 (W64.of_int (size _ctx))].
+ apply (eq_from_nth witness); 1: by rewrite size_cat size_to_list size_take // size_to_list /=.
  move => i; rewrite size_take // size_to_list /= => ib.
  rewrite nth_take 1,2:/# nth_cat size_to_list /=.
  rewrite /prefix_built !get_setE // initiE 1:/# /=.
  case (i < 64) => Hi64.
  + rewrite ifF 1:/# ifF 1:/# /=.
    case (i < 32) => Hi32.
    + by rewrite ifF 1:/# /= /get8 initiE //= initiE //= /set256_direct initiE 1:/# /= ifT 1:/# /get256_direct pack32bE 1:/# initiE 1:/# /= initiE 1:/#.
    + by rewrite ifT 1:/# /get256_direct pack32bE 1:/# initiE 1:/# /= initiE 1:/#.
  by smt().
(* sub prefix_built 0 66 = the first 66 bytes of prefix_built. *)
have prefix_sub66 :
  sub prefix_built 0 66 = take 66 (to_list prefix_built).
+ rewrite /prefix_built.
  apply (eq_from_nth witness);1: by rewrite size_sub // size_take // size_to_list //.
  move => i; rewrite size_sub // => ib.
  by rewrite nth_sub // nth_take 1,2:/# get_to_list.
have prefix_msg :
  sub prefix_built 0 66
    = to_list _vk_hash ++ [W8.zero; truncateu8 (W64.of_int (size _ctx))]
  by rewrite prefix_sub66 prefix_first66.

(* Initial predicate facts from init_pabsorb. *)
have [Hi_p [Hi_r8 Hi_tb]] :=
  init_pabsorb (witness<:W64.t Array26.t>) 17 (W8.of_int 31) _; first smt().

(* Goal at this point: (A) /\ (B), where
   A = pabsorb_spec_updstate_avx2 [] (init_spec witness 17 31) — unfolded
       into the r8/at/pabsorb_spec_ref conjuncts.
   B = implication chain through update post → absorb_m × 2 → finish → squeeze
       → SHAKE256.
*)
split.

(* === A === *)
+ (* pabsorb_spec_updstate_avx2 [] (init_spec witness 17 31) — unfolded. *)
  move: Hi_p; rewrite /pabsorb_spec_updstate_avx2
                     /Keccak1600_ref.pabsorb_spec_ref /=; smt().

(* === B === *)
(* Intro the LHS of the update_h pre (unfolded predicate parts + len bound),
   then forall result0 (= state after update), then the unfolded
   update_h post hypotheses for result0 (predicate parts + Ho_r8_inv +
   Ho_tb_inv giving rate/trailb preservation). *)
move=> _ _ _ _ _ _
       result0 Ho1 Ho2 Ho3 Ho4 Ho5 Ho6 Ho_r8_inv Ho_tb_inv.

(* Refold the unfolded post predicate parts into a single pabsorb fact
   for result0. *)
have Hro_p :
  pabsorb_spec_updstate_avx2 (sub prefix_built 0 66) result0.
+ rewrite /pabsorb_spec_updstate_avx2 /Keccak1600_ref.pabsorb_spec_ref /=.
  smt().

(* Chain through absorb_m × 2 and finish using the bridges. *)
have [Hac_p [Hac_r8 Hac_tb]] := absorb_m_pabsorb Glob.mem{hr} result0
  context_pointer{hr} (size _ctx) (sub prefix_built 0 66)
  Hro_p _ _; 1,2: smt(size_ge0).

have [Ham_p [Ham_r8 Ham_tb]] := absorb_m_pabsorb Glob.mem{hr}
  (absorb_m_updstate_avx2_spec Glob.mem{hr} result0
     context_pointer{hr} (size _ctx))
  message_pointer{hr} (size _msg)
  (sub prefix_built 0 66 ++ memread Glob.mem{hr} context_pointer{hr} (size _ctx))
  Hac_p _ _; 1,2: smt(size_ge0).

have [Hf_eq Hf_r8] := finish_absorb
  (absorb_m_updstate_avx2_spec Glob.mem{hr}
     (absorb_m_updstate_avx2_spec Glob.mem{hr} result0
        context_pointer{hr} (size _ctx))
     message_pointer{hr} (size _msg))
  (sub prefix_built 0 66
     ++ memread Glob.mem{hr} context_pointer{hr} (size _ctx)
     ++ memread Glob.mem{hr} message_pointer{hr} (size _msg))
  Ham_p.

(* Goal now: (r8 of post-finish = 136) /\ ((r8 = 136) => forall result4, ...). *)
split; first by rewrite Hf_r8 Ham_r8 Hac_r8 Ho_r8_inv Hi_r8.
move=> _ result4 Hres4_2 _.

(* Close: substitute squeeze post, apply finish bridge, unfold SHAKE256. *)
rewrite Hres4_2.
apply Array64.tP => i Hi.
rewrite Array64.get_of_list //.
rewrite Hf_eq Ham_r8 Hac_r8 Ho_r8_inv Hi_r8
        Ham_tb Hac_tb Ho_tb_inv Hi_tb.
rewrite prefix_msg Hctx Hmsg -!catA.
rewrite /SHAKE256 /KECCAK1600 /SHAKE_DS_BYTE /c512_r8 get_of_list //.
by rewrite (nth_change_dfl witness); smt(size_SQUEEZE1600).
qed.


phoare K_derive_message_representative_ph' _vk_hash _ctx _msg :
 [ K.__derive_message_representative
 : arg.`1 = _vk_hash /\
   arg.`3 = List.size _ctx /\
   memread Glob.mem arg.`2 arg.`3 = _ctx /\
   arg.`5 = List.size _msg /\
   memread Glob.mem arg.`4 arg.`5 = _msg /\
   arg.`2 + List.size _ctx < W64.modulus /\
   arg.`4 + List.size _msg < W64.modulus
 ==> res = Array64.of_list witness (SHAKE256
       (to_list _vk_hash ++ [W8.zero; truncateu8 (W64.of_int (List.size _ctx))]
        ++ _ctx ++ _msg) 64)
 ] = 1%r.
proof.
by conseq K_derive_message_representative_ll
          (K_derive_message_representative_h' _vk_hash _ctx _msg).
qed.

phoare derive_message_representative_ph _vk_hash _ctx _msg :
 [ M.__derive_message_representative
 : arg.`1 = _vk_hash /\
   arg.`3 = List.size _ctx /\
   memread Glob.mem arg.`2 arg.`3 = _ctx /\
   arg.`5 = List.size _msg /\
   memread Glob.mem arg.`4 arg.`5 = _msg /\
   arg.`2 + List.size _ctx < W64.modulus /\
   arg.`4 + List.size _msg < W64.modulus
 ==> res = Array64.of_list witness (Bytes64.to_list
     (H_mu (Bytes64.of_list (to_list _vk_hash))
           ([W8.zero; truncateu8 (W64.of_int (List.size _ctx))] ++ _ctx ++ _msg)))
 ] = 1%r.
proof.
have Hconseq := (K_derive_message_representative_ph' _vk_hash _ctx _msg).
conseq derive_message_representative_eq Hconseq => |>.
+ move => &1 ???????; exists Glob.mem{1} arg{1}  =>/=;do split;smt(W64.to_uint_cmp pow2_64).
rewrite Bytes64.of_listK;1: by rewrite size_SHAKE256 // Bytes64.to_listK.
congr;congr.
rewrite Bytes64.of_listK;1: by rewrite size_to_list.
by rewrite -!catA /=.
qed.

(* ---------- derive_seed_for_mask ---------- *)

(* Assembles block = k || randomness || mu (128 bytes) using four 256-bit
   AVX2 copies, calls shake256_absorb_128, then squeeze_64_bytes.
   The result is SHAKE256(k || randomness || mu, 64) = H_rhopp(K, coins, mu)
   when rnd_to_list coins = to_list randomness. *)

hoare K_derive_seed_for_mask_h' _k _randomness _mu _arr :
  K.derive_seed_for_mask :
    arg.`1 = _k /\ arg.`2 = _randomness /\ arg.`3 = _mu /\ arg.`4 = _arr
    ==>
    res = Array64.of_list witness
            (SHAKE256 (to_list _k ++ to_list _randomness ++ to_list _mu) 64).
proof.
proc.
ecall (squeeze_64_bytes_h' seed_for_mask (to_list _k ++ to_list _randomness ++ to_list _mu)).
wp; ecall (shake256_absorb_128_h' block).
wp; skip => />.
congr; congr;congr;  apply (eq_from_nth witness).
  + by rewrite size_to_list !size_cat !size_to_list /=.
  move => i; rewrite size_to_list /= => Hi.
  rewrite !nth_cat !size_to_list !size_cat !size_to_list.
  case (i < 32) => Hi32.
  + rewrite ifT 1:/#.
    rewrite /get256_direct /set256_direct /get8 /pack32_t /(\bits8) wordP => k kb.
    by rewrite !initiE 1:/# /= !initiE 1:/# /= !initiE 1..3:/# /= ifF 1:/# ifF 1:/# !initiE 1..3:/# /= ifF 1:/# initiE 1:/# initiE 1:/# initiE 1:/# /= ifT 1:/# initiE 1:/# /= initiE 1:/# /= initiE 1:/# initiE 1:/# /#.
  case (i < 64) => Hi64.
  + (* 32 <= i < 64: from randomness[i-32] via set256_direct at offset 32 — ifF(96) ifF(64) ifT(32) *)
    rewrite /get256_direct /set256_direct /get8 /pack32_t /(\bits8) wordP => k kb.
    by rewrite !initiE 1:/# /= !initiE 1:/# /= !initiE 1..3:/# /= ifF 1:/# ifF 1:/# !initiE 1..3:/# /= ifT 1:/# initiE 1:/# /= initiE 1:/# /= initiE 1:/# initiE 1:/# /#.
  case (i < 96) => Hi96.
  + (* 64 <= i < 96: from mu[i-64] via set256_direct at offset 64 — ifF(96) ifT(64) *)
    rewrite /get256_direct /set256_direct /get8 /pack32_t /(\bits8) wordP => k kb.
    by rewrite !initiE 1:/# /= !initiE 1:/# /= !initiE 1..3:/# /= ifF 1:/# !initiE 1..3:/# /= ifT 1:/# initiE 1:/# /= initiE 1:/# /= initiE 1:/# initiE 1:/# /#.
  + (* 96 <= i < 128: from mu[i-64] via set256_direct at offset 96 — ifT(96) *)
    rewrite /get256_direct /set256_direct /get8 /pack32_t /(\bits8) wordP => k kb.
    rewrite !initiE 1:/# /= !initiE 1:/# /= !initiE 1..3:/# /= ifT 1:/# initiE 1:/# /= initiE 1:/# /= ifF 1:/# initiE 1:/# /= initiE 1:/# /#.
qed.

lemma K_derive_seed_for_mask_ll : islossless K.derive_seed_for_mask.
proof.
proc.
call squeeze_64_bytes_ll.
call shake256_absorb_128_ll.
by auto.
qed.

phoare K_derive_seed_for_mask_ph' _k _randomness _mu _arr :
 [ K.derive_seed_for_mask
 : arg.`1 = _k /\ arg.`2 = _randomness /\ arg.`3 = _mu /\ arg.`4 = _arr
 ==> res = Array64.of_list witness
             (SHAKE256 (to_list _k ++ to_list _randomness ++ to_list _mu) 64)
 ] = 1%r.
proof.
by conseq K_derive_seed_for_mask_ll (K_derive_seed_for_mask_h' _k _randomness _mu _arr).
qed.

phoare derive_seed_for_mask_ph _k _randomness _mu _arr :
  [ M.derive_seed_for_mask :
    arg.`1 = _k /\ arg.`2 = _randomness /\ arg.`3 = _mu /\ arg.`4 = _arr
    ==>
    res = Array64.of_list witness
            (SHAKE256 (to_list _k ++ to_list _randomness ++ to_list _mu) 64)
  ] = 1%r.
proof.
by conseq derive_seed_for_mask_eq (K_derive_seed_for_mask_ph' _k _randomness _mu _arr) => // /#.
qed.
