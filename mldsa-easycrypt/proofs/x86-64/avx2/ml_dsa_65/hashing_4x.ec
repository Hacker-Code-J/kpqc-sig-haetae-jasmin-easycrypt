require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat Symmetric Sampling MLDSA_W32_Rep MLDSA.
import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq.

require import Array2 Array4 Array32 Array64 Array136 Array168.
require import WArray2 WArray32 WArray64 WArray136 WArray168.

(****************************************************************************)
(* Clone KeccakArrayAvx2x4 for each array size used in hashing_4x.jinc     *)
(* (Keccak1600_fixedsizes_avx2x4 re-exports Keccak1600_avx2x4, so          *)
(*  absorb_spec_avx2x4 and Keccak1600_Jazz.M are available from here)       *)
(****************************************************************************)

from Keccak require import Keccak1600_fixedsizes_avx2x4.

(****************************************************************************)
(* Establish that M's 4x keccak primitives equal Keccak1600_Jazz.M          *)
(****************************************************************************)

equiv state_init_avx2x4_eq:
 M.__state_init_avx2x4 ~ Keccak1600_Jazz.M.__state_init_avx2x4
 : ={arg} ==> ={res}
 by sim.

equiv keccakf1600_avx2x4_eq:
 M._keccakf1600_avx2x4 ~ Keccak1600_Jazz.M._keccakf1600_avx2x4
 : ={arg} ==> ={res}
 by sim.

clone KeccakArrayAvx2x4 as A2avx2x4
 with op _ASIZE <- 2,
      theory A <- Array2,
      theory WA <- WArray2
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2x4 as A32avx2x4
 with op _ASIZE <- 32,
      theory A <- Array32,
      theory WA <- WArray32
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2x4 as A64avx2x4
 with op _ASIZE <- 64,
      theory A <- Array64,
      theory WA <- WArray64
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2x4 as A136avx2x4
 with op _ASIZE <- 136,
      theory A <- Array136,
      theory WA <- WArray136
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2x4 as A168avx2x4
 with op _ASIZE <- 168,
      theory A <- Array168,
      theory WA <- WArray168
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

(****************************************************************************)
(* Equiv lemmas: M.primitive ~ KeccakArray.MM.primitive                     *)
(****************************************************************************)

equiv a2__absorb_avx2x4_eq:
 M.a2____absorb_avx2x4 ~ A2avx2x4.MM.__absorb_avx2x4
 : ={arg} ==> ={res}
 by sim.

equiv a32__absorb_bcast_avx2x4_eq:
 M.a32____absorb_bcast_avx2x4 ~ A32avx2x4.MM.__absorb_bcast_avx2x4
 : ={arg} ==> ={res}
 by sim.

equiv a64__absorb_bcast_avx2x4_eq:
 M.a64____absorb_bcast_avx2x4 ~ A64avx2x4.MM.__absorb_bcast_avx2x4
 : ={arg} ==> ={res}
 by sim.

equiv a136__dumpstate_avx2x4_eq:
 M.a136____dumpstate_avx2x4 ~ A136avx2x4.MM.__dumpstate_avx2x4
 : ={arg} ==> ={res}
 by sim.

equiv a168__dumpstate_avx2x4_eq:
 M.a168____dumpstate_avx2x4 ~ A168avx2x4.MM.__dumpstate_avx2x4
 : ={arg} ==> ={res}
 by sim.

(****************************************************************************)
(* Module K: keccak-library wrapper mirroring M's 4x hashing procedures     *)
(****************************************************************************)

module K = {

  proc shake128_absorb_34_4x (state:W256.t Array25.t, rho:W8.t Array32.t,
                              domain_separators:W16.t Array4.t) :
  W256.t Array25.t = {
    var d0:W8.t Array2.t;
    var d1:W8.t Array2.t;
    var d2:W8.t Array2.t;
    var d3:W8.t Array2.t;
    var  _0:int;
    var  _1:int;
    d0 <- witness;
    d1 <- witness;
    d2 <- witness;
    d3 <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2x4 (state);
    (state,  _0) <@ A32avx2x4.MM.__absorb_bcast_avx2x4 (state, 0, rho, 0, 168);
    d0 <-
    (Array2.init
    (WArray2.get8
    (WArray2.set16 (WArray2.init8 (fun i => d0.[i])) 0 domain_separators.[0])
    ));
    d1 <-
    (Array2.init
    (WArray2.get8
    (WArray2.set16 (WArray2.init8 (fun i => d1.[i])) 0 domain_separators.[1])
    ));
    d2 <-
    (Array2.init
    (WArray2.get8
    (WArray2.set16 (WArray2.init8 (fun i => d2.[i])) 0 domain_separators.[2])
    ));
    d3 <-
    (Array2.init
    (WArray2.get8
    (WArray2.set16 (WArray2.init8 (fun i => d3.[i])) 0 domain_separators.[3])
    ));
    (state,  _1) <@ A2avx2x4.MM.__absorb_avx2x4 (state, 32, d0, d1, d2, d3, 31, 168);
    return state;
  }

  proc shake256_absorb_66_4x (state:W256.t Array25.t,
                              rho_prime:W8.t Array64.t,
                              starting_domain_separator:W16.t) :
  W256.t Array25.t = {
    var t:W16.t;
    var d0:W8.t Array2.t;
    var d1:W8.t Array2.t;
    var d2:W8.t Array2.t;
    var d3:W8.t Array2.t;
    var  _0:int;
    var  _1:int;
    d0 <- witness;
    d1 <- witness;
    d2 <- witness;
    d3 <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2x4 (state);
    (state,  _0) <@ A64avx2x4.MM.__absorb_bcast_avx2x4 (state, 0, rho_prime, 0, 136);
    t <- starting_domain_separator;
    d0 <-
    (Array2.init
    (WArray2.get8 (WArray2.set16 (WArray2.init8 (fun i => d0.[i])) 0 t)));
    t <- (t + (W16.of_int 1));
    d1 <-
    (Array2.init
    (WArray2.get8 (WArray2.set16 (WArray2.init8 (fun i => d1.[i])) 0 t)));
    t <- (t + (W16.of_int 1));
    d2 <-
    (Array2.init
    (WArray2.get8 (WArray2.set16 (WArray2.init8 (fun i => d2.[i])) 0 t)));
    t <- (t + (W16.of_int 1));
    d3 <-
    (Array2.init
    (WArray2.get8 (WArray2.set16 (WArray2.init8 (fun i => d3.[i])) 0 t)));
    (state,  _1) <@ A2avx2x4.MM.__absorb_avx2x4 (state, 64, d0, d1, d2, d3, 31, 136);
    return state;
  }

  proc shake128_squeezeblock4x (state:W256.t Array25.t,
                                h0:W8.t Array168.t, h1:W8.t Array168.t,
                                h2:W8.t Array168.t, h3:W8.t Array168.t) :
  W256.t Array25.t * W8.t Array168.t * W8.t Array168.t *
  W8.t Array168.t * W8.t Array168.t = {
    var offset:int;
    var  _0:int;
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2x4 (state);
    offset <- 0;
    (h0, h1, h2, h3,  _0) <@ A168avx2x4.MM.__dumpstate_avx2x4 (h0, h1, h2, h3,
    offset, 168, state);
    return (state, h0, h1, h2, h3);
  }

  proc shake256_squeezeblock4x (state:W256.t Array25.t,
                                h0:W8.t Array136.t, h1:W8.t Array136.t,
                                h2:W8.t Array136.t, h3:W8.t Array136.t) :
  W256.t Array25.t * W8.t Array136.t * W8.t Array136.t *
  W8.t Array136.t * W8.t Array136.t = {
    var offset:int;
    var  _0:int;
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2x4 (state);
    offset <- 0;
    (h0, h1, h2, h3,  _0) <@ A136avx2x4.MM.__dumpstate_avx2x4 (h0, h1, h2, h3,
    offset, 136, state);
    return (state, h0, h1, h2, h3);
  }

}.

(****************************************************************************)
(* Equiv lemmas: M.proc ~ K.proc                                            *)
(****************************************************************************)

equiv shake128_absorb_34_4x_eq:
 M.shake128_absorb_34_4x ~ K.shake128_absorb_34_4x
 : ={arg} ==> ={res}
 by sim.

equiv shake256_absorb_66_4x_eq:
 M.shake256_absorb_66_4x ~ K.shake256_absorb_66_4x
 : ={arg} ==> ={res}
 by sim.

equiv shake128_squeezeblock4x_eq:
 M.shake128_squeezeblock4x ~ K.shake128_squeezeblock4x
 : ={arg} ==> ={res}
 by sim.

equiv shake256_squeezeblock4x_eq:
 M.shake256_squeezeblock4x ~ K.shake256_squeezeblock4x
 : ={arg} ==> ={res}
 by sim.

(****************************************************************************)
(* Correctness lemmas (absorbed-state characterization)                     *)
(****************************************************************************)

hoare shake128_absorb_34_4x_h' _rho _ds :
 K.shake128_absorb_34_4x
 : arg.`2 = _rho /\ arg.`3 = _ds
 ==>
   absorb_spec_avx2x4 168 31
     (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds.[0]))))
      (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds.[1]))))
      (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0_ds.[2]))))
      (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds.[3]))))
     res.
proof.
proc.
ecall (A2avx2x4.absorb_avx2x4_h (to_list _rho) (to_list _rho) (to_list _rho) (to_list _rho) state d0 d1 d2 d3 31 168).
wp.
ecall (A32avx2x4.absorb_bcast_avx2x4_h [<:W8.t>] [<:W8.t>] [<:W8.t>] [<:W8.t>] state rho 0 168).
wp; call (state_init_avx2x4_h 168).
by auto => |>;smt(Array32.size_to_list).
qed.

lemma shake128_absorb_34_4x_ll : islossless K.shake128_absorb_34_4x.
proof.
proc.
call A2avx2x4.absorb_avx2x4_ll.
wp.
call A32avx2x4.absorb_bcast_avx2x4_ll.
call state_init_avx2x4_ll.
by auto.
qed.

phoare shake128_absorb_34_4x_ph' _rho _ds :
 [ K.shake128_absorb_34_4x
 : arg.`2 = _rho /\ arg.`3 = _ds
 ==>
   absorb_spec_avx2x4 168 31
     (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds.[0]))))
      (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds.[1]))))
      (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0_ds.[2]))))
      (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds.[3]))))
     res
 ] = 1%r.
proof.
by conseq shake128_absorb_34_4x_ll (shake128_absorb_34_4x_h' _rho _ds).
qed.

phoare shake128_absorb_34_4x_ph _rho _ds :
 [ M.shake128_absorb_34_4x
 : arg.`2 = _rho /\ arg.`3 = _ds
 ==>
   absorb_spec_avx2x4 168 31
     (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds.[0]))))
      (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds.[1]))))
      (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0_ds.[2]))))
      (to_list _rho ++ to_list (Array2.init (get8 (set16_direct (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds.[3]))))
     res
 ] = 1%r.
proof.
by conseq shake128_absorb_34_4x_eq (shake128_absorb_34_4x_ph' _rho _ds) => // /#.
qed.

hoare shake256_absorb_66_4x_h' _rho_prime _ds0 :
 K.shake256_absorb_66_4x
 : arg.`2 = _rho_prime /\ arg.`3 = _ds0
 ==>
   absorb_spec_avx2x4 136 31
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds0))))
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness))  0 (_ds0 + W16.one)))))
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness))  0 (_ds0 + (W16.of_int 2))))))
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness))  0 (_ds0 + (W16.of_int 3))))))
     res.
proof.
proc.
ecall (A2avx2x4.absorb_avx2x4_h (to_list _rho_prime) (to_list _rho_prime) (to_list _rho_prime) (to_list _rho_prime) state d0 d1 d2 d3 31 136).
wp.
ecall (A64avx2x4.absorb_bcast_avx2x4_h [<:W8.t>] [<:W8.t>] [<:W8.t>] [<:W8.t>] state rho_prime 0 136).
wp; call (state_init_avx2x4_h 136).
auto => |> r0 ? r1 Hinit ?; rewrite size_to_list /#.
qed.

lemma shake256_absorb_66_4x_ll : islossless K.shake256_absorb_66_4x.
proof.
proc.
call A2avx2x4.absorb_avx2x4_ll.
wp.
call A64avx2x4.absorb_bcast_avx2x4_ll.
call state_init_avx2x4_ll.
by auto.
qed.

phoare shake256_absorb_66_4x_ph' _rho_prime _ds0 :
 [ K.shake256_absorb_66_4x
 : arg.`2 = _rho_prime /\ arg.`3 = _ds0
 ==>
   absorb_spec_avx2x4 136 31
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds0))))
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness))  0 (_ds0 + W16.one)))))
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness))  0 (_ds0 + (W16.of_int 2))))))
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness))  0 (_ds0 + (W16.of_int 3))))))
     res
 ] = 1%r.
proof.
by conseq shake256_absorb_66_4x_ll (shake256_absorb_66_4x_h' _rho_prime _ds0).
qed.

phoare shake256_absorb_66_4x_ph _rho_prime _ds0 :
 [ M.shake256_absorb_66_4x
 : arg.`2 = _rho_prime /\ arg.`3 = _ds0
 ==>
   absorb_spec_avx2x4 136 31
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness)) 0 _ds0))))
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness))  0 (_ds0 + W16.one)))))
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness))  0 (_ds0 + (W16.of_int 2))))))
     (to_list _rho_prime ++ to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (Array2."_.[_]" witness))  0 (_ds0 + (W16.of_int 3))))))
     res
 ] = 1%r.
proof.
by conseq shake256_absorb_66_4x_eq (shake256_absorb_66_4x_ph' _rho_prime _ds0) => // /#.
qed.
