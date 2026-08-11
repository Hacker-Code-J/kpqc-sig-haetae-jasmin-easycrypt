require import AllCore BitEncoding List RealExp IntDiv.
from Jasmin require import JWord JByte_array.


require import Parameters GFq Rq VecMat Conversion.
import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq MLDSAParams.
import BitChunking Array256.

abbrev q_bits = 23.
lemma q_bitlenl : 2^(q_bits-1) < q-1 <= 2^(q_bits) by auto.

abbrev noise_bits = if Eta = 4 then 4 else 3.
lemma noise_bitlen :  2^(noise_bits-1) < 2*Eta+1 (* signed range + 1 *) <= 2^(noise_bits)
  by  have/= H := param_sets; elim H => /> ??????-> /=.

(* noise_bits is the bit width used by BitPack/BitUnpack for eta-bounded coefficients. *)
lemma noise_bits_eq : noise_bits = ilog 2 (Eta + Eta) + 1.
proof. by have/= H := param_sets; elim H => /> ??????->. qed.

abbrev gamma1_bits = 20.
lemma gamma1_bitlen :  2^(gamma1_bits-1) < 2*gamma1 (* signed range *) <= 2^(gamma1_bits)
  by  have/= H := param_sets; elim H => /> ??->???? /=.

abbrev w1_bits = 4.
lemma w1_bitlen : 2^(w1_bits-1) < (q-1) %/ (2*gamma2) - 1 <= 2^(w1_bits)
  by  have/= H := param_sets; elim H => /> ???->???? /=.


abbrev s1_bytes = (n * noise_bits * lvec) %/ 8.

abbrev t_bytes = (n * (q_bits-d) * kvec) %/ 8.

abbrev s2_bytes = (n * noise_bits * kvec) %/ 8.

abbrev t0_bytes = (n * d * kvec) %/ 8.

abbrev hint_bytes = w_hint + kvec.

abbrev z_bytes = (n * gamma1_bits * lvec) %/ 8.

abbrev sk_bytes = 32 + 32 + 64 + s1_bytes + s2_bytes + t0_bytes.
abbrev pk_bytes = 32 + t_bytes.
abbrev sig_bytes = lambda %/ 4 + z_bytes + hint_bytes.

abbrev w1_bytes = (n * w1_bits * kvec) %/ 8.


(* Size of BitsToBytes / SimpleBitPack outputs (used by key-length proofs
   and by the encode-pack correctness bridges in verify.ec / sign.ec). *)
lemma size_BitsToBytes' (l : bool list) : size (BitsToBytes l) = size l %/ 8
  by rewrite /BitsToBytes size_map size_chunk //.

lemma size_SimpleBitPack' (_p : poly) (b : int) :
  1 <= b => size (SimpleBitPack _p b) = (ilog 2 b + 1) * n %/ 8.
proof.
move => Hb.
rewrite /SimpleBitPack /= size_BitsToBytes' (size_flatten_ctt (ilog 2 b + 1)).
+ move => l; rewrite mapP => He; elim He => c /= [# ?->].
  by rewrite /IntegerToBits BS2Int.size_int2bs; smt(ilog_ge0).
by rewrite size_map size_to_list.
qed.


(*
ML-DSA-44 2560 1312 2420
ML-DSA-65 4032 1952 3309
ML-DSA-87 4896 2592 4627
*)

lemma key_sizes : (sk_bytes, pk_bytes, sig_bytes) \in [ (* (2560,1312,2420); *)
                                                           (4032,1952,3309);
                                                           (4896,2592,4627)]
  by  have /= H:= param_sets;elim H =>  [#] ?->??-> ->->-> /=. 


clone import JArray.MonoArray as Bytes32 with op size <= 32, type elem <= W8.t, op dfl <= witness.
clone import JArray.MonoArray as Bytes64 with op size <= 64, type elem <= W8.t, op dfl <= witness.
clone import JArray.MonoArray as BytesSK with op size <= sk_bytes, type elem <= W8.t, op dfl <= witness.
clone import JArray.MonoArray as BytesPK with op size <= pk_bytes, type elem <= W8.t, op dfl <= witness.
clone import JArray.MonoArray as BytesSig with op size <= sig_bytes, type elem <= W8.t, op dfl <= witness.
clone import JArray.MonoArray as BytesCT with op size <= lambda %/ 4, type elem <= W8.t, op dfl <= witness.
clone import JArray.MonoArray as BytesW1 with op size <= w1_bytes, type elem <= W8.t, op dfl <= witness.

(* Validity predicate on sk: its s2 slice decodes to polynomials in [-Eta, Eta].
   Each of the kvec chunks (of size (n*noise_bits)/8) encodes a polynomial whose
   nibbles are all in [0, 2*Eta].  Together with skDecode this gives
   infnorm_lt s2 (Eta+1) via BitUnpack_infnorm. *)
op valid_sk_s2 (sk : BytesSK.t) : bool =
    forall k, 0 <= k < kvec =>
       valid_eta_bytes (take ((n * noise_bits) %/ 8)
                             (drop (128 + s1_bytes + k * ((n * noise_bits) %/ 8))
                                   (BytesSK.to_list sk))).

module PkEncDec = {
  proc pkEncode(rho : Bytes32.t, t1 : polykvec) : BytesPK.t = {
    var i, ti, pkbytes, pk;
    pkbytes <- to_list rho;
    i <- 0;
    while (i < kvec) {
      ti <- SimpleBitPack t1.[i] (2^((q_bits-d)) - 1) ;
      pkbytes <- pkbytes ++ ti;
      i <- i + 1;
    }
    pk <- BytesPK.of_list pkbytes;
    return pk;
  }

  proc pkDecode(pk :  BytesPK.t) :  Bytes32.t * polykvec = {
    var i, rho, ti;
    var t : polykvec;
    t <- witness;
    rho <- Bytes32.of_list (take 32 (to_list pk));
    i <- 0;
    while (i < kvec) {
      ti <- SimpleBitUnpack (take ((n * (q_bits-d)) %/ 8) (drop (((n * (q_bits-d)) %/ 8)*i + 32) (to_list pk))) (2^(q_bits - d)-1);
      t <- t.[i <- ti];
      i <- i + 1;
    }
    return (rho,t);
  }

}.

lemma pkEncode_corr _rho _t1 :
    phoare [ PkEncDec.pkEncode : arg = (_rho,_t1) ==>
              res = BytesPK.of_list (Bytes32.to_list _rho ++ (flatten (map (fun p => SimpleBitPack p (2^((q_bits-d)) - 1)) (to_list _t1)))) ] = 1%r.
proof.
proc.
have /= pars:= param_sets.
wp; while (0 <= i <= kvec /\ t1 = _t1 /\
       pkbytes = to_list _rho ++ (flatten (map (fun (p : poly) => SimpleBitPack p (2 ^ (q_bits - d) - 1)) (take i (to_list _t1))))) (kvec - i); last first.
+ auto => />;split;1: smt(take0 flatten_nil cats0).
  by smt(KArray.size_to_list take_oversize).
move => z; auto => /> &hr *; do split;1,2,4:smt().
rewrite (take_nth witness) /=;1: by rewrite size_to_list /#.
by rewrite -cats1 map_cat flatten_cat map1 flatten1 /= !catA.
qed.

lemma pkDecode_corr _pk :
    phoare [ PkEncDec.pkDecode : arg = _pk ==>
            res.`1 = Bytes32.of_list (take 32 (to_list _pk))
         /\ res.`2 = KArray.init (fun i =>
                SimpleBitUnpack (take ((n * (q_bits-d)) %/ 8) (drop (((n * (q_bits-d)) %/ 8)*i + 32) (to_list _pk))) (2^(q_bits - d)-1))] = 1%r.
proc.
have /= pars:= param_sets.
while (0 <= i <= kvec /\ pk = _pk /\
    forall k, 0 <= k < i =>
     t.[k] = SimpleBitUnpack (take ((n * (q_bits-d)) %/ 8) (drop (((n * (q_bits-d)) %/ 8)*k + 32) (to_list _pk))) (2 ^ (q_bits - d) - 1)) (kvec - i); last first.
+ auto => />; do split;1,2:smt().
  + move => i t; do split;1:smt().
  move => ??? H;rewrite tP => k kb.
  by rewrite initiE 1:/# /= /#.
move => z;auto => /> &hr *;do split;1,2,4:smt().
by move => k kbl kbh;rewrite get_setE /#.
qed.

module SkEncDec = {
  proc skEncode(rho k : Bytes32.t, tr : Bytes64.t, s1 : polylvec, s2 t0 : polykvec)
    : BytesSK.t = {
    var i, skbytes, ski,sk; 
    skbytes <- to_list rho ++ to_list k ++ to_list tr;
    i <- 0;
    while (i < lvec) {
      ski <- BitPack s1.[i] Eta Eta;
      skbytes <- skbytes ++ ski;
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitPack s2.[i] Eta Eta;
      skbytes <- skbytes ++ ski;
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitPack t0.[i] (2^(d-1)-1) (2^(d-1));
      skbytes <- skbytes ++ ski;
      i <- i + 1;
    }
    sk <- BytesSK.of_list skbytes;
    return sk;
  }

  proc skDecode(sk : BytesSK.t) : Bytes32.t * Bytes32.t * Bytes64.t * polylvec * polykvec * polykvec = {
    var rho, k, tr,ski, i;
    var s1 : polylvec;
    var  s2,t0 : polykvec;  
    s1 <- witness;
    s2 <- witness;
    t0 <- witness;
    rho <- Bytes32.of_list (take 32 (to_list sk)); 
    k <- Bytes32.of_list (take 32 (drop 32 (to_list sk)));
    tr <- Bytes64.of_list (take 64 (drop 64 (to_list sk)));
    i <- 0;
    while (i < lvec) {
      ski <- BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + i*((n * noise_bits) %/ 8)) (to_list sk))) Eta Eta;
      s1 <- s1.[i <- ski];
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + s1_bytes + i*((n * noise_bits) %/ 8)) (to_list sk))) Eta Eta;
      s2 <- s2.[i <- ski];
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitUnpack (take ((n * d) %/ 8) (drop (128 + s1_bytes + s2_bytes + i*(n * d) %/ 8) (to_list sk))) (2^(d-1)-1) (2^(d-1));
      t0 <- t0.[i <- ski];
      i <- i + 1;
    }
    return (rho,k,tr,s1,s2,t0);  
  }
}.

lemma skEncode_corr _rho _k _tr _s1 _s2 _t0 :
    phoare [ SkEncDec.skEncode : arg = (_rho,_k,_tr,_s1,_s2,_t0) ==>
              res = BytesSK.of_list
              (Bytes32.to_list _rho ++ Bytes32.to_list _k ++ Bytes64.to_list _tr
              ++  (flatten (map (fun p => BitPack p Eta Eta) (to_list _s1)))
              ++  (flatten (map (fun p => BitPack p Eta Eta) (to_list _s2)))
              ++  (flatten (map (fun p => BitPack p  (2^(d-1)-1) (2^(d-1))) (to_list _t0))))
              ] = 1%r.
proof.
proc.
have /= pars:= param_sets.

wp; while (0 <= i <= kvec /\ t0 = _t0 /\
       skbytes = to_list _rho ++ to_list _k ++ to_list _tr ++ flatten (map (fun (p : poly) => BitPack p Eta Eta) (to_list _s1)) ++
     flatten (map (fun (p : poly) => BitPack p Eta Eta) (to_list _s2)) ++
     flatten (map (fun (p : poly) => BitPack p 4095 4096) (take i (to_list _t0)))) (kvec - i).
+ move => z; auto => /> &hr *; do split;1,2,4:smt().
  rewrite (take_nth witness) /=;1: by rewrite size_to_list /#.
  by rewrite -cats1 map_cat flatten_cat map1 flatten1 /= !catA.

wp;conseq (: _ ==> 
   skbytes =
   to_list _rho ++ to_list _k ++ to_list _tr ++ flatten (map (fun (p : poly) => BitPack p Eta Eta) (to_list _s1)) ++
   flatten (map (fun (p : poly) => BitPack p Eta Eta) (to_list _s2))).
+ auto => />; do split;1,2:smt(take0 cats0).
  + by rewrite take0 /= flatten_nil cats0.
  move => i; do split;1:smt().
  by move => *;rewrite take_oversize ?size_to_list /#.

wp; while (0 <= i <= kvec /\ s2 = _s2 /\
       skbytes = to_list _rho ++ to_list _k ++ to_list _tr ++ flatten (map (fun (p : poly) => BitPack p Eta Eta) (to_list _s1)) ++
     flatten (map (fun (p : poly) => BitPack p Eta Eta) (take i (to_list _s2)))) (kvec - i).
+ move => z; auto => /> &hr *; do split;1,2,4:smt().
  rewrite (take_nth witness) /=;1: by rewrite size_to_list /#.
  by rewrite -cats1 map_cat flatten_cat map1 flatten1 /= !catA.

  wp;conseq (: _ ==> 
   skbytes =
   to_list _rho ++ to_list _k ++ to_list _tr ++ flatten (map (fun (p : poly) => BitPack p Eta Eta) (to_list _s1))).
+ auto => />; do split;1,2:smt(take0 cats0).
  + by rewrite take0 /= flatten_nil cats0.
  move => i; do split;1:smt().
  by move => *;rewrite take_oversize ?size_to_list /#.

wp; while (0 <= i <= kvec /\ s1 = _s1 /\
       skbytes = to_list _rho ++ to_list _k ++ to_list _tr ++ flatten (map (fun (p : poly) => BitPack p Eta Eta) (take i (to_list _s1)))) (kvec - i).
+ move => z; auto => /> &hr *; do split;1,2,4:smt().
  rewrite (take_nth witness) /=;1: by rewrite size_to_list /#.
  by rewrite -cats1 map_cat flatten_cat map1 flatten1 /= !catA.

auto => />; do split;1,2:smt(take0 cats0).
move => *; do split;1:smt().
by move => *;rewrite take_oversize ?size_to_list /#.
qed.

lemma skDecode_corr _sk :
    phoare [ SkEncDec.skDecode : arg = _sk ==>
            res.`1 = Bytes32.of_list (take 32 (to_list _sk))
         /\ res.`2 = Bytes32.of_list (take 32 (drop 32 (to_list _sk)))
         /\ res.`3 = Bytes64.of_list (take 64 (drop 64 (to_list _sk)))
         /\ res.`4 = LArray.init (fun i => BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + i * (n * noise_bits) %/ 8) (to_list _sk))) Eta Eta)
         /\ res.`5 = KArray.init (fun i => BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + s1_bytes + i*((n * noise_bits) %/ 8)) (to_list _sk))) Eta Eta)
         /\ res.`6 = KArray.init (fun i => BitUnpack (take ((n * d) %/ 8) (drop (128 + s1_bytes + s2_bytes + i*((n * d) %/ 8)) (to_list _sk))) (2^(d-1)-1) (2^(d-1)))
          ] = 1%r.
proc.
have /= pars:= param_sets.
seq 3 : #pre;[1,2,5:by auto | 4: by hoare;auto].

while (0 <= i <= kvec /\ sk = _sk /\
 rho = Bytes32.of_list (take 32 (to_list _sk)) /\
  k = Bytes32.of_list (take 32 (drop 32 (to_list _sk))) /\
  tr = Bytes64.of_list (take 64 (drop 64 (to_list _sk))) /\
  s1 =
  LArray.init
    (fun (i0 : int) =>
       BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + i0 * (n * noise_bits) %/ 8) (to_list _sk))) Eta Eta) /\
  s2 =
  KArray.init
    (fun (i0 : int) =>
       BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + s1_bytes + i0 * ((n * noise_bits) %/ 8)) (to_list _sk)))
         Eta Eta) /\
    forall k, 0 <= k < i =>
     t0.[k] = BitUnpack (take 416 (drop (128 + s1_bytes + s2_bytes + k * ((n * d) %/ 8)) (to_list _sk))) 4095 4096) (kvec - i).
+ move => z;auto => /> &hr *;do split;1,2,4:smt().
  by move => k kbl kbh;rewrite get_setE /#.

wp;conseq (: _ ==>
   rho = Bytes32.of_list (take 32 (to_list _sk)) /\
  k = Bytes32.of_list (take 32 (drop 32 (to_list _sk))) /\
  tr = Bytes64.of_list (take 64 (drop 64 (to_list _sk))) /\
  s1 =
  LArray.init
    (fun (i0 : int) =>
       BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + i0 * (n * noise_bits) %/ 8) (to_list _sk))) Eta Eta) /\
  s2 =
  KArray.init
    (fun (i0 : int) =>
       BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + s1_bytes + i0 * ((n * noise_bits) %/ 8)) (to_list _sk)))
         Eta Eta)).
+ auto => /> &hr; do split;1,2:smt().
  move => i t0;do split;1:smt().
  move => *;rewrite tP => k kb.
  by rewrite initiE 1:/# /= /#.

while (0 <= i <= kvec /\ sk = _sk /\
 rho = Bytes32.of_list (take 32 (to_list _sk)) /\
  k = Bytes32.of_list (take 32 (drop 32 (to_list _sk))) /\
  tr = Bytes64.of_list (take 64 (drop 64 (to_list _sk))) /\
  s1 =
  LArray.init
    (fun (i0 : int) =>
       BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + i0 * (n * noise_bits) %/ 8) (to_list _sk))) Eta Eta) /\
    forall k, 0 <= k < i =>
     s2.[k] = BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + s1_bytes + k * ((n * noise_bits) %/ 8)) (to_list _sk))) Eta Eta) (kvec - i).
+ move => z;auto => /> &hr *;do split;1,2,4:smt().
  by move => k kbl kbh;rewrite get_setE /#.

wp;conseq (: _ ==>
   rho = Bytes32.of_list (take 32 (to_list _sk)) /\
  k = Bytes32.of_list (take 32 (drop 32 (to_list _sk))) /\
  tr = Bytes64.of_list (take 64 (drop 64 (to_list _sk))) /\
  s1 =
  LArray.init
    (fun (i0 : int) =>
       BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + i0 * (n * noise_bits) %/ 8) (to_list _sk))) Eta Eta) ).
+ auto => /> &hr; do split;1,2:smt().
  move => i s2;do split;1:smt().
  move => *;rewrite tP => k kb.
  by rewrite initiE 1:/# /= /#.

while (0 <= i <= lvec /\ sk = _sk /\
 rho = Bytes32.of_list (take 32 (to_list _sk)) /\
  k = Bytes32.of_list (take 32 (drop 32 (to_list _sk))) /\
  tr = Bytes64.of_list (take 64 (drop 64 (to_list _sk))) /\
    forall k, 0 <= k < i =>
     s1.[k] = BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + k * (n * noise_bits) %/ 8) (to_list _sk))) Eta Eta) (kvec - i).
+ move => z;auto => /> &hr *;do split;1,2,4:smt().
  by move => k kbl kbh;rewrite get_setE /#.

auto => /> &hr; do split;1,2:smt().
move => i s1;do split;1:smt().
move => *;rewrite tP => k kb.
by rewrite initiE 1:/# /= /#.

qed.

(* Bridge: valid_sk_s2 lifts through skDecode to give infnorm_lt s2 (Eta+1).
   conseq of skDecode_corr extracts the functional form res.`5 = KArray.init (BitUnpack ...);
   then BitUnpack_infnorm applies pointwise using valid_sk_s2 on each of kvec chunks. *)
lemma skDecode_s2_bound _sk :
    valid_sk_s2 _sk =>
    phoare [ SkEncDec.skDecode : arg = _sk ==>
             PolyKVec.infnorm_lt res.`5 (Eta+1) ] = 1%r.
proof.
move => Hval.
proc *.
call (skDecode_corr _sk).
auto => /> r [#] _ _ _ _ Hs5 _.
rewrite Hs5 /PolyKVec.infnorm_lt allP /=.
move => ii /mem_iota /= Hi.
rewrite KArray.initiE 1:/# /=.
apply BitUnpack_infnorm.
- rewrite size_take; first smt(param_sets).
  rewrite size_drop; first smt(param_sets).
  rewrite BytesSK.size_to_list -noise_bits_eq.
  have /= := param_sets; case=> />; smt().
- by have := Hval ii _; smt().
qed.

(* Two-sided relational version: apply skDecode_corr on both sides; arg equality gives ={res},
   valid_sk_s2 + BitUnpack_infnorm applied to the left's functional form gives the bound. *)
equiv skDecode_equiv_bound :
    SkEncDec.skDecode ~ SkEncDec.skDecode :
    ={arg} /\ valid_sk_s2 arg{1}
    ==>
    ={res} /\ PolyKVec.infnorm_lt res{1}.`5 (Eta+1).
proof.
exists * arg{1}, arg{2}; elim* => _sk1 _sk2.
proc *.
call{2} (skDecode_corr _sk2).
call{1} (skDecode_corr _sk1).
skip => /> Hval r2 H21 H22 H23 H24 Hs5_r2 H26 r1 H11 H12 H13 H14 Hs5_r1 H16.
split. 
+ (* r1 = r2: both equal the functional form of arg{1} = arg{2} = _sk2. *)
  have : r1 = (r1.`1, r1.`2, r1.`3, r1.`4, r1.`5, r1.`6) by smt().
  have : r2 = (r2.`1, r2.`2, r2.`3, r2.`4, r2.`5, r2.`6) by smt().
  by smt().
+ (* infnorm_lt r1.`5 (Eta+1): from r1 = functional form + valid_sk_s2 + BitUnpack_infnorm. *)
  rewrite Hs5_r2 /PolyKVec.infnorm_lt allP /= => ii /mem_iota /= Hi.
  rewrite KArray.initiE 1:/# /=.
  apply BitUnpack_infnorm.
  - rewrite size_take; first smt(param_sets).
    rewrite size_drop; first smt(param_sets).
    rewrite BytesSK.size_to_list -noise_bits_eq.
    have /= := param_sets; case=> />; smt().
  - by have := Hval ii _; smt().
qed.
    
module SigEncDec = {
  proc sigEncode(ct : BytesCT.t, z : polylvec, h : polykvec) : BytesSig.t = {
    var sigma, sigbytes, zi, hb, i;
    sigbytes <- to_list ct;
    i <- 0;
    while (i < lvec) {
       zi <- BitPack z.[i] (gamma1 - 1) (gamma1);
       sigbytes <- sigbytes ++ zi;
       i <- i + 1;
    }
    hb <@ HintPackUnpack.hintBitPack(h);
    sigbytes <- sigbytes ++ hb;
    sigma <- BytesSig.of_list sigbytes;
    return sigma;
  }

  proc sigDecode(sigma : BytesSig.t) : 
    BytesCT.t * polylvec * polykvec option = {
     var ct,zi,h,i;
     var z : polylvec;
     z <- witness;
     ct <- BytesCT.init(fun ii => sigma.[ii]);
     i <- 0;
     while (i < lvec) {
       zi <- BitUnpack (mkseq (fun ii => sigma.[lambda %/ 4 + (n * gamma1_bits) %/ 8 * i + ii]) ((n * gamma1_bits) %/ 8)) (gamma1 - 1) gamma1;
       z <- z.[i <- zi];
       i <- i + 1;
    }
    h <@ HintPackUnpack.hintBitUnpack (take (kvec + w_hint) (drop (lambda %/4 + z_bytes) (to_list sigma)));

    return (ct,z,h);
  }
}.

op w1Encode(w1 : polykvec) : BytesW1.t = 
  BytesW1.of_list (flatten (map
    (fun wi => SimpleBitPack wi ((q-1)%/(2*gamma2) - 1)) 
       (mkseq (fun ii => w1.[ii]) kvec))).
