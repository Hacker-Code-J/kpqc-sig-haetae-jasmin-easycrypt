require import AllCore IntDiv List.
from Jasmin require import JByte_array JWord.
require import Array256.
require import Parameters GFq Rq VecMat Conversion Serialization Symmetric.
import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq MLDSAParams.

op "_.[_]" : 'a list -> int -> 'a = nth witness.

type sib_leakage = bool list.

module type LeakyRO(XOF : XOF_SIB) = {
   proc init() : unit
   proc get(mu : Bytes64.t, w1 : BytesW1.t) : (BytesCT.t * poly) * sib_leakage
}.

module SampleInBall(XOF : XOF_SIB) = {
   proc sample(rho : BytesCT.t) : poly * sib_leakage = {
      var leakage : bool list;
      var s : Bytes8.t;
      var h : bool list;
      var i,j;
      var c : poly;
      leakage <- [];
      c <- poly_zero;
      s <- H_sib rho;
      h <- BytesToBits (Bytes8.to_list s);
      XOF.init(rho);
      i <- 256 - tau;
      while (i < 256) {
          j <@ XOF.next();
          while(i < W8.to_uint j) { leakage <- leakage ++ [true]; j <@ XOF.next(); }
          leakage <- leakage ++ [false]; 
          c.[i] <- c.[W8.to_uint j];
          c.[W8.to_uint j] <- if h.[i+tau-256] then incoeff (-1) else incoeff (1);
          i <- i + 1;
      }
      return (c,leakage);
   }
}.

(*************** Begin SampleInBall CORRECTNESS BRIDGE ****************)


op sampleInBall : BytesCT.t ->  poly * sib_leakage. (* Write me: PY *)


phoare SampleInBall_correct _ct :
   [ SampleInBall(MLDSA_XOF_SIB).sample : arg = _ct ==> res = sampleInBall _ct] = 1%r.
admitted. (* FIXME: PY *)

(* The challenge polynomial has tau nonzero coefficients, each ±1, so infnorm < 2.
   Provable from the SampleInBall algorithm: only incoeff(±1) values are placed.
   Cf. wpoly_srng 1 1 challenge established in verify.ec:487 (impl-level, not directly citeable). *)
lemma sampleInBall_norm (ct : BytesCT.t) :
    infnorm_lt (sampleInBall ct).`1 2.
proof. admit. qed. (* FIXME: PY *)

(*************** End SampleInBall CORRECTNESS BRIDGE ****************)


module (SIB_RO : LeakyRO) (XOF : XOF_SIB) = {
   proc init() = {}
   proc get(mu : Bytes64.t, w1 : BytesW1.t): (BytesCT.t * poly) * sib_leakage = {
        var rr;
        var ct <- H_ct mu w1;
        rr <@ SampleInBall(XOF).sample(ct);
        return ((ct,rr.`1),rr.`2);
   }
}.

import Bytes3.
module RejNTTPoly(XOF : XOF_RejNTTPoly) = {
  proc sample(rho : Bytes34.t) : poly = {
    var j, b3, co;
    var c : poly;
    c <- witness;
    XOF.init(rho);
    j <- 0;
    while (j < 256) {
      b3 <@ XOF.next();
      co <- CoeffFromThreeBytes b3.[0] b3.[1] b3.[2];
      if (co <> None) {
         c.[j] <- incoeff (oget co);
         j <- j + 1;
      }
    }
    return c;
  }
}.

(*************** Begin RejNTTPoly CORRECTNESS BRIDGE ****************)

(* Concrete definition is in Symmetric.ec: MLDSA_XOFA *)


op rejNTTPoly : Bytes34.t ->  poly. (* Write me: PY *)


phoare RejNTTPoly_correct _rho :
   [ RejNTTPoly(MLDSA_XOFA).sample : arg = _rho ==> res = rejNTTPoly _rho] = 1%r.
admitted. (* FIXME : PY *)
   
(*************** End RejNTTPoly CORRECTNESS BRIDGE ****************)


module RejBoundedPoly(XOF : XOF_RejBPoly) = {
  proc sample(rho : Bytes66.t) : poly = {
    var j,z,z0,z1;
    var a : poly;
    a <- witness;
    XOF.init(rho);
    j <- 0;
    while (j < 256) {
      z <@ XOF.next();
      z0 <- CoeffFromHalfByte (to_uint z %% 16);
      z1 <- CoeffFromHalfByte (to_uint z %/ 16);
      if (z0 <> None) { a.[j] <- incoeff (oget z0); j <- j + 1; }
      if ((z1 <> None) && (j < 256)) { a.[j] <- incoeff (oget z1); j <- j + 1; }
    }
    return a;
  }
}.

(*************** Begin RejBoundedPoly CORRECTNESS BRIDGE ****************)

(* Concrete definition is in Symmetric.ec: MLDSA_XOFS *)


op rejBoundedPoly : Bytes66.t ->  poly. (* Write Me: PY *)


phoare RejBoundedPoly_correct _rho :
   [ RejBoundedPoly(MLDSA_XOFS).sample : arg = _rho ==> res = rejBoundedPoly _rho] = 1%r.
admitted. (* FIXME : PY *)
   
(*************** End RejBoundedPoly CORRECTNESS BRIDGE ****************)

module ExpandA(XOF : XOF_RejNTTPoly) = {
   proc sample(rho : Bytes32.t) : polymat = {
      var r,s,rhop,ars;
      var aa : polymat;
      aa <- witness;
      r <- 0;
      while (r < kvec) {
          s <- 0;
          while (s < lvec) {
            rhop <- Bytes34.of_list (Bytes32.to_list rho ++ [W8.of_int r; W8.of_int s]);
            ars <@ RejNTTPoly(XOF).sample(rhop);
            aa <- aa.[(r,s) <- ars];
            s <- s + 1;
          }
          r <- r + 1;
      }
      return aa;
   }
}.

(*************** Begin ExpandA CORRECTNESS BRIDGE ****************)

op expandA : Bytes32.t ->  polymat. (* Write me: PY *)


phoare ExpandA_correct _rho :
   [ ExpandA(MLDSA_XOFA).sample : arg = _rho ==> res = expandA _rho] = 1%r.
admitted. (* FIXME: PY *)
   
(*************** End ExpandA CORRECTNESS BRIDGE ****************)

module ExpandS(XOF : XOF_RejBPoly) = {
   proc sample(rho : Bytes64.t) : polylvec * polykvec = {
      var si,r,rhop;
      var s1 : polylvec;
      var s2 : polykvec;
      s1 <- witness;
      s2 <- witness;
      r <- 0;
      while (r < lvec) {
         rhop <- Bytes66.of_list (Bytes64.to_list rho ++ (IntegerToBytes r 2));        
         si <@ RejBoundedPoly(XOF).sample(rhop);
         s1 <- s1.[r <- si];
            r <- r + 1;
      }
      while (r < kvec) {
         rhop <- Bytes66.of_list (Bytes64.to_list rho ++ (IntegerToBytes (r+lvec) 2));        
         si <@ RejBoundedPoly(XOF).sample(rhop);
         s2 <- s2.[r <- si];
         r <- r + 1;
      }
      return (s1,s2);
   }
}.

(*************** Begin ExpandS CORRECTNESS BRIDGE ****************)

op expandS : Bytes64.t -> polylvec * polykvec. (* WRITE ME: PY *)


phoare ExpandS_correct _rho :
   [ ExpandS(MLDSA_XOFS).sample : arg = _rho ==> res = expandS _rho] = 1%r.
admitted. (* FIXME: PY *)
   
(*************** End ExpandS CORRECTNESS BRIDGE ****************)


module ExpandMask = {
   proc sample(rho : Bytes64.t, mu : int) : polylvec = {
     var r, rhop, v,si;
     var s : polylvec;
     s <- witness;
     r <- 0;
     while (r < lvec) {
        rhop <- Bytes66.of_list (Bytes64.to_list rho ++ (IntegerToBytes (mu+r) 2));        
        v <- H_v rhop;
        si <- BitUnpack (BytesV.to_list v) (gamma1-1) (gamma1);
        s <- s.[r <- si];
        r <- r + 1;
     }
     return s;
   }
}.

(*************** Begin ExpandMask CORRECTNESS BRIDGE ****************)

op expandMask : Bytes64.t -> int -> polylvec. (* WRITE ME : PY *)


phoare ExpandMask_correct _rho _mu :
   [ ExpandMask.sample : arg = (_rho,_mu) ==> res = expandMask _rho _mu] = 1%r.
admitted. (* FIXME: PY *)
   
(*************** End ExpandMask CORRECTNESS BRIDGE ****************)

