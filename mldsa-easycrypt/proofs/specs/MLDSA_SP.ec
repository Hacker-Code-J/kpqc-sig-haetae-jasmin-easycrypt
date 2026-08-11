require import AllCore IntDiv List.
from Jasmin require import JByte_array JWord.

require import Parameters GFq Rq VecMat Conversion Serialization Symmetric Sampling.
import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq MLDSAParams.

require import MLDSA.

module type Samplers = {
   proc init() : Bytes32.t 
   proc sampleA() : polymat
   proc sampleS() : polylvec * polykvec
   proc resetY(_ : Bytes64.t) : unit
   proc sampleY() : polylvec
}.

op dcoins : Bytes32.t distr.
op drnd : rnd_ distr.

module S(XOFA : XOF_RejNTTPoly, XOFS : XOF_RejBPoly) : Samplers = {
   var rho : Bytes32.t
   var rhop : Bytes64.t
   var _K : Bytes32.t
   var kappa : int
   var rhopp : Bytes64.t
   var coins : rnd_

   proc init() : Bytes32.t = {
     var eps,epsp;
     eps <$ dcoins;
     epsp <- Bytes34.of_list (Bytes32.to_list eps ++ [W8.of_int kvec;W8.of_int lvec]);
     (rho,rhop,_K) <- H_seed epsp;
     return rho;
   }

   proc sampleA() : polymat = {
      var _A;
      _A <@ ExpandA(XOFA).sample(rho);
      return _A;
   }

   proc sampleS() : polylvec * polykvec = {
      var s1,s2;
      (s1,s2) <@ ExpandS(XOFS).sample(rhop);
      return (s1,s2);
   }


   proc resetY(mu : Bytes64.t) : unit = {
     coins <$ drnd;
     rhopp <- H_rhopp _K coins mu;
     kappa <- 0;
   }

   proc sampleY() : polylvec = {
     var y;
     y <@ ExpandMask.sample(rhopp,kappa);
     kappa <- kappa + lvec;
     return y;
   }
}.

module MLDSA_SP(S : Samplers, XOFSIB : XOF_SIB, RO : LeakyRO) = {
   proc keygen_derand() : BytesSK.t * BytesPK.t= {
     var sk,rho,_A,s1,s2,t,t1,t0,pk,tr;
     rho <@ S.init();
     _A <@ S.sampleA();
     (s1,s2) <@ S.sampleS();
     t <- invnttv (ntt_mulmxv _A (nttv s1)) + s2;
     (t1,t0) <- Power2Round t;
     pk <@ PkEncDec.pkEncode(rho,t1);
     tr <- H_tr pk;
     sk <@ SkEncDec.skEncode(rho,witness,tr,s1,s2,t0);
     return (sk,pk);
  }

  proc sign_derand(sk : BytesSK.t, m : W8.t list, coins : rnd_) : BytesSig.t  * Leakage list= {
     var rho,_K,tr,s1,s2,t0,s1h,s2h,t0h,_A,mu,y,w,w1,ctl,ct,c,ch,cs1,
         cs2,z,r0,ct0,h,leakage,sigma,bz,bh;
     var zh : (polylvec * polykvec) option;
     ctl <- witness;
     ct <- witness;
     leakage <- [];
     (rho,_K,tr,s1,s2,t0) <@ SkEncDec.skDecode(sk);
     s1h <- nttv s1;
     s2h <- nttv s2;
     t0h <- nttv t0;
     _A <@ S.sampleA();
     mu <- H_mu tr m;
     S.resetY(mu);
     zh <- None;
     while (zh = None) {
       y <@ S.sampleY();
       w <- invnttv (ntt_mulmxv _A (nttv y));
       w1 <- polykvec_HighBits w;
       ctl <@ RO(XOFSIB).get(mu,w1Encode w1);
       (ct,c) <- ctl.`1;
       leakage <- leakage ++ [ RO ctl.`2] ;
       ch <- ntt c;
       cs1 <- invnttv (ntt_smul ch s1);
       cs2 <- invnttv (ntt_smul ch s2);
       z <- y + cs1;
       r0 <- polykvec_LowBits (w - cs2);
       bz <- infnorm_lt z (gamma1 - Beta) && 
                  infnorm_lt r0 (gamma2 - Beta);
       leakage <- leakage ++ [ CheckZ bz ];
       if (bz) {
          ct0 <- invnttv (ntt_smul ch t0);
          h <- MakeHint (PolyKVec.zerov-ct0) w - cs2 + ct0;
          bh <- infnorm_lt ct0 gamma2 && hammw h w_hint;
          leakage <- leakage ++ [ CheckH bh ];
          if (bh) { zh <- Some (z,h); }
       }
     }
     sigma <@ SigEncDec.sigEncode(ct,mods (oget zh).`1 q,(oget zh).`2);
     return (sigma, leakage);
  }

  proc verify(pk : BytesPK.t, sigma : BytesSig.t, m : W8.t list) : bool = {
    var rho,t1,c,l,ct,z,h,rb,_A,tr,mu,wapprox,w1,ctp;
    w1 <- witness;
    rb <- false;
    (rho,t1) <@ PkEncDec.pkDecode(pk);
    (ct,z,h) <@ SigEncDec.sigDecode(sigma);
    if (h <> None) {
      _A <@ S.sampleA();
      tr <- H_tr pk;
      mu <- H_mu tr m;
      (c,l) <@ SampleInBall(XOFSIB).sample(ct);
      wapprox <- invnttv (ntt_mulmxv _A (nttv z) - (ntt_smul (ntt c) (nttv (smul t1 (incoeff (2^d))))));
      w1 <- UseHint (oget h) wapprox;
      ctp <- H_ct mu (w1Encode w1);
      rb <- infnorm_lt z (gamma1 - Beta);
      rb <- rb && ct = ctp;
    }
    return rb;
  }
}.
