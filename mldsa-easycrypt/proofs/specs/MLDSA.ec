require import AllCore IntDiv List.
from Jasmin require import JByte_array JWord.

require import Parameters GFq Rq VecMat Conversion Serialization Symmetric Sampling.
import PolyLVec PolyKVec PolyMat.
import Round ZModQ Zq MLDSAParams.

type Leakage = [
   | RO of bool list
   | CheckZ of bool
   | CheckH of bool ].

module MLDSA(XOFA : XOF_RejNTTPoly, XOFS : XOF_RejBPoly, XOFSIB : XOF_SIB, RO : LeakyRO) = {
   proc keygen_derand(eps : Bytes32.t) : BytesSK.t * BytesPK.t= {
     var sk,rho,rhop,_K,_A,s1,s2,t,t1,t0,pk,tr,epsp;
     epsp <- Bytes34.of_list (Bytes32.to_list eps ++ [W8.of_int kvec;W8.of_int lvec]);
     (rho,rhop,_K) <- H_seed epsp;
     _A <@ ExpandA(XOFA).sample(rho);
     (s1,s2) <@ ExpandS(XOFS).sample(rhop);
     t <- invnttv (ntt_mulmxv _A (nttv s1)) + s2;
     (t1,t0) <- Power2Round t;
     pk <@ PkEncDec.pkEncode(rho,t1);
     tr <- H_tr pk;
     sk <@ SkEncDec.skEncode(rho,_K,tr,s1,s2,t0);
     return (sk,pk);
  }

  proc sign_derand(sk : BytesSK.t, m : W8.t list, coins : rnd_) : BytesSig.t option * Leakage list= {
     var rho,_K,tr,s1,s2,t0,s1h,s2h,t0h,_A,mu,rhopp,kappa,y,w,w1,ctl,ct,c,ch,cs1,
         cs2,z,r0,ct0,h,leakage,sigma,bz,bh;
     var zh : (polylvec * polykvec) option;
     ct <- witness;
     ctl <- witness;
     sigma <- witness;
     leakage <- [];
     (rho,_K,tr,s1,s2,t0) <@ SkEncDec.skDecode(sk);
     s1h <- nttv s1;
     s2h <- nttv s2;
     t0h <- nttv t0;
     _A <@ ExpandA(XOFA).sample(rho);
     mu <- H_mu tr m;
     rhopp <- H_rhopp _K coins mu;
     kappa <- 0;
     zh <- None;
     while (zh = None && ! (kappa_max <= kappa)) {
       y <@ ExpandMask.sample(rhopp,kappa * lvec);
       w <- invnttv (ntt_mulmxv _A (nttv y));
       w1 <- polykvec_HighBits w;
       ctl <@ RO(XOFSIB).get(mu,w1Encode w1);
       (ct,c) <- ctl.`1;
       leakage <- leakage ++ [ RO ctl.`2] ;
       ch <- ntt c;
       cs1 <- invnttv (ntt_smul ch s1h);
       cs2 <- invnttv (ntt_smul ch s2h);
       z <- y + cs1;
       r0 <- polykvec_LowBits (w - cs2);
       bz <- infnorm_lt z (gamma1 - Beta) &&
                  infnorm_lt r0 (gamma2 - Beta);
       leakage <- leakage ++ [ CheckZ bz ];
       if (bz) {
          ct0 <- invnttv (ntt_smul ch t0h);
          h <- MakeHint (PolyKVec.zerov-ct0) (w - cs2 + ct0);
          bh <- infnorm_lt ct0 gamma2 && hammw h w_hint;
          leakage <- leakage ++ [ CheckH bh ];
          if (bh) { zh <- Some (z,h); }
       }
       kappa <- kappa + 1;
     }
     if (zh <> None) {
       sigma <@ SigEncDec.sigEncode(ct,(oget zh).`1,(oget zh).`2);
     }
     return (if zh = None then None else Some sigma, leakage);
  }

  (* Eager variant: decomposes w into (w0,w1) immediately, then uses w0 - cs2.
     The Jasmin implementation follows this order. *)
  proc sign_eager(sk : BytesSK.t, m : W8.t list, coins : rnd_) : BytesSig.t option * Leakage list = {
     var rho,_K,tr,s1,s2,t0,s1h,s2h,t0h,_A,mu,rhopp,kappa,y,w,w0,w1,ctl,ct,c,ch,cs1,
         cs2,z,r0,ct0,h,leakage,sigma,bz,bh;
     var zh : (polylvec * polykvec) option;
     ct <- witness;
     ctl <- witness;
     sigma <- witness;
     leakage <- [];
     (rho,_K,tr,s1,s2,t0) <@ SkEncDec.skDecode(sk);
     s1h <- nttv s1;
     s2h <- nttv s2;
     t0h <- nttv t0;
     _A <@ ExpandA(XOFA).sample(rho);
     mu <- H_mu tr m;
     rhopp <- H_rhopp _K coins mu;
     kappa <- 0;
     zh <- None;
     while (zh = None && ! (kappa_max <= kappa)) {
       y <@ ExpandMask.sample(rhopp,kappa * lvec);
       w <- invnttv (ntt_mulmxv _A (nttv y));
       (* eager decomposition: split w now *)
       w0 <- polykvec_LowBits w;
       w1 <- polykvec_HighBits w;
       ctl <@ RO(XOFSIB).get(mu,w1Encode w1);
       (ct,c) <- ctl.`1;
       leakage <- leakage ++ [ RO ctl.`2] ;
       ch <- ntt c;
       cs1 <- invnttv (ntt_smul ch s1h);
       cs2 <- invnttv (ntt_smul ch s2h);
       z <- y + cs1;
       r0 <- w0 - cs2;
       bz <- infnorm_lt z (gamma1 - Beta) &&
                  infnorm_lt r0 (gamma2 - Beta);
       leakage <- leakage ++ [ CheckZ bz ];
       if (bz) {
          ct0 <- invnttv (ntt_smul ch t0h);
          h <- PolyKVec.MakeHintImpl w1 (r0 + ct0);
          bh <- infnorm_lt ct0 gamma2 && hammw h w_hint;
          leakage <- leakage ++ [ CheckH bh ];
          if (bh) { zh <- Some (z,h); }
       }
       kappa <- kappa + 1;
     }
     if (zh <> None) {
       sigma <@ SigEncDec.sigEncode(ct,(oget zh).`1,(oget zh).`2);
     }
     return (if zh = None then None else Some sigma, leakage);
  }

  proc verify(pk : BytesPK.t, sigma : BytesSig.t, m : W8.t list) : bool = {
    var rho,t1,c,l,ct,z,h,rb,_A,tr,mu,wapprox,w1,ctp;
    w1 <- witness;
    rb <- false;
    (rho,t1) <@ PkEncDec.pkDecode(pk);
    (ct,z,h) <@ SigEncDec.sigDecode(sigma);
    if (h <> None) {
      _A <@ ExpandA(XOFA).sample(rho);
      tr <- H_tr pk;
      mu <- H_mu tr m;
      (c,l) <@ SampleInBall(XOFSIB).sample(ct); (* we don't care about leakage in verify *)
      wapprox <- invnttv (ntt_mulmxv _A (nttv z) - (ntt_smul (ntt c) (nttv (smul t1 (incoeff (2^d))))));
      w1 <- UseHint (oget h) wapprox;
      ctp <- H_ct mu (w1Encode w1);
      rb <-  infnorm_lt z (gamma1 - Beta);
      rb <- rb && ct = ctp;
    }
    return rb;
  }
}.

(* The eager decomposition is equivalent to the standard one.
   Stated for the concrete XOFs to avoid module restriction issues.
   Two algebraic facts are needed in the loop body:
   (1) LowBits commutativity: LowBits(w-cs2) = LowBits(w)-cs2 (same bz infnorm check).
   (2) MakeHintImpl_MakeHint_equiv: MakeHintImpl(w1, r0+ct0) = MakeHint(-ct0, w-cs2+ct0)
       where w1 = HighBits(w) and r0 = LowBits(w)-cs2. *)
lemma sign_eager_equiv :
    equiv [ MLDSA(MLDSA_XOFA, MLDSA_XOFS, MLDSA_XOF_SIB, SIB_RO).sign_derand ~
            MLDSA(MLDSA_XOFA, MLDSA_XOFS, MLDSA_XOF_SIB, SIB_RO).sign_eager :
      ={sk, m, coins,
        glob MLDSA_XOFA, glob MLDSA_XOFS, glob MLDSA_XOF_SIB, glob SIB_RO}
      /\ valid_sk_s2 sk{1}
      ==>
      ={res} ].
proof.
proc.
(* Break seq 13 13 into: 4 witness/leakage assignments (sim), skDecode (equiv bridge
   skDecode_equiv_bound which yields infnorm_lt s2), 3 nttv assignments (auto yields
   s2h = nttv s2), 5 remaining assignments (sim). *)
seq 13 13 : (={rho, _K, tr, s1, s2, t0, s1h, s2h, t0h, _A, mu, rhopp,
               kappa, zh, leakage, sigma, ct, ctl,
               glob MLDSA_XOFA, glob MLDSA_XOFS, glob MLDSA_XOF_SIB, glob SIB_RO}
            /\ PolyKVec.infnorm_lt s2{1} (Eta + 1)
            /\ s2h{1} = nttv s2{1}).
+ seq 4 4 : (={sk, m, coins, ct, ctl, sigma, leakage,
               glob MLDSA_XOFA, glob MLDSA_XOFS, glob MLDSA_XOF_SIB, glob SIB_RO}
             /\ valid_sk_s2 sk{1}); 1: by auto.
  seq 1 1 : (={sk, m, coins, ct, ctl, sigma, leakage, rho, _K, tr, s1, s2, t0,
               glob MLDSA_XOFA, glob MLDSA_XOFS, glob MLDSA_XOF_SIB, glob SIB_RO}
             /\ PolyKVec.infnorm_lt s2{1} (Eta + 1)); 1: by call skDecode_equiv_bound.
  seq 3 3 : (={sk, m, coins, ct, ctl, sigma, leakage, rho, _K, tr, s1, s2, t0,
               s1h, s2h, t0h,
               glob MLDSA_XOFA, glob MLDSA_XOFS, glob MLDSA_XOF_SIB, glob SIB_RO}
             /\ PolyKVec.infnorm_lt s2{1} (Eta + 1)
             /\ s2h{1} = nttv s2{1}); 1: by auto.
  wp; call(: ={glob MLDSA_XOFA, glob MLDSA_XOFS, glob MLDSA_XOF_SIB, glob SIB_RO});
    first by sim.
  by auto.
seq 1 1 : (={rho, _K, tr, s1, s2, t0, s1h, s2h, t0h, _A, mu, rhopp,
              kappa, zh, leakage, sigma, ct, ctl,
              glob MLDSA_XOFA, glob MLDSA_XOFS,  glob SIB_RO}
            /\ PolyKVec.infnorm_lt s2{1} (Eta + 1)
            /\ s2h{1} = nttv s2{1}); last by sim.
while (={rho, _K, tr, s1, s2, t0, s1h, s2h, t0h, _A, mu, rhopp,
           kappa, zh, leakage, sigma, ct, ctl,
           glob MLDSA_XOFA, glob MLDSA_XOFS,  glob SIB_RO}
        /\ PolyKVec.infnorm_lt s2{1} (Eta + 1)
        /\ s2h{1} = nttv s2{1}); last by auto => />.
seq 10 11 : (={_K, tr, s1, s2, t0,
                   w, w1, c, ch, cs1, cs2, z, ct, ctl, leakage,
                   rho, s1h, s2h, t0h, _A, mu, rhopp, kappa, zh, sigma,
                   glob MLDSA_XOFA, glob MLDSA_XOFS,  glob SIB_RO}
             /\ PolyKVec.infnorm_lt s2{1} (Eta + 1)
             /\ s2h{1} = nttv s2{1}
             /\ PolyKVec.infnorm_lt cs2{1} (Beta + 1)
             /\ w1{1} = polykvec_HighBits w{1}
             /\ w0{2} = polykvec_LowBits w{2}).
+ seq 1 1 : (#pre /\ ={y}); 1: by conseq />;sim.
  sp; inline {1} 1; inline {2} 1.
  wp. 
  ecall{2} (SampleInBall_correct ct1{2}).
  ecall{1} (SampleInBall_correct ct1{1}).
  auto => /> &2 Hs2 Hkappa.
  by apply cs2_norm_bound; [apply sampleInBall_norm | exact Hs2].
sp 1 1; seq 1 1 : (#pre /\ ={bz} /\
             bz{1} = (infnorm_lt z{1} (gamma1 - Beta) &&
                     infnorm_lt r0{1} (gamma2 - Beta))).
+ auto => /> &1 &2 *.
  by rewrite (bz_sync w{1} cs2{1} _) 1:/#.

seq 1 1 : #pre; 1: by auto.
if;1,3: by auto => />.
sp 2 2; seq 1 1 : (#pre /\ ={bh} /\ ={h} /\
          bh{1} = (infnorm_lt ct0{1} gamma2 && hammw h{1} w_hint)).
+ auto => /> &1 &2 *.
  by rewrite (polykvec_MakeHintImpl_MakeHint_equiv w{1} cs2{1}
                (invnttv (ntt_smul ch{1} t0h{1})) _) 1:/#.

seq 1 1 : (#pre); 1: by auto.

if; 1,3: by auto => />.
by auto => />.
qed.
