require import RefJasminNTT.
require import AllCore IntDiv CoreMap List Distr Ring StdOrder BitEncoding.
from Jasmin require import JWord JModel_x86.
import SLH64.
require import Array256 BArray1024.
require import GFq NTT_Fq Hpoly_extract.
import Zq.

module JFwdInner = {
  proc step(rp : BArray1024.t, zc j len cmp : int, asz bsz tsz : int) : BArray1024.t = {
    var zeta_0, s, coeff, t;
    var offset;

    while (j < cmp) {
      zeta_0 <- BArray1024.get32 Hpoly_extract.jzetas zc;
      s <- BArray1024.get32 rp j;
      offset <- j + len;
      coeff <- BArray1024.get32 rp offset;
      t <@ Hpoly_extract.M.__fqmul (zeta_0, coeff);
      coeff <- s - t;
      rp <- BArray1024.set32 rp offset coeff;
      s <- s + t;
      rp <- BArray1024.set32 rp j s;
      j <- j + 1;
    }
    return rp;
  }
}.

module SFwdInner = {
  proc step(r : coeff Array256.t, zetas : coeff Array256.t, zc j len cmp : int, asz bsz tsz : int) : coeff Array256.t = {
    var t, zeta_;

    while (j < cmp) {
      zeta_ <- zetas.[zc];
      t <- zeta_ * r.[j + len];
      r.[j + len] <- r.[j] + (-t);
      r.[j] <- r.[j] + t;
      j <- j + 1;
    }
    return r;
  }
}.

theory ProofForwardLoopBody.

equiv forward_inner_loop_equiv_debug :
  JFwdInner.step ~ SFwdInner.step :
  NTT_Fq.poly_repr rp{1} r{2} /\
  zetas{2} = NTT_Fq.zetas /\
  1 <= zc{1} < 256 /\ zc{1} = zc{2} /\
  0 <= j{1} <= cmp{1} /\ j{1} = j{2} /\
  0 < len{1} /\ len{1} = len{2} /\
  cmp{1} = cmp{2} /\
  0 <= cmp{1} <= 256 /\
  0 <= j{1} + len{1} <= 256 /\
  cmp{1} <= j{1} + len{1} /\
  0 <= asz{1} < 31 /\ 0 <= bsz{1} < 31 /\ 0 <= tsz{1} < 31
  ==>
  NTT_Fq.poly_repr res{1} res{2}.
proof.
proc.
while (
  NTT_Fq.poly_repr rp{1} r{2} /\
  zetas{2} = NTT_Fq.zetas /\
  1 <= zc{1} < 256 /\ zc{1} = zc{2} /\
  0 <= j{1} <= cmp{1} /\ j{1} = j{2} /\
  0 < len{1} /\ len{1} = len{2} /\
  cmp{1} = cmp{2} /\
  0 <= cmp{1} <= 256 /\
  0 <= j{1} + len{1} <= 256 /\
  cmp{1} <= j{1} + len{1} /\
  0 <= asz{1} < 31 /\ 0 <= bsz{1} < 31 /\ 0 <= tsz{1} < 31
); [wp|skip => />].
abort.

end ProofForwardLoopBody.
