require import RefJasminNTT.
require import AllCore IntDiv CoreMap List Distr Ring StdOrder BitEncoding.
from Jasmin require import JWord JModel_x86.
import SLH64.
require import Array256 BArray1024.
require import Fq GFq NTT_Fq Hpoly_extract.
import Zq.

module JMul = {
  proc step(rp : BArray1024.t, zc j len : int) : W32.t = {
    var zeta_0, coeff, t;
    var offset;
    zeta_0 <- BArray1024.get32 Hpoly_extract.jzetas zc;
    offset <- j + len;
    coeff <- BArray1024.get32 rp offset;
    t <@ Hpoly_extract.M.__fqmul (zeta_0, coeff);
    return t;
  }
}.

module SMul = {
  proc step(r : coeff Array256.t, zetas : coeff Array256.t, zc j len : int) : coeff = {
    return zetas.[zc] * r.[j + len];
  }
}.

theory ProbeOneSidedCall.

equiv one_sided_call :
  JMul.step ~ SMul.step :
  NTT_Fq.poly_repr rp{1} r{2} /\
  zetas{2} = NTT_Fq.zetas /\
  1 <= zc{1} < 256 /\ zc{1} = zc{2} /\
  0 <= j{1} + len{1} < 256 /\ j{1} = j{2} /\ len{1} = len{2} /\
  - Fq.SignedReductions.R %/ 2 * Fq.q <=
    W32.to_sint (BArray1024.get32 Hpoly_extract.jzetas zc{1}) *
    W32.to_sint (BArray1024.get32 rp{1} (j{1} + len{1})) <
    Fq.SignedReductions.R %/ 2 * Fq.q
  ==>
  NTT_Fq.word_to_coeff res{1} = res{2}.
proof.
proc.
wp.
ecall{1} (RefJasminNTT.fqmul_word_to_coeff_mul_bound_ph
  (W32.to_sint zeta_0{1}) (W32.to_sint coeff{1})).
+ wp; skip => /> &1 &2 hrepr hzc_ge hzc_lt hj_ge hj_lt hbd_ge hbd_lt.
  move=> result hres _ _.
  rewrite hres.
  have hp :
    r{2}.[j{2} + len{2}] =
    NTT_Fq.word_to_coeff (BArray1024.get32 rp{1} (j{2} + len{2})).
  + apply NTT_Fq.poly_repr_get; first exact hrepr.
    by rewrite mem_range; smt().
  rewrite hp.
  have hz := RefJasminNTT.jzetas_get_cancel zc{2} _.
  + by smt().
  rewrite -hz /NTT_Fq.word_to_coeff /Hpoly_extract.jzetas.
  ring.
print goal 1.
qed.

end ProbeOneSidedCall.
