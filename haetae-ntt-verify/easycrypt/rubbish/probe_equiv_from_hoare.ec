require import RefJasminNTT.
require import AllCore IntDiv Ring StdOrder BitEncoding.
from Jasmin require import JWord JModel_x86.
import SLH64.
require import Fq GFq NTT_Fq Hpoly_extract.
import Zq.

module FqSpec = {
  proc mul(a0 b0 : W32.t) : W32.t = {
    var r;
    r <@ Hpoly_extract.M.__fqmul(a0, b0);
    return r;
  }
}.

module FqPure = {
  proc mul(a0 b0 : W32.t) : coeff = {
    return NTT_Fq.word_to_coeff a0 * NTT_Fq.word_to_coeff b0 * inv NTT_Fq.R;
  }
}.

theory ProbeEquivFromHoare.

equiv fqmul_same :
  Hpoly_extract.M.__fqmul ~ FqSpec.mul :
  arg{1} = (a0{2}, b0{2}) ==> ={res}.
proof.
proc.
inline {2} FqSpec.mul.
wp.
call (_: ={a} /\ ={b}).
+ by proc; sim.
by skip.
qed.

equiv fqmul_pure :
  Hpoly_extract.M.__fqmul ~ FqPure.mul :
  arg{1} = (a0{2}, b0{2}) /\
  - Fq.SignedReductions.R %/ 2 * Fq.q <= W32.to_sint a0{2} * W32.to_sint b0{2} <
    Fq.SignedReductions.R %/ 2 * Fq.q
  ==>
  NTT_Fq.word_to_coeff res{1} = res{2} /\ Fq.bw32 res{1} 16.
proof.
proc.
inline {2} FqPure.mul.
wp.
exists* (W32.to_sint a{1}), (W32.to_sint b{1}); elim* => aa bb.
ecall (RefJasminNTT.fqmul_word_to_coeff_mul_bound_h aa bb).
skip => />.
qed.

end ProbeEquivFromHoare.
