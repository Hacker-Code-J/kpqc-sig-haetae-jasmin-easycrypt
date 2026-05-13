(* HAETAE NTT proof scaffold, following the structure of
   formosa-mlkem/proof/eclib/NTTAlgebra.ec. *)

require import AllCore IntDiv List Ring StdOrder BitEncoding.

require import Array256.
require import Fq Fastexp.
require import GFq Rq.
require import NTT_Fq.

import Zq IntOrder BitReverse.

theory NTTAlgebra.

module NTT_vars = {
  var r                       : coeff Array256.t
  var zetas, zetas_inv        : coeff Array256.t
  var len, start, j, zetasctr : int
  var t, zeta_                : coeff
}.

module NTT_opt = {
  proc ntt_inner() = {
    NTT_vars.zetasctr <- NTT_vars.zetasctr + 1;
    NTT_vars.zeta_    <- NTT_vars.zetas.[NTT_vars.zetasctr];
    NTT_vars.j        <- NTT_vars.start;
    while (NTT_vars.j < NTT_vars.start + NTT_vars.len) {
      NTT_vars.t                              <- NTT_vars.zeta_ * NTT_vars.r.[NTT_vars.j + NTT_vars.len];
      NTT_vars.r.[NTT_vars.j + NTT_vars.len] <- NTT_vars.r.[NTT_vars.j] + (-NTT_vars.t);
      NTT_vars.r.[NTT_vars.j]                <- NTT_vars.r.[NTT_vars.j] + NTT_vars.t;
      NTT_vars.j                             <- NTT_vars.j + 1;
    }
    NTT_vars.start <- NTT_vars.j + NTT_vars.len;
  }

  proc ntt_outer() = {
    NTT_vars.start <- 0;
    while (NTT_vars.start < 256) {
      ntt_inner();
    }
    NTT_vars.len <- NTT_vars.len %/ 2;
  }

  proc ntt() = {
    NTT_vars.zetasctr <- 0;
    NTT_vars.len      <- 128;
    while (1 <= NTT_vars.len) {
      ntt_outer();
    }
    return NTT_vars.r;
  }

  proc invntt_inner() = {
    NTT_vars.zeta_    <- NTT_vars.zetas_inv.[NTT_vars.zetasctr];
    NTT_vars.zetasctr <- NTT_vars.zetasctr + 1;
    NTT_vars.j        <- NTT_vars.start;
    while (NTT_vars.j < NTT_vars.start + NTT_vars.len) {
      NTT_vars.t                              <- NTT_vars.r.[NTT_vars.j];
      NTT_vars.r.[NTT_vars.j]                <- NTT_vars.t + NTT_vars.r.[NTT_vars.j + NTT_vars.len];
      NTT_vars.r.[NTT_vars.j + NTT_vars.len] <- NTT_vars.t + (-NTT_vars.r.[NTT_vars.j + NTT_vars.len]);
      NTT_vars.r.[NTT_vars.j + NTT_vars.len] <- NTT_vars.zeta_ * NTT_vars.r.[NTT_vars.j + NTT_vars.len];
      NTT_vars.j                             <- NTT_vars.j + 1;
    }
    NTT_vars.start <- NTT_vars.j + NTT_vars.len;
  }

  proc invntt_outer() = {
    NTT_vars.start <- 0;
    while (NTT_vars.start < 256) {
      invntt_inner();
    }
    NTT_vars.len <- NTT_vars.len * 2;
  }

  proc invntt_post() = {
    NTT_vars.j <- 0;
    while (NTT_vars.j < 256) {
      NTT_vars.r.[NTT_vars.j] <- NTT_vars.r.[NTT_vars.j] * NTT_vars.zetas_inv.[255];
      NTT_vars.j              <- NTT_vars.j + 1;
    }
  }

  proc invntt() = {
    NTT_vars.zetasctr <- 0;
    NTT_vars.len      <- 1;
    while (NTT_vars.len < 256) {
      invntt_outer();
    }
    invntt_post();
    return NTT_vars.r;
  }
}.

equiv inline_ntt :
  NTT_Fq.NTT.ntt ~ NTT_opt.ntt :
  arg{1} = (NTT_vars.r{2}, NTT_vars.zetas{2}) ==>
  ={res}.
proof.
proc.
inline {2} NTT_opt.ntt_outer.
inline {2} NTT_opt.ntt_inner.
wp.
while (r{1}        = NTT_vars.r{2} /\
       zetas{1}    = NTT_vars.zetas{2} /\
       zetasctr{1} = NTT_vars.zetasctr{2} /\
       len{1}      = NTT_vars.len{2}).
+ wp.
  while (r{1}        = NTT_vars.r{2} /\
         zetas{1}    = NTT_vars.zetas{2} /\
         zetasctr{1} = NTT_vars.zetasctr{2} /\
         len{1}      = NTT_vars.len{2} /\
         start{1}    = NTT_vars.start{2}).
  + wp.
    while (r{1}        = NTT_vars.r{2} /\
           zetas{1}    = NTT_vars.zetas{2} /\
           zetasctr{1} = NTT_vars.zetasctr{2} /\
           len{1}      = NTT_vars.len{2} /\
           zeta_{1}    = NTT_vars.zeta_{2} /\
           start{1}    = NTT_vars.start{2} /\
           j{1}        = NTT_vars.j{2}).
    + by wp; skip.
    by wp; skip.
  by wp; skip.
by wp; skip.
qed.

equiv inline_invntt :
  NTT_Fq.NTT.invntt ~ NTT_opt.invntt :
  arg{1} = (NTT_vars.r{2}, NTT_vars.zetas_inv{2}) ==>
  ={res}.
proof.
proc.
inline {2} NTT_opt.invntt_outer.
inline {2} NTT_opt.invntt_inner.
inline {2} NTT_opt.invntt_post.
wp.
while (r{1}         = NTT_vars.r{2} /\
       zetas_inv{1} = NTT_vars.zetas_inv{2} /\
       j{1}         = NTT_vars.j{2}).
+ by wp; skip.
wp.
while (r{1}         = NTT_vars.r{2} /\
       zetas_inv{1} = NTT_vars.zetas_inv{2} /\
       zetasctr{1}  = NTT_vars.zetasctr{2} /\
       len{1}       = NTT_vars.len{2}).
+ wp.
  while (r{1}         = NTT_vars.r{2} /\
         zetas_inv{1} = NTT_vars.zetas_inv{2} /\
         zetasctr{1}  = NTT_vars.zetasctr{2} /\
         len{1}       = NTT_vars.len{2} /\
         start{1}     = NTT_vars.start{2}).
  + wp.
    while (r{1}         = NTT_vars.r{2} /\
           zetas_inv{1} = NTT_vars.zetas_inv{2} /\
           zetasctr{1}  = NTT_vars.zetasctr{2} /\
           len{1}       = NTT_vars.len{2} /\
           zeta_{1}     = NTT_vars.zeta_{2} /\
           start{1}     = NTT_vars.start{2} /\
           j{1}         = NTT_vars.j{2}).
    + by wp; skip.
    by wp; skip.
  by wp; skip.
by wp; skip.
qed.

end NTTAlgebra.
