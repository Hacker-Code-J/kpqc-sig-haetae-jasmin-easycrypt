require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array256 WArray1024 BArray1024.
require import Hpoly_extract.

abbrev jzetas_inv = Hpoly_extract.jzetas_inv.
abbrev jzetas = Hpoly_extract.jzetas.

module M = {
  proc __montgomery_reduce (a:W64.t) : W32.t = {
    var r:W32.t;
    r <@ Hpoly_extract.M.__montgomery_reduce(a);
    return r;
  }

  proc __fqmul (a:W32.t, b:W32.t) : W32.t = {
    var r:W32.t;
    r <@ Hpoly_extract.M.__fqmul(a, b);
    return r;
  }

  proc _poly_ntt (rp:BArray1024.t) : BArray1024.t = {
    var zetasp:BArray1024.t;
    var zeta_0:W32.t;
    var s:W32.t;
    var coeff:W32.t;
    var t:W32.t;
    var zetasctr:int;
    var len:int;
    var start:int;
    var j:int;
    var cmp:int;
    var offset:int;
    zetasp <- witness;
    zetasp <- jzetas;
    zetasctr <- 0;
    len <- 128;
    while ((0 < len)) {
      start <- 0;
      while ((start < 256)) {
        zetasctr <- (zetasctr + 1);
        zeta_0 <- (BArray1024.get32 zetasp zetasctr);
        j <- start;
        cmp <- start;
        cmp <- (cmp + len);
        while ((j < cmp)) {
          s <- (BArray1024.get32 rp j);
          offset <- j;
          offset <- (offset + len);
          coeff <- (BArray1024.get32 rp offset);
          t <@ __fqmul (zeta_0, coeff);
          coeff <- s;
          coeff <- (coeff - t);
          rp <- (BArray1024.set32 rp offset coeff);
          s <- (s + t);
          rp <- (BArray1024.set32 rp j s);
          j <- (j + 1);
        }
        start <- j;
        start <- (start + len);
      }
      len <- (len `|>>` 1);
    }
    return rp;
  }

  proc _poly_invntt (rp:BArray1024.t) : BArray1024.t = {
    var zetasp:BArray1024.t;
    var zeta_0:W32.t;
    var t:W32.t;
    var coeff:W32.t;
    var s:W32.t;
    var zetasctr:int;
    var len:int;
    var start:int;
    var j:int;
    var cmp:int;
    var offset:int;
    zetasp <- witness;
    zetasp <- jzetas_inv;
    zetasctr <- 0;
    len <- 1;
    while ((len < 256)) {
      start <- 0;
      while ((start < 256)) {
        zeta_0 <- (BArray1024.get32 zetasp zetasctr);
        zetasctr <- (zetasctr + 1);
        j <- start;
        cmp <- start;
        cmp <- (cmp + len);
        while ((j < cmp)) {
          t <- (BArray1024.get32 rp j);
          offset <- j;
          offset <- (offset + len);
          coeff <- (BArray1024.get32 rp offset);
          s <- t;
          s <- (s + coeff);
          rp <- (BArray1024.set32 rp j s);
          t <- (t - coeff);
          t <@ __fqmul (zeta_0, t);
          rp <- (BArray1024.set32 rp offset t);
          j <- (j + 1);
        }
        start <- j;
        start <- (start + len);
      }
      len <- (len `<<` 1);
    }
    zeta_0 <- (BArray1024.get32 zetasp 255);
    j <- 0;
    while ((j < 256)) {
      coeff <- (BArray1024.get32 rp j);
      t <@ __fqmul (zeta_0, coeff);
      rp <- (BArray1024.set32 rp j t);
      j <- (j + 1);
    }
    return rp;
  }

  proc _poly_basemul (rp:BArray1024.t, ap:BArray1024.t, bp:BArray1024.t) :
  BArray1024.t = {
    var a:W32.t;
    var b:W32.t;
    var r:W32.t;
    var i:int;
    i <- 0;
    while ((i < 256)) {
      a <- (BArray1024.get32 ap i);
      b <- (BArray1024.get32 bp i);
      r <@ __fqmul (a, b);
      rp <- (BArray1024.set32 rp i r);
      i <- (i + 1);
    }
    return rp;
  }

  proc poly_ntt_jazz (rp:BArray1024.t) : BArray1024.t = {
    rp <@ _poly_ntt (rp);
    return rp;
  }

  proc poly_invntt_jazz (rp:BArray1024.t) : BArray1024.t = {
    rp <@ _poly_invntt (rp);
    return rp;
  }

  proc poly_basemul_jazz (rp:BArray1024.t, ap:BArray1024.t, bp:BArray1024.t) :
  BArray1024.t = {
    rp <@ _poly_basemul (rp, ap, bp);
    return rp;
  }
}.
