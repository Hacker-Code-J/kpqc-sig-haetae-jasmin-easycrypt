require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array5 Array24 Array25 WArray192 BArray40 BArray192 BArray200.

abbrev haetae_keccak1600_rc =
(BArray192.of_list64
[(W64.of_int 1); (W64.of_int 32898); (W64.of_int (-9223372036854742902));
(W64.of_int (-9223372034707259392)); (W64.of_int 32907);
(W64.of_int 2147483649); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854743031)); (W64.of_int 138); (W64.of_int 136);
(W64.of_int 2147516425); (W64.of_int 2147483658); (W64.of_int 2147516555);
(W64.of_int (-9223372036854775669)); (W64.of_int (-9223372036854742903));
(W64.of_int (-9223372036854743037)); (W64.of_int (-9223372036854743038));
(W64.of_int (-9223372036854775680)); (W64.of_int 32778);
(W64.of_int (-9223372034707292150)); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854742912)); (W64.of_int 2147483649);
(W64.of_int (-9223372034707259384))]).

module M = {
  proc _keccak_init_state (sp_0:BArray200.t) : BArray200.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 25))) {
      sp_0 <- (BArray200.set64 sp_0 (W64.to_uint i) (W64.of_int 0));
      i <- (i + (W64.of_int 1));
    }
    return sp_0;
  }
  proc __keccakf1600_index (x:int, y:int) : int = {
    var r:int;
    r <- ((x %% 5) + (5 * (y %% 5)));
    return r;
  }
  proc __keccakf1600_rho_offset (i:int) : int = {
    var r:int;
    var x:int;
    var y:int;
    var t:int;
    var z:int;
    r <- 0;
    x <- 1;
    y <- 0;
    t <- 0;
    while ((t < 24)) {
      if ((i = (x + (5 * y)))) {
        r <- ((((t + 1) * (t + 2)) %/ 2) %% 64);
      } else {
        
      }
      z <- (((2 * x) + (3 * y)) %% 5);
      x <- y;
      y <- z;
      t <- (t + 1);
    }
    return r;
  }
  proc __keccakf1600_rho (x:int, y:int) : int = {
    var r:int;
    var i:int;
    i <@ __keccakf1600_index (x, y);
    r <@ __keccakf1600_rho_offset (i);
    return r;
  }
  proc __rol_u64 (x:W64.t, i:int) : W64.t = {
    var  _0:bool;
    var  _1:bool;
    if ((i <> 0)) {
      ( _0,  _1, x) <- (ROL_64 x (W8.of_int i));
    } else {
      
    }
    return x;
  }
  proc __andn_u64 (a:W64.t, b:W64.t) : W64.t = {
    var t:W64.t;
    t <- ((invw a) `&` b);
    return t;
  }
  proc __keccak_theta_sum (a:BArray200.t) : BArray40.t = {
    var c:BArray40.t;
    var x:int;
    var y:int;
    c <- witness;
    x <- 0;
    while ((x < 5)) {
      c <- (BArray40.set64 c x (BArray200.get64 a x));
      x <- (x + 1);
    }
    y <- 1;
    while ((y < 5)) {
      x <- 0;
      while ((x < 5)) {
        c <-
        (BArray40.set64 c x
        ((BArray40.get64 c x) `^` (BArray200.get64 a (x + (y * 5)))));
        x <- (x + 1);
      }
      y <- (y + 1);
    }
    return c;
  }
  proc __keccak_theta_rol (c:BArray40.t) : BArray40.t = {
    var aux:W64.t;
    var d:BArray40.t;
    var x:int;
    d <- witness;
    x <- 0;
    while ((x < 5)) {
      d <- (BArray40.set64 d x (BArray40.get64 c ((x + 1) %% 5)));
      aux <@ __rol_u64 ((BArray40.get64 d x), 1);
      d <- (BArray40.set64 d x aux);
      d <-
      (BArray40.set64 d x
      ((BArray40.get64 d x) `^` (BArray40.get64 c (((x - 1) + 5) %% 5))));
      x <- (x + 1);
    }
    return d;
  }
  proc __keccak_rol_sum (a:BArray200.t, d:BArray40.t, y:int) : BArray40.t = {
    var aux:W64.t;
    var b:BArray40.t;
    var x:int;
    var xp:int;
    var yp:int;
    var r:int;
    b <- witness;
    x <- 0;
    while ((x < 5)) {
      xp <- ((x + (3 * y)) %% 5);
      yp <- x;
      r <@ __keccakf1600_rho (xp, yp);
      b <- (BArray40.set64 b x (BArray200.get64 a (xp + (yp * 5))));
      b <-
      (BArray40.set64 b x ((BArray40.get64 b x) `^` (BArray40.get64 d xp)));
      aux <@ __rol_u64 ((BArray40.get64 b x), r);
      b <- (BArray40.set64 b x aux);
      x <- (x + 1);
    }
    return b;
  }
  proc __keccak_set_row (e:BArray200.t, b:BArray40.t, y:int) : BArray200.t = {
    var x:int;
    var x1:int;
    var x2:int;
    var t:W64.t;
    x <- 0;
    while ((x < 5)) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      t <@ __andn_u64 ((BArray40.get64 b x1), (BArray40.get64 b x2));
      t <- (t `^` (BArray40.get64 b x));
      e <- (BArray200.set64 e (x + (y * 5)) t);
      x <- (x + 1);
    }
    return e;
  }
  proc _keccak_pround (e:BArray200.t, a:BArray200.t) : BArray200.t = {
    var c:BArray40.t;
    var d:BArray40.t;
    var y:int;
    var b:BArray40.t;
    b <- witness;
    c <- witness;
    d <- witness;
    c <@ __keccak_theta_sum (a);
    d <@ __keccak_theta_rol (c);
    y <- 0;
    while ((y < 5)) {
      b <@ __keccak_rol_sum (a, d, y);
      e <@ __keccak_set_row (e, b, y);
      y <- (y + 1);
    }
    return e;
  }
  proc __keccakf1600_statepermute (a:BArray200.t) : BArray200.t = {
    var se:BArray200.t;
    var e:BArray200.t;
    var rcp:BArray192.t;
    var c:int;
    var rc:W64.t;
    e <- witness;
    rcp <- witness;
    se <- witness;
    e <- se;
    c <- 0;
    while ((c < 12)) {
      e <@ _keccak_pround (e, a);
      (a, e) <- (swap_ e a);
      rcp <- haetae_keccak1600_rc;
      rc <- (BArray192.get64 rcp (2 * c));
      e <- (BArray200.set64 e 0 ((BArray200.get64 e 0) `^` rc));
      a <@ _keccak_pround (a, e);
      (a, e) <- (swap_ e a);
      rcp <- haetae_keccak1600_rc;
      rc <- (BArray192.get64 rcp ((2 * c) + 1));
      a <- (BArray200.set64 a 0 ((BArray200.get64 a 0) `^` rc));
      c <- (c + 1);
    }
    return a;
  }
  proc _keccakf1600 (sp_0:BArray200.t) : BArray200.t = {
    
    sp_0 <@ __keccakf1600_statepermute (sp_0);
    return sp_0;
  }
  proc __fips202_absorb_once_fixed (sp_0:BArray200.t, inp:int, inlen:W64.t,
                                    domain:W8.t, rate:int) : BArray200.t = {
    var ms:W64.t;
    var inpa:W64.t;
    var ratev:W64.t;
    var i:W64.t;
    var cond:bool;
    var lane:W64.t;
    var t:W64.t;
    var b:W8.t;
    var shift:W8.t;
    sp_0 <@ _keccak_init_state (sp_0);
    ms <- (init_msf);
    sp_0 <- (protect_ptr sp_0 ms);
    inpa <- (W64.of_int inp);
    (* Erased call to declassify *)
    inpa <- (protect_64 inpa ms);
    ratev <- (W64.of_int rate);
    (* Erased call to declassify *)
    ratev <- (protect_64 ratev ms);
    (* Erased call to declassify *)
    inlen <- (protect_64 inlen ms);
    (* Erased call to declassify *)
    domain <- (protect_8 domain ms);
    while ((ratev \ule inlen)) {
      i <- (W64.of_int 0);
      ms <- (init_msf);
      cond <- (i \ult ratev);
      while (cond) {
        ms <- (update_msf cond ms);
        lane <- i;
        lane <- (lane `>>` (W8.of_int 3));
        t <- (loadW64 Glob.mem (W64.to_uint inpa));
        t <- (protect_64 t ms);
        sp_0 <-
        (BArray200.set64 sp_0 (W64.to_uint lane)
        ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
        inpa <- (inpa + (W64.of_int 8));
        i <- (i + (W64.of_int 8));
        cond <- (i \ult ratev);
      }
      ms <- (update_msf (! cond) ms);
      inlen <- (inlen - ratev);
      (* Erased call to spill *)
      sp_0 <@ _keccakf1600 (sp_0);
      (* Erased call to unspill *)
      ms <- (init_msf);
      sp_0 <- (protect_ptr sp_0 ms);
      ratev <- (protect_64 ratev ms);
      inpa <- (protect_64 inpa ms);
      inlen <- (protect_64 inlen ms);
      domain <- (protect_8 domain ms);
    }
    i <- (W64.of_int 0);
    ms <- (init_msf);
    cond <- (i \ult inlen);
    while (cond) {
      ms <- (update_msf cond ms);
      lane <- i;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (loadW8 Glob.mem (W64.to_uint inpa));
      b <- (protect_8 b ms);
      t <- (zeroextu64 b);
      shift <- (truncateu8 i);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      inpa <- (inpa + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
      cond <- (i \ult inlen);
    }
    ms <- (update_msf (! cond) ms);
    lane <- i;
    lane <- (lane `>>` (W8.of_int 3));
    shift <- (truncateu8 i);
    shift <- (shift `&` (W8.of_int 7));
    shift <- (shift `<<` (W8.of_int 3));
    t <- (zeroextu64 domain);
    t <- (t `<<` (shift `&` (W8.of_int 63)));
    sp_0 <-
    (BArray200.set64 sp_0 (W64.to_uint lane)
    ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
    lane <- ratev;
    lane <- (lane `>>` (W8.of_int 3));
    lane <- (lane - (W64.of_int 1));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <-
    (BArray200.set64 sp_0 (W64.to_uint lane)
    ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
    return sp_0;
  }
  proc __fips202_shake_once (outp:int, outlen:W64.t, inp:int, inlen:W64.t,
                             rate:int) : int = {
    var st:BArray200.t;
    var sp_0:BArray200.t;
    var domain:W8.t;
    var ratev:W64.t;
    var ms:W64.t;
    var outa:W64.t;
    var i:W64.t;
    var cond:bool;
    var lane:W64.t;
    var t:W64.t;
    var shift:W8.t;
    var b:W8.t;
    sp_0 <- witness;
    st <- witness;
    sp_0 <- st;
    domain <- (W8.of_int 31);
    (* Erased call to spill *)
    sp_0 <@ __fips202_absorb_once_fixed (sp_0, inp, inlen, domain, rate);
    (* Erased call to unspill *)
    ratev <- (W64.of_int rate);
    ms <- (init_msf);
    sp_0 <- (protect_ptr sp_0 ms);
    outa <- (W64.of_int outp);
    (* Erased call to declassify *)
    outa <- (protect_64 outa ms);
    (* Erased call to declassify *)
    outlen <- (protect_64 outlen ms);
    (* Erased call to declassify *)
    ratev <- (protect_64 ratev ms);
    while ((ratev \ule outlen)) {
      (* Erased call to spill *)
      sp_0 <@ _keccakf1600 (sp_0);
      (* Erased call to unspill *)
      ms <- (init_msf);
      sp_0 <- (protect_ptr sp_0 ms);
      outa <- (protect_64 outa ms);
      outlen <- (protect_64 outlen ms);
      ratev <- (protect_64 ratev ms);
      i <- (W64.of_int 0);
      ms <- (init_msf);
      cond <- (i \ult ratev);
      while (cond) {
        ms <- (update_msf cond ms);
        lane <- i;
        lane <- (lane `>>` (W8.of_int 3));
        t <- (BArray200.get64 sp_0 (W64.to_uint lane));
        Glob.mem <- (storeW64 Glob.mem (W64.to_uint outa) t);
        outa <- (outa + (W64.of_int 8));
        outp <- (outp + 8);
        i <- (i + (W64.of_int 8));
        cond <- (i \ult ratev);
      }
      ms <- (update_msf (! cond) ms);
      outlen <- (outlen - ratev);
    }
    if ((outlen <> (W64.of_int 0))) {
      (* Erased call to spill *)
      sp_0 <@ _keccakf1600 (sp_0);
      (* Erased call to unspill *)
      ms <- (init_msf);
      sp_0 <- (protect_ptr sp_0 ms);
      outa <- (protect_64 outa ms);
      outlen <- (protect_64 outlen ms);
      i <- (W64.of_int 0);
      ms <- (init_msf);
      cond <- (i \ult outlen);
      while (cond) {
        ms <- (update_msf cond ms);
        lane <- i;
        lane <- (lane `>>` (W8.of_int 3));
        t <- (BArray200.get64 sp_0 (W64.to_uint lane));
        shift <- (truncateu8 i);
        shift <- (shift `&` (W8.of_int 7));
        shift <- (shift `<<` (W8.of_int 3));
        t <- (t `>>` (shift `&` (W8.of_int 63)));
        b <- (truncateu8 t);
        Glob.mem <- (storeW8 Glob.mem (W64.to_uint outa) b);
        outa <- (outa + (W64.of_int 1));
        outp <- (outp + 1);
        i <- (i + (W64.of_int 1));
        cond <- (i \ult outlen);
      }
      ms <- (update_msf (! cond) ms);
    } else {
      
    }
    return outp;
  }
  proc fips202_shake128_jazz (outp:int, outlen:W64.t, inp:int, inlen:W64.t) : 
  int = {
    
    outp <@ __fips202_shake_once (outp, outlen, inp, inlen, 168);
    return outp;
  }
  proc fips202_shake256_jazz (outp:int, outlen:W64.t, inp:int, inlen:W64.t) : 
  int = {
    
    outp <@ __fips202_shake_once (outp, outlen, inp, inlen, 136);
    return outp;
  }
}.
