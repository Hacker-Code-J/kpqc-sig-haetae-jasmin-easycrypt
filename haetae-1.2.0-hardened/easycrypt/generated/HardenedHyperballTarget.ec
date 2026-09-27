require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array1 Array2 Array5 Array24 Array25 Array26 Array76 Array166 Array512
Array2048 Array4096 Array8192 WArray192 WArray304 WArray1328 BArray1 BArray8
BArray16 BArray26 BArray40 BArray192 BArray200 BArray304 BArray512 BArray1328
BArray8192 BArray32768.

abbrev jcdt83_lo =
(BArray1328.of_list64
[(W64.of_int 767145465612017192); (W64.of_int 5708348702329189102);
(W64.of_int (-2986515139374512380)); (W64.of_int 7315992374869995997);
(W64.of_int (-7240595365343461296)); (W64.of_int 195392804384423549);
(W64.of_int 956154643040125894); (W64.of_int (-387090023418055461));
(W64.of_int (-6839973910006153600)); (W64.of_int 1752582669294548863);
(W64.of_int 4800866410357959959); (W64.of_int 3667394071068326311);
(W64.of_int 7998665258853332362); (W64.of_int 1039285826929998432);
(W64.of_int (-5325172712904727316)); (W64.of_int 8302908906926177525);
(W64.of_int 8594781109006420459); (W64.of_int (-5174631349969467793));
(W64.of_int 8655299069842505098); (W64.of_int (-5152057033357634684));
(W64.of_int (-7176303742971548487)); (W64.of_int (-4736152177093509389));
(W64.of_int 9014672416777812641); (W64.of_int 4984359074700584923);
(W64.of_int (-2887029340802828403)); (W64.of_int (-7587158779559040837));
(W64.of_int (-3226889267410948733)); (W64.of_int 2938417944103238712);
(W64.of_int (-2279529697979260704)); (W64.of_int 7021364755983520008);
(W64.of_int (-5699981999439543809)); (W64.of_int (-70422136106126370));
(W64.of_int 4972332497587472585); (W64.of_int (-1005689185452603130));
(W64.of_int (-6353529195586080244)); (W64.of_int 418384427087521389);
(W64.of_int (-9048179565493353424)); (W64.of_int 5860820516995035126);
(W64.of_int 6144759436214999286); (W64.of_int 2057362318352304828);
(W64.of_int (-1833664629943763904)); (W64.of_int (-5686588886910490621));
(W64.of_int 5484949054085740288); (W64.of_int 8266722527040612711);
(W64.of_int (-1736797318333312100)); (W64.of_int (-7619591592559817454));
(W64.of_int (-5653300277827871264)); (W64.of_int (-2805408635628270210));
(W64.of_int 4201673510770952224); (W64.of_int (-5542802630767400586));
(W64.of_int (-963011482571663333)); (W64.of_int (-7391284510404850280));
(W64.of_int 6273169357352979088); (W64.of_int 456876313255139270);
(W64.of_int (-4092082967717326062)); (W64.of_int 1621190494596410906);
(W64.of_int (-2053365783733785617)); (W64.of_int (-6670276636412627550));
(W64.of_int 7115633661535853623); (W64.of_int (-3128754293651494253));
(W64.of_int 6935088653178559021); (W64.of_int 3249567803139592707);
(W64.of_int 3228497872348613985); (W64.of_int 2608497649573788682);
(W64.of_int (-5557320224091228199)); (W64.of_int 6459840567858685922);
(W64.of_int (-9221884450999136146)); (W64.of_int 8703981739283037248);
(W64.of_int (-8798104171703783439)); (W64.of_int (-2620674995057133332));
(W64.of_int (-6683477291279709549)); (W64.of_int (-202686826310768826));
(W64.of_int 203645829219293199); (W64.of_int (-4039817201464381253));
(W64.of_int 6618745965193433548); (W64.of_int (-3860679526618670689));
(W64.of_int 2071704274388800110); (W64.of_int 6471675482471026258);
(W64.of_int (-8724390486189509312)); (W64.of_int (-6332167634226479284));
(W64.of_int (-4578558332206810384)); (W64.of_int (-3298093711129306011));
(W64.of_int (-2366758840984369973)); (W64.of_int (-1692001402250280346));
(W64.of_int (-1205041686108142602)); (W64.of_int (-854982138418773943));
(W64.of_int (-604316758675095801)); (W64.of_int (-425523836596219738));
(W64.of_int (-298492804824911630)); (W64.of_int (-208590077685954889));
(W64.of_int (-145211944389320022)); (W64.of_int (-100706867223975277));
(W64.of_int (-69576574077182978)); (W64.of_int (-47886531750657860));
(W64.of_int (-32832905617300018)); (W64.of_int (-22425909576001919));
(W64.of_int (-15259309166283028)); (W64.of_int (-10343392321865658));
(W64.of_int (-6984474311914934)); (W64.of_int (-4698360669985171));
(W64.of_int (-3148474636774176)); (W64.of_int (-2101815542697524));
(W64.of_int (-1397748079304948)); (W64.of_int (-925981864506689));
(W64.of_int (-611103417999386)); (W64.of_int (-401758429195526));
(W64.of_int (-263119325522126)); (W64.of_int (-171663273123127));
(W64.of_int (-111567669955921)); (W64.of_int (-72232911965015));
(W64.of_int (-46587256485616)); (W64.of_int (-29931872023758));
(W64.of_int (-19157324087377)); (W64.of_int (-12214326882085));
(W64.of_int (-7757780197058)); (W64.of_int (-4908379885196));
(W64.of_int (-3093649914360)); (W64.of_int (-1942388117830));
(W64.of_int (-1214876870458)); (W64.of_int (-756936566813));
(W64.of_int (-469804590101)); (W64.of_int (-290472590512));
(W64.of_int (-178905127292)); (W64.of_int (-109766482441));
(W64.of_int (-67088124190)); (W64.of_int (-40846054556));
(W64.of_int (-24773237568)); (W64.of_int (-14967292570));
(W64.of_int (-9008058511)); (W64.of_int (-5400652945));
(W64.of_int (-3225433705)); (W64.of_int (-1918917990));
(W64.of_int (-1137236592)); (W64.of_int (-671384067));
(W64.of_int (-394835975)); (W64.of_int (-231306359));
(W64.of_int (-134984312)); (W64.of_int (-78469989));
(W64.of_int (-45441029)); (W64.of_int (-26212999)); (W64.of_int (-15062913));
(W64.of_int (-8622330)); (W64.of_int (-4916583)); (W64.of_int (-2792704));
(W64.of_int (-1580188)); (W64.of_int (-890665)); (W64.of_int (-500082));
(W64.of_int (-279697)); (W64.of_int (-155831)); (W64.of_int (-86484));
(W64.of_int (-47811)); (W64.of_int (-26328)); (W64.of_int (-14441));
(W64.of_int (-7889)); (W64.of_int (-4292)); (W64.of_int (-2325));
(W64.of_int (-1253)); (W64.of_int (-672)); (W64.of_int (-358));
(W64.of_int (-189)); (W64.of_int (-98)); (W64.of_int (-50));
(W64.of_int (-25)); (W64.of_int (-12)); (W64.of_int (-5)); (W64.of_int (-2))]
).

abbrev jcdt83_hi =
(BArray304.of_list32
[(W32.of_int 25509); (W32.of_int 50968); (W32.of_int 76278);
(W32.of_int 101343); (W32.of_int 126067); (W32.of_int 150361);
(W32.of_int 174138); (W32.of_int 197318); (W32.of_int 219830);
(W32.of_int 241607); (W32.of_int 262590); (W32.of_int 282730);
(W32.of_int 301985); (W32.of_int 320323); (W32.of_int 337718);
(W32.of_int 354156); (W32.of_int 369628); (W32.of_int 384134);
(W32.of_int 397682); (W32.of_int 410285); (W32.of_int 421964);
(W32.of_int 432744); (W32.of_int 442656); (W32.of_int 451734);
(W32.of_int 460015); (W32.of_int 467541); (W32.of_int 474353);
(W32.of_int 480496); (W32.of_int 486012); (W32.of_int 490948);
(W32.of_int 495346); (W32.of_int 499250); (W32.of_int 502703);
(W32.of_int 505743); (W32.of_int 508411); (W32.of_int 510743);
(W32.of_int 512772); (W32.of_int 514532); (W32.of_int 516052);
(W32.of_int 517360); (W32.of_int 518480); (W32.of_int 519437);
(W32.of_int 520251); (W32.of_int 520940); (W32.of_int 521521);
(W32.of_int 522010); (W32.of_int 522419); (W32.of_int 522760);
(W32.of_int 523044); (W32.of_int 523278); (W32.of_int 523471);
(W32.of_int 523630); (W32.of_int 523760); (W32.of_int 523866);
(W32.of_int 523951); (W32.of_int 524021); (W32.of_int 524076);
(W32.of_int 524121); (W32.of_int 524157); (W32.of_int 524185);
(W32.of_int 524208); (W32.of_int 524226); (W32.of_int 524240);
(W32.of_int 524251); (W32.of_int 524259); (W32.of_int 524266);
(W32.of_int 524271); (W32.of_int 524275); (W32.of_int 524278);
(W32.of_int 524280); (W32.of_int 524282); (W32.of_int 524283);
(W32.of_int 524285); (W32.of_int 524285); (W32.of_int 524286);
(W32.of_int 524286)]).

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
  proc __mul48 (a:W64.t, b:W64.t) : W64.t * W64.t = {
    var lo:W64.t;
    var hi:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var top:W64.t;
    var mask:W64.t;
    rax <- a;
    (rdx, rax) <- (mulu_64 rax b);
    lo <- rax;
    hi <- rdx;
    hi <- (hi `<<` (W8.of_int 16));
    top <- lo;
    top <- (top `>>` (W8.of_int 48));
    hi <- (hi `^` top);
    mask <- (W64.of_int 281474976710655);
    lo <- (lo `&` mask);
    return (lo, hi);
  }
  proc __renormalize48 (x0:W64.t, x1:W64.t) : W64.t * W64.t = {
    var mask:W64.t;
    var carry:W64.t;
    mask <- (W64.of_int 281474976710655);
    carry <- x0;
    carry <- (carry `>>` (W8.of_int 48));
    x1 <- (x1 + carry);
    x0 <- (x0 `&` mask);
    return (x0, x1);
  }
  proc __bit_at_u8 (x:W32.t, shift:W8.t) : W8.t = {
    var r:W8.t;
    if ((shift = (W8.of_int 1))) {
      x <- (x `>>` (W8.of_int 1));
    } else {
      
    }
    if ((shift = (W8.of_int 2))) {
      x <- (x `>>` (W8.of_int 2));
    } else {
      
    }
    if ((shift = (W8.of_int 3))) {
      x <- (x `>>` (W8.of_int 3));
    } else {
      
    }
    if ((shift = (W8.of_int 4))) {
      x <- (x `>>` (W8.of_int 4));
    } else {
      
    }
    if ((shift = (W8.of_int 5))) {
      x <- (x `>>` (W8.of_int 5));
    } else {
      
    }
    if ((shift = (W8.of_int 6))) {
      x <- (x `>>` (W8.of_int 6));
    } else {
      
    }
    if ((shift = (W8.of_int 7))) {
      x <- (x `>>` (W8.of_int 7));
    } else {
      
    }
    x <- (x `&` (W32.of_int 1));
    r <- (truncateu8 x);
    return r;
  }
  proc __copy_cneg_regs (x0:W64.t, x1:W64.t, sign:W64.t) : W64.t * W64.t = {
    var y0:W64.t;
    var y1:W64.t;
    var lowmask:W64.t;
    var mask:W64.t;
    lowmask <- (W64.of_int 281474976710655);
    mask <- (W64.of_int 0);
    mask <- (mask - sign);
    y0 <- mask;
    y0 <- (y0 `&` lowmask);
    y0 <- (y0 `^` x0);
    y1 <- x1;
    y1 <- (y1 `^` mask);
    y0 <- (y0 + sign);
    (y0, y1) <@ __renormalize48 (y0, y1);
    return (y0, y1);
  }
  proc __sub_regs (x0:W64.t, x1:W64.t, y0:W64.t, y1:W64.t) : W64.t * W64.t = {
    var n0:W64.t;
    var n1:W64.t;
    (n0, n1) <@ __copy_cneg_regs (y0, y1, (W64.of_int 1));
    x0 <- (x0 + n0);
    x1 <- (x1 + n1);
    return (x0, x1);
  }
  proc __sub_from_threehalves_regs (x0:W64.t, x1:W64.t) : W64.t * W64.t = {
    var add:W64.t;
    (x0, x1) <@ __copy_cneg_regs (x0, x1, (W64.of_int 1));
    add <- (W64.of_int 3);
    add <- (add `<<` (W8.of_int 27));
    x1 <- (x1 + add);
    (x0, x1) <@ __renormalize48 (x0, x1);
    return (x0, x1);
  }
  proc __fixpoint_mul_regs (x0:W64.t, x1:W64.t, y0:W64.t, y1:W64.t) : 
  W64.t * W64.t = {
    var r0:W64.t;
    var r1:W64.t;
    var mask:W64.t;
    var lo:W64.t;
    var hi:W64.t;
    var tmp:W64.t;
    mask <- (W64.of_int 281474976710655);
    (lo, hi) <@ __mul48 (x0, y0);
    tmp <- lo;
    tmp <- (tmp `>>` (W8.of_int 47));
    tmp <- (tmp + (W64.of_int 1));
    tmp <- (tmp `>>` (W8.of_int 1));
    r0 <- hi;
    r0 <- (r0 + tmp);
    (lo, hi) <@ __mul48 (x0, y1);
    r0 <- (r0 + lo);
    r1 <- hi;
    (lo, hi) <@ __mul48 (x1, y0);
    r0 <- (r0 + lo);
    r1 <- (r1 + hi);
    tmp <- (W64.of_int 1);
    tmp <- (tmp `<<` (W8.of_int 27));
    r0 <- (r0 + tmp);
    r0 <- (r0 `>>` (W8.of_int 28));
    tmp <- r1;
    tmp <- (tmp `<<` (W8.of_int 20));
    tmp <- (tmp `&` mask);
    r0 <- (r0 + tmp);
    r1 <- (r1 `>>` (W8.of_int 28));
    tmp <- x1;
    (hi, tmp) <- (mulu_64 tmp y1);
    lo <- tmp;
    tmp <- lo;
    tmp <- (tmp `<<` (W8.of_int 20));
    tmp <- (tmp `&` mask);
    r0 <- (r0 + tmp);
    lo <- (lo `>>` (W8.of_int 28));
    hi <- (hi `<<` (W8.of_int 36));
    lo <- (lo + hi);
    r1 <- (r1 + lo);
    tmp <- r0;
    tmp <- (tmp `>>` (W8.of_int 48));
    r1 <- (r1 + tmp);
    r0 <- (r0 `&` mask);
    return (r0, r1);
  }
  proc __fixpoint_square_regs (x0:W64.t, x1:W64.t) : W64.t * W64.t = {
    var r0:W64.t;
    var r1:W64.t;
    var mask:W64.t;
    var lo:W64.t;
    var hi:W64.t;
    var tmp:W64.t;
    mask <- (W64.of_int 281474976710655);
    (lo, hi) <@ __mul48 (x0, x0);
    r0 <- lo;
    r0 <- (r0 `>>` (W8.of_int 48));
    r0 <- (r0 + hi);
    (lo, hi) <@ __mul48 (x0, x1);
    lo <- (lo `<<` (W8.of_int 1));
    r0 <- (r0 + lo);
    r1 <- hi;
    r1 <- (r1 `<<` (W8.of_int 1));
    r0 <- (r0 `>>` (W8.of_int 28));
    tmp <- r1;
    tmp <- (tmp `<<` (W8.of_int 20));
    tmp <- (tmp `&` mask);
    r0 <- (r0 + tmp);
    r1 <- (r1 `>>` (W8.of_int 28));
    tmp <- x1;
    (hi, tmp) <- (mulu_64 tmp x1);
    lo <- tmp;
    tmp <- lo;
    tmp <- (tmp `<<` (W8.of_int 20));
    tmp <- (tmp `&` mask);
    r0 <- (r0 + tmp);
    lo <- (lo `>>` (W8.of_int 28));
    hi <- (hi `<<` (W8.of_int 36));
    lo <- (lo + hi);
    r1 <- (r1 + lo);
    tmp <- r0;
    tmp <- (tmp `>>` (W8.of_int 48));
    r1 <- (r1 + tmp);
    r0 <- (r0 `&` mask);
    return (r0, r1);
  }
  proc __fixpoint_unsigned_signed_mul_regs (xy0:W64.t, xy1:W64.t, y0:W64.t,
                                            y1:W64.t) : W64.t * W64.t = {
    var z0:W64.t;
    var z1:W64.t;
    var sign:W64.t;
    var x0:W64.t;
    var x1:W64.t;
    sign <- y1;
    sign <- (sign `>>` (W8.of_int 63));
    sign <- (sign `&` (W64.of_int 1));
    (x0, x1) <@ __copy_cneg_regs (y0, y1, sign);
    (z0, z1) <@ __fixpoint_mul_regs (x0, x1, xy0, xy1);
    (z0, z1) <@ __copy_cneg_regs (z0, z1, sign);
    return (z0, z1);
  }
  proc _fixpoint_square (rp:BArray16.t, xp:BArray16.t) : BArray16.t = {
    var x0:W64.t;
    var x1:W64.t;
    var r0:W64.t;
    var r1:W64.t;
    x0 <- (BArray16.get64 xp 0);
    x1 <- (BArray16.get64 xp 1);
    (r0, r1) <@ __fixpoint_square_regs (x0, x1);
    rp <- (BArray16.set64 rp 0 r0);
    rp <- (BArray16.set64 rp 1 r1);
    return rp;
  }
  proc __fixpoint_mul_high_regs (x0:W64.t, x1:W64.t, y:W64.t) : W64.t * W64.t = {
    var r0:W64.t;
    var r1:W64.t;
    var mask:W64.t;
    var tmp0:W64.t;
    var tmp1:W64.t;
    var add:W64.t;
    var t:W64.t;
    mask <- (W64.of_int 281474976710655);
    (r0, r1) <@ __mul48 (x0, y);
    (tmp0, tmp1) <@ __mul48 (x1, y);
    r1 <- (r1 + tmp0);
    add <- (W64.of_int 1);
    add <- (add `<<` (W8.of_int 27));
    r0 <- (r0 + add);
    r0 <- (r0 `>>` (W8.of_int 28));
    t <- r1;
    t <- (t `<<` (W8.of_int 20));
    t <- (t `&` mask);
    r0 <- (r0 + t);
    r1 <- (r1 `>>` (W8.of_int 28));
    tmp1 <- (tmp1 `<<` (W8.of_int 20));
    r1 <- (r1 + tmp1);
    (r0, r1) <@ __renormalize48 (r0, r1);
    return (r0, r1);
  }
  proc _fixpoint_mul_high (rp:BArray16.t, xp:BArray16.t, y:W64.t) : BArray16.t = {
    var x0:W64.t;
    var x1:W64.t;
    var r0:W64.t;
    var r1:W64.t;
    x0 <- (BArray16.get64 xp 0);
    x1 <- (BArray16.get64 xp 1);
    (r0, r1) <@ __fixpoint_mul_high_regs (x0, x1, y);
    rp <- (BArray16.set64 rp 0 r0);
    rp <- (BArray16.set64 rp 1 r1);
    return rp;
  }
  proc _fixpoint_half_round (xp:BArray16.t) : BArray16.t = {
    var x0:W64.t;
    var x1:W64.t;
    var t:W64.t;
    x0 <- (BArray16.get64 xp 0);
    x1 <- (BArray16.get64 xp 1);
    x0 <- (x0 + (W64.of_int 1));
    x0 <- (x0 `>>` (W8.of_int 1));
    t <- x1;
    t <- (t `&` (W64.of_int 1));
    t <- (t `<<` (W8.of_int 47));
    x0 <- (x0 + t);
    x1 <- (x1 `>>` (W8.of_int 1));
    (x0, x1) <@ __renormalize48 (x0, x1);
    xp <- (BArray16.set64 xp 0 x0);
    xp <- (BArray16.set64 xp 1 x1);
    return xp;
  }
  proc _fixpoint_newton_invsqrt (rp:BArray16.t, xhalfp:BArray16.t,
                                 start_cubep:BArray16.t,
                                 start_threep:BArray16.t) : BArray16.t = {
    var x0:W64.t;
    var x1:W64.t;
    var sc0:W64.t;
    var sc1:W64.t;
    var st0:W64.t;
    var st1:W64.t;
    var tmp0:W64.t;
    var tmp1:W64.t;
    var inv0:W64.t;
    var inv1:W64.t;
    var i:W64.t;
    var tmp20:W64.t;
    var tmp21:W64.t;
    x0 <- (BArray16.get64 xhalfp 0);
    x1 <- (BArray16.get64 xhalfp 1);
    sc0 <- (BArray16.get64 start_cubep 0);
    sc1 <- (BArray16.get64 start_cubep 1);
    st0 <- (BArray16.get64 start_threep 0);
    st1 <- (BArray16.get64 start_threep 1);
    (tmp0, tmp1) <@ __fixpoint_mul_regs (x0, x1, sc0, sc1);
    (inv0, inv1) <@ __sub_regs (st0, st1, tmp0, tmp1);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 6))) {
      (tmp0, tmp1) <@ __fixpoint_square_regs (inv0, inv1);
      (tmp20, tmp21) <@ __fixpoint_mul_regs (x0, x1, tmp0, tmp1);
      (tmp20, tmp21) <@ __sub_from_threehalves_regs (tmp20, tmp21);
      (inv0, inv1) <@ __fixpoint_unsigned_signed_mul_regs (inv0, inv1, 
      tmp20, tmp21);
      i <- (i + (W64.of_int 1));
    }
    rp <- (BArray16.set64 rp 0 inv0);
    rp <- (BArray16.set64 rp 1 inv1);
    return rp;
  }
  proc _sample_gauss83 (rand_lo:W64.t, rand_hi:W32.t) : W64.t = {
    var r:W64.t;
    var hip:BArray304.t;
    var lop:BArray1328.t;
    var rndhi:W64.t;
    var i:W64.t;
    var c:W32.t;
    var hi:W64.t;
    var lo:W64.t;
    var borrow:bool;
    var  _0:bool;
    var  _1:bool;
    hip <- witness;
    lop <- witness;
    hip <- jcdt83_hi;
    lop <- jcdt83_lo;
    rndhi <- (zeroextu64 rand_hi);
    i <- (W64.of_int 0);
    r <- (W64.of_int 0);
    while ((i \ult (W64.of_int 76))) {
      c <- (BArray304.get32 hip (W64.to_uint i));
      hi <- (zeroextu64 c);
      lo <- (BArray1328.get64 lop (W64.to_uint i));
      (borrow, lo) <- (sbb_64 lo rand_lo false);
      ( _0, hi) <- (sbb_64 hi rndhi borrow);
      hi <- (hi `>>` (W8.of_int 63));
      r <- (r + hi);
      i <- (i + (W64.of_int 1));
    }
    while ((i \ult (W64.of_int 166))) {
      hi <- (W64.of_int 524287);
      lo <- (BArray1328.get64 lop (W64.to_uint i));
      (borrow, lo) <- (sbb_64 lo rand_lo false);
      ( _1, hi) <- (sbb_64 hi rndhi borrow);
      hi <- (hi `>>` (W8.of_int 63));
      r <- (r + hi);
      i <- (i + (W64.of_int 1));
    }
    return r;
  }
  proc __smulh48 (a:W64.t, b:W64.t) : W64.t = {
    var r:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var tmp:W64.t;
    var rem:W64.t;
    rax <- a;
    (rdx, rax) <- (mulu_64 rax b);
    hi <- rdx;
    lo <- rax;
    tmp <- a;
    tmp <- (tmp `|>>` (W8.of_int 63));
    tmp <- (tmp `&` b);
    hi <- (hi - tmp);
    r <- hi;
    r <- (r `<<` (W8.of_int 16));
    tmp <- lo;
    tmp <- (tmp `>>` (W8.of_int 48));
    r <- (r `|` tmp);
    rem <- lo;
    rem <- (rem `&` (W64.of_int 281474976710655));
    tmp <- (W64.of_int 0);
    tmp <- (tmp - rem);
    rem <- (rem `|` tmp);
    rem <- (rem `>>` (W8.of_int 63));
    r <- (r + rem);
    return r;
  }
  proc _approx_exp (x:W64.t) : W64.t = {
    var result:W64.t;
    result <- (W64.of_int 55868746);
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 743564434));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 6953427278));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 55833338892));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 390932311155));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 2345623661771));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 11728123872951));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 46912496106200));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 140737488354861));
    result <@ __smulh48 (result, x);
    result <- (result - (W64.of_int 281474976710650));
    result <@ __smulh48 (result, x);
    result <- (result + (W64.of_int 281474976710657));
    return result;
  }
  proc __sample_gauss_sigma76_regs (randp:BArray26.t) : W64.t * W64.t *
                                                        W64.t * W64.t = {
    var rounded:W64.t;
    var sqr0:W64.t;
    var sqr1:W64.t;
    var accepted:W64.t;
    var byte:W8.t;
    var rand_gauss83_lo:W64.t;
    var t:W64.t;
    var u:W64.t;
    var rand_gauss83_hi:W32.t;
    var x:W64.t;
    var rand_rej:W64.t;
    var y0:W64.t;
    var y1:W64.t;
    var y:BArray16.t;
    var yp:BArray16.t;
    var sqrbuf:BArray16.t;
    var sqrp:BArray16.t;
    var exp_in:W64.t;
    var ms:W64.t;
    var exp:W64.t;
    sqrbuf <- witness;
    sqrp <- witness;
    y <- witness;
    yp <- witness;
    byte <- (BArray26.get8 randp 0);
    rand_gauss83_lo <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 1);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 2);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 3);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 24));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 4);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 32));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 5);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 40));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 6);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 48));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 7);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 56));
    rand_gauss83_lo <- (rand_gauss83_lo `|` t);
    byte <- (BArray26.get8 randp 8);
    u <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 9);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    u <- (u `|` t);
    byte <- (BArray26.get8 randp 10);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    u <- (u `|` t);
    u <- (u `&` (W64.of_int 524287));
    rand_gauss83_hi <- (truncateu32 u);
    x <@ _sample_gauss83 (rand_gauss83_lo, rand_gauss83_hi);
    byte <- (BArray26.get8 randp 11);
    rand_rej <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 12);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 13);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 14);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 24));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 15);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 32));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 16);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 40));
    rand_rej <- (rand_rej `|` t);
    byte <- (BArray26.get8 randp 17);
    y0 <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 18);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 19);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 20);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 24));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 21);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 32));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 22);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 40));
    y0 <- (y0 `|` t);
    byte <- (BArray26.get8 randp 23);
    y1 <- (zeroextu64 byte);
    byte <- (BArray26.get8 randp 24);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 8));
    y1 <- (y1 `|` t);
    byte <- (BArray26.get8 randp 25);
    t <- (zeroextu64 byte);
    t <- (t `<<` (W8.of_int 16));
    y1 <- (y1 `|` t);
    t <- x;
    t <- (t `<<` (W8.of_int 24));
    y1 <- (y1 `|` t);
    rounded <- y0;
    rounded <- (rounded `>>` (W8.of_int 15));
    rounded <- (rounded + (W64.of_int 1));
    rounded <- (rounded `>>` (W8.of_int 1));
    t <- y1;
    t <- (t `<<` (W8.of_int 32));
    rounded <- (rounded + t);
    y <- (BArray16.set64 y 0 y0);
    y <- (BArray16.set64 y 1 y1);
    yp <- y;
    sqrp <- sqrbuf;
    sqrp <@ _fixpoint_square (sqrp, yp);
    sqr0 <- (BArray16.get64 sqrp 0);
    sqr1 <- (BArray16.get64 sqrp 1);
    exp_in <- sqr1;
    t <- x;
    t <- (t * x);
    t <- (t `<<` (W8.of_int 20));
    exp_in <- (exp_in - t);
    exp_in <- (exp_in `<<` (W8.of_int 20));
    t <- sqr0;
    t <- (t `>>` (W8.of_int 28));
    exp_in <- (exp_in `|` t);
    exp_in <- (exp_in + (W64.of_int 1));
    exp_in <- (exp_in `>>` (W8.of_int 1));
    (* Erased call to declassify *)
    ms <- (init_msf);
    exp_in <- (protect_64 exp_in ms);
    exp <@ _approx_exp (exp_in);
    accepted <- rand_rej;
    t <- rand_rej;
    t <- (t `&` (W64.of_int 1));
    accepted <- (accepted `^` t);
    accepted <- (accepted - exp);
    accepted <- (accepted `|>>` (W8.of_int 63));
    t <- (W64.of_int 0);
    t <- (t - rounded);
    u <- rounded;
    u <- (u `|` t);
    u <- (u `>>` (W8.of_int 63));
    u <- (u `|` rand_rej);
    accepted <- (accepted `&` u);
    accepted <- (accepted `&` (W64.of_int 1));
    return (rounded, sqr0, sqr1, accepted);
  }
  proc _sample_gauss_N_carry (bufp:BArray8192.t, bytecnt:W64.t,
                              signbytes:W64.t, firstflag:W64.t, off:W64.t) : 
  BArray8192.t = {
    var src:W64.t;
    var i:W64.t;
    var idx:W64.t;
    var b:W8.t;
    src <- bytecnt;
    if ((firstflag <> (W64.of_int 0))) {
      src <- (src + signbytes);
    } else {
      
    }
    src <- (src - off);
    i <- (W64.of_int 0);
    while ((i \ult off)) {
      idx <- src;
      idx <- (idx + i);
      b <- (BArray8192.get8 bufp (W64.to_uint idx));
      bufp <- (BArray8192.set8 bufp (W64.to_uint i) b);
      i <- (i + (W64.of_int 1));
    }
    return bufp;
  }
  proc __poly_sample_shake256_init (sp_0:BArray200.t, seedp:int, nonce:W64.t) : 
  BArray200.t = {
    var n:W64.t;
    var pos:W64.t;
    var lane:W64.t;
    var b:W8.t;
    var t:W64.t;
    var shift:W8.t;
    var k:int;
    var src:int;
    sp_0 <@ _keccak_init_state (sp_0);
    src <- seedp;
    n <- nonce;
    pos <- (W64.of_int 0);
    while ((pos \ult (W64.of_int 64))) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (loadW8 Glob.mem src);
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      src <- (src + 1);
      pos <- (pos + (W64.of_int 1));
    }
    k <- 0;
    while ((k < 2)) {
      lane <- pos;
      lane <- (lane `>>` (W8.of_int 3));
      b <- (truncateu8 n);
      t <- (zeroextu64 b);
      shift <- (truncateu8 pos);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      n <- (n `>>` (W8.of_int 8));
      pos <- (pos + (W64.of_int 1));
      k <- (k + 1);
    }
    t <- (W64.of_int 31);
    t <- (t `<<` (W8.of_int 16));
    sp_0 <- (BArray200.set64 sp_0 8 ((BArray200.get64 sp_0 8) `^` t));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <- (BArray200.set64 sp_0 16 ((BArray200.get64 sp_0 16) `^` t));
    return sp_0;
  }
  proc __sample_full_squeeze256 (outp:BArray8192.t, outoff:W64.t,
                                 sp_0:BArray200.t) : BArray8192.t *
                                                     BArray200.t = {
    var idx:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var lane:W64.t;
    var t:W64.t;
    var j:W64.t;
    var b:W8.t;
    idx <- outoff;
    (* Erased call to spill *)
    sp_0 <@ _keccakf1600 (sp_0);
    (* Erased call to unspill *)
    ms <- (init_msf);
    outp <- (protect_ptr outp ms);
    sp_0 <- (protect_ptr sp_0 ms);
    idx <- (protect_64 idx ms);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 136))) {
      lane <- i;
      lane <- (lane `>>` (W8.of_int 3));
      t <- (BArray200.get64 sp_0 (W64.to_uint lane));
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 8))) {
        b <- (truncateu8 t);
        outp <- (BArray8192.set8 outp (W64.to_uint idx) b);
        t <- (t `>>` (W8.of_int 8));
        idx <- (idx + (W64.of_int 1));
        j <- (j + (W64.of_int 1));
      }
      i <- (i + (W64.of_int 8));
    }
    return (outp, sp_0);
  }
  proc __sample_gauss_at (rp:BArray32768.t, sqsump:BArray16.t,
                          coefcntp:BArray8.t, bufp:BArray8192.t,
                          counts:W64.t, dont_write_last:W64.t, bufoff:W64.t,
                          outoff:W64.t) : BArray32768.t * BArray16.t *
                                          BArray8.t = {
    var srp:BArray32768.t;
    var ssqsump:BArray16.t;
    var scoefcntp:BArray8.t;
    var sbufp:BArray8192.t;
    var sdont:W64.t;
    var sbufoff:W64.t;
    var soutoff:W64.t;
    var len:W64.t;
    var bytecnt:W64.t;
    var slen:W64.t;
    var sbytecnt:W64.t;
    var spos:W64.t;
    var scoefcnt:W64.t;
    var randbuf:BArray26.t;
    var randp:BArray26.t;
    var pos:W64.t;
    var base:W64.t;
    var bufp_tmp:BArray8192.t;
    var k:int;
    var byte:W8.t;
    var coefcnt:W64.t;
    var sample:W64.t;
    var sqr0:W64.t;
    var sqr1:W64.t;
    var accepted:W64.t;
    var ms:W64.t;
    var last_0:W64.t;
    var dont:W64.t;
    var rp_tmp:BArray32768.t;
    var outidx:W64.t;
    var accepted64:W64.t;
    var mask:W64.t;
    var sqsum_tmp:BArray16.t;
    var s0:W64.t;
    var s1:W64.t;
    var carry:W64.t;
    var coefcntp_tmp:BArray8.t;
    bufp_tmp <- witness;
    coefcntp_tmp <- witness;
    randbuf <- witness;
    randp <- witness;
    rp_tmp <- witness;
    sbufp <- witness;
    scoefcntp <- witness;
    sqsum_tmp <- witness;
    srp <- witness;
    ssqsump <- witness;
    srp <- rp;
    ssqsump <- sqsump;
    scoefcntp <- coefcntp;
    sbufp <- bufp;
    sdont <- dont_write_last;
    sbufoff <- bufoff;
    soutoff <- outoff;
    len <- counts;
    len <- (len `&` (W64.of_int 4294967295));
    bytecnt <- counts;
    bytecnt <- (bytecnt `>>` (W8.of_int 32));
    slen <- len;
    sbytecnt <- bytecnt;
    spos <- (W64.of_int 0);
    scoefcnt <- (W64.of_int 0);
    randp <- randbuf;
    coefcnt <- scoefcnt;
    len <- slen;
    while ((coefcnt \ult len)) {
      bytecnt <- sbytecnt;
      if ((bytecnt \ult (W64.of_int 26))) {
        slen <- coefcnt;
      } else {
        pos <- spos;
        base <- sbufoff;
        base <- (base + pos);
        bufp_tmp <- sbufp;
        k <- 0;
        while ((k < 26)) {
          byte <-
          (BArray8192.get8 bufp_tmp (W64.to_uint (base + (W64.of_int k))));
          randp <- (BArray26.set8 randp k byte);
          k <- (k + 1);
        }
        (* Erased call to spill *)
        (sample, sqr0, sqr1, accepted) <@ __sample_gauss_sigma76_regs (
        randp);
        (* Erased call to unspill *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        (* Erased call to declassify *)
        ms <- (init_msf);
        coefcnt <- (protect_64 coefcnt ms);
        len <- (protect_64 len ms);
        pos <- (protect_64 pos ms);
        bytecnt <- (protect_64 bytecnt ms);
        accepted <- (protect_64 accepted ms);
        last_0 <- len;
        last_0 <- (last_0 - (W64.of_int 1));
        dont <- sdont;
        (* Erased call to declassify *)
        dont <- (protect_64 dont ms);
        rp_tmp <- srp;
        rp_tmp <- (protect_ptr rp_tmp ms);
        if ((dont <> (W64.of_int 0))) {
          if ((coefcnt = last_0)) {
            accepted64 <- accepted;
          } else {
            outidx <- soutoff;
            outidx <- (outidx + coefcnt);
            rp_tmp <- (BArray32768.set64 rp_tmp (W64.to_uint outidx) sample);
            srp <- rp_tmp;
            accepted64 <- accepted;
          }
        } else {
          outidx <- soutoff;
          outidx <- (outidx + coefcnt);
          rp_tmp <- (BArray32768.set64 rp_tmp (W64.to_uint outidx) sample);
          srp <- rp_tmp;
          accepted64 <- accepted;
        }
        coefcnt <- (coefcnt + accepted64);
        pos <- (pos + (W64.of_int 26));
        bytecnt <- (bytecnt - (W64.of_int 26));
        mask <- (W64.of_int 0);
        mask <- (mask - accepted64);
        sqr0 <- (sqr0 `&` mask);
        sqr1 <- (sqr1 `&` mask);
        sqsum_tmp <- ssqsump;
        ms <- (init_msf);
        sqsum_tmp <- (protect_ptr sqsum_tmp ms);
        s0 <- (BArray16.get64 sqsum_tmp 0);
        s1 <- (BArray16.get64 sqsum_tmp 1);
        s0 <- (s0 + sqr0);
        s1 <- (s1 + sqr1);
        sqsum_tmp <- (BArray16.set64 sqsum_tmp 0 s0);
        sqsum_tmp <- (BArray16.set64 sqsum_tmp 1 s1);
        ssqsump <- sqsum_tmp;
        scoefcnt <- coefcnt;
        spos <- pos;
        sbytecnt <- bytecnt;
      }
      coefcnt <- scoefcnt;
      len <- slen;
    }
    sqsum_tmp <- ssqsump;
    s0 <- (BArray16.get64 sqsum_tmp 0);
    s1 <- (BArray16.get64 sqsum_tmp 1);
    carry <- s0;
    carry <- (carry `>>` (W8.of_int 48));
    s1 <- (s1 + carry);
    mask <- (W64.of_int 281474976710655);
    s0 <- (s0 `&` mask);
    sqsum_tmp <- (BArray16.set64 sqsum_tmp 0 s0);
    sqsum_tmp <- (BArray16.set64 sqsum_tmp 1 s1);
    ssqsump <- sqsum_tmp;
    coefcnt <- scoefcnt;
    coefcntp_tmp <- scoefcntp;
    coefcntp_tmp <- (BArray8.set64 coefcntp_tmp 0 coefcnt);
    scoefcntp <- coefcntp_tmp;
    rp <- srp;
    sqsump <- ssqsump;
    coefcntp <- scoefcntp;
    return (rp, sqsump, coefcntp);
  }
  proc __sample_gauss_N_copy_signs_at (signsp:BArray512.t, bufp:BArray8192.t,
                                       signbytes:W64.t, signoff:W64.t) : 
  BArray512.t = {
    var i:W64.t;
    var b:W8.t;
    var idx:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult signbytes)) {
      b <- (BArray8192.get8 bufp (W64.to_uint i));
      idx <- signoff;
      idx <- (idx + i);
      signsp <- (BArray512.set8 signsp (W64.to_uint idx) b);
      i <- (i + (W64.of_int 1));
    }
    return signsp;
  }
  proc _sample_gauss_N_full_at (rp:BArray32768.t, signsp:BArray512.t,
                                sqsump:BArray16.t, seedp:int, nonce:W64.t,
                                len:W64.t, sampleoff:W64.t, signoff:W64.t) : 
  BArray32768.t * BArray512.t * BArray16.t = {
    var state:BArray200.t;
    var sp_0:BArray200.t;
    var buf:BArray8192.t;
    var bufp:BArray8192.t;
    var coefcnt_buf:BArray8.t;
    var coefcntp:BArray8.t;
    var block:W64.t;
    var off:W64.t;
    var ms:W64.t;
    var signbytes:W64.t;
    var bytecnt:W64.t;
    var counts:W64.t;
    var dont:W64.t;
    var bufoff:W64.t;
    var outoff:W64.t;
    var got:W64.t;
    var total:W64.t;
    var firstflag:W64.t;
    var remaining:W64.t;
    buf <- witness;
    bufp <- witness;
    coefcnt_buf <- witness;
    coefcntp <- witness;
    sp_0 <- witness;
    state <- witness;
    sp_0 <- state;
    bufp <- buf;
    coefcntp <- coefcnt_buf;
    sp_0 <@ __poly_sample_shake256_init (sp_0, seedp, nonce);
    block <- (W64.of_int 0);
    off <- (W64.of_int 0);
    while ((block \ult (W64.of_int 49))) {
      (* Erased call to spill *)
      (bufp, sp_0) <@ __sample_full_squeeze256 (bufp, off, sp_0);
      (* Erased call to declassify *)
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      bufp <- (protect_ptr bufp ms);
      sp_0 <- (protect_ptr sp_0 ms);
      rp <- (protect_ptr rp ms);
      signsp <- (protect_ptr signsp ms);
      sqsump <- (protect_ptr sqsump ms);
      block <- (protect_64 block ms);
      off <- (protect_64 off ms);
      len <- (protect_64 len ms);
      sampleoff <- (protect_64 sampleoff ms);
      signoff <- (protect_64 signoff ms);
      off <- (off + (W64.of_int 136));
      block <- (block + (W64.of_int 1));
    }
    signbytes <- len;
    signbytes <- (signbytes `>>` (W8.of_int 3));
    signsp <@ __sample_gauss_N_copy_signs_at (signsp, bufp, signbytes,
    signoff);
    (* Erased call to spill *)
    bytecnt <- (W64.of_int 6664);
    bytecnt <- (bytecnt - signbytes);
    counts <- bytecnt;
    counts <- (counts `<<` (W8.of_int 32));
    counts <- (counts `|` len);
    dont <- len;
    while (((W64.of_int 256) \ule dont)) {
      dont <- (dont - (W64.of_int 256));
    }
    bufoff <- signbytes;
    outoff <- sampleoff;
    (* Erased call to spill *)
    (rp, sqsump, coefcntp) <@ __sample_gauss_at (rp, sqsump, coefcntp, 
    bufp, counts, dont, bufoff, outoff);
    (* Erased call to unspill *)
    ms <- (init_msf);
    rp <- (protect_ptr rp ms);
    signsp <- (protect_ptr signsp ms);
    sqsump <- (protect_ptr sqsump ms);
    coefcntp <- (protect_ptr coefcntp ms);
    sp_0 <- (protect_ptr sp_0 ms);
    len <- (protect_64 len ms);
    bytecnt <- (protect_64 bytecnt ms);
    signbytes <- (protect_64 signbytes ms);
    dont <- (protect_64 dont ms);
    sampleoff <- (protect_64 sampleoff ms);
    got <- (BArray8.get64 coefcntp 0);
    (* Erased call to declassify *)
    got <- (protect_64 got ms);
    total <- got;
    firstflag <- (W64.of_int 1);
    while ((total \ult len)) {
      off <- bytecnt;
      while (((W64.of_int 26) \ule off)) {
        off <- (off - (W64.of_int 26));
      }
      (* Erased call to spill *)
      bufp <@ _sample_gauss_N_carry (bufp, bytecnt, signbytes, firstflag,
      off);
      (* Erased call to unspill *)
      (* Erased call to spill *)
      ms <- (init_msf);
      bufp <- (protect_ptr bufp ms);
      sp_0 <- (protect_ptr sp_0 ms);
      (bufp, sp_0) <@ __sample_full_squeeze256 (bufp, off, sp_0);
      (* Erased call to declassify *)
      (* Erased call to unspill *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      (* Erased call to declassify *)
      ms <- (init_msf);
      bufp <- (protect_ptr bufp ms);
      sp_0 <- (protect_ptr sp_0 ms);
      rp <- (protect_ptr rp ms);
      signsp <- (protect_ptr signsp ms);
      sqsump <- (protect_ptr sqsump ms);
      signbytes <- (protect_64 signbytes ms);
      len <- (protect_64 len ms);
      total <- (protect_64 total ms);
      dont <- (protect_64 dont ms);
      off <- (protect_64 off ms);
      sampleoff <- (protect_64 sampleoff ms);
      (* Erased call to spill *)
      bytecnt <- (W64.of_int 136);
      bytecnt <- (bytecnt + off);
      remaining <- len;
      remaining <- (remaining - total);
      counts <- bytecnt;
      counts <- (counts `<<` (W8.of_int 32));
      counts <- (counts `|` remaining);
      bufoff <- (W64.of_int 0);
      outoff <- sampleoff;
      outoff <- (outoff + total);
      (* Erased call to spill *)
      (rp, sqsump, coefcntp) <@ __sample_gauss_at (rp, sqsump, coefcntp,
      bufp, counts, dont, bufoff, outoff);
      (* Erased call to unspill *)
      ms <- (init_msf);
      rp <- (protect_ptr rp ms);
      signsp <- (protect_ptr signsp ms);
      sqsump <- (protect_ptr sqsump ms);
      coefcntp <- (protect_ptr coefcntp ms);
      sp_0 <- (protect_ptr sp_0 ms);
      len <- (protect_64 len ms);
      bytecnt <- (protect_64 bytecnt ms);
      signbytes <- (protect_64 signbytes ms);
      total <- (protect_64 total ms);
      dont <- (protect_64 dont ms);
      sampleoff <- (protect_64 sampleoff ms);
      got <- (BArray8.get64 coefcntp 0);
      (* Erased call to declassify *)
      got <- (protect_64 got ms);
      total <- (total + got);
      firstflag <- (W64.of_int 0);
    }
    return (rp, signsp, sqsump);
  }
  proc _hb_checked_mul_rnd13_regs (x:W64.t, y0:W64.t, y1:W64.t, sign:W64.t) : 
  W32.t * W64.t = {
    var ret:W32.t;
    var bad:W64.t;
    var x1:W64.t;
    var x0:W64.t;
    var r0:W64.t;
    var r1:W64.t;
    var magnitude:W64.t;
    var roundbit:W64.t;
    var mask:W64.t;
    x1 <- x;
    x1 <- (x1 `>>` (W8.of_int 32));
    x0 <- x;
    x0 <- (x0 `&` (W64.of_int 4294967295));
    x0 <- (x0 `<<` (W8.of_int 16));
    (r0, r1) <@ __fixpoint_mul_regs (x0, x1, y0, y1);
    magnitude <- r1;
    magnitude <- (magnitude `>>` (W8.of_int 15));
    roundbit <- r1;
    roundbit <- (roundbit `>>` (W8.of_int 14));
    roundbit <- (roundbit `&` (W64.of_int 1));
    magnitude <- (magnitude + roundbit);
    bad <- (W64.of_int 2147483647);
    bad <- (bad - magnitude);
    bad <- (bad `|>>` (W8.of_int 63));
    mask <- (W64.of_int 0);
    mask <- (mask - sign);
    magnitude <- (magnitude `^` mask);
    magnitude <- (magnitude + sign);
    ret <- (truncateu32 magnitude);
    return (ret, bad);
  }
  proc _hb_checked_mul_rnd13 (x:W64.t, yp:BArray16.t, sign:W8.t) : W32.t *
                                                                   W64.t = {
    var ret:W32.t;
    var bad:W64.t;
    var ms:W64.t;
    var y0:W64.t;
    var y1:W64.t;
    var s:W64.t;
    ms <- (init_msf);
    yp <- (protect_ptr yp ms);
    y0 <- (BArray16.get64 yp 0);
    y1 <- (BArray16.get64 yp 1);
    s <- (zeroextu64 sign);
    (ret, bad) <@ _hb_checked_mul_rnd13_regs (x, y0, y1, s);
    return (ret, bad);
  }
  proc _hb_checked_scale_samples (y1p:BArray8192.t, y2p:BArray8192.t,
                                  samplesp:BArray32768.t, signsp:BArray512.t,
                                  scalep:BArray16.t, counts:W64.t) : 
  BArray8192.t * BArray8192.t * W64.t = {
    var bad:W64.t;
    var lcount:W64.t;
    var total:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var byte_idx:W64.t;
    var sign32:W32.t;
    var shift:W8.t;
    var sign8:W8.t;
    var sample:W64.t;
    var r:W32.t;
    var item_bad:W64.t;
    var j:W64.t;
    lcount <- counts;
    lcount <- (lcount `&` (W64.of_int 4294967295));
    total <- counts;
    total <- (total `>>` (W8.of_int 32));
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    samplesp <- (protect_ptr samplesp ms);
    signsp <- (protect_ptr signsp ms);
    scalep <- (protect_ptr scalep ms);
    lcount <- (protect_64 lcount ms);
    total <- (protect_64 total ms);
    bad <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult lcount)) {
      byte_idx <- i;
      byte_idx <- (byte_idx `>>` (W8.of_int 3));
      sign32 <- (zeroextu32 (BArray512.get8 signsp (W64.to_uint byte_idx)));
      shift <- (truncateu8 i);
      shift <- (shift `&` (W8.of_int 7));
      sign8 <@ __bit_at_u8 (sign32, shift);
      sample <- (BArray32768.get64 samplesp (W64.to_uint i));
      (* Erased call to spill *)
      (r, item_bad) <@ _hb_checked_mul_rnd13 (sample, scalep, sign8);
      (* Erased call to unspill *)
      bad <- (bad `|` item_bad);
      ms <- (init_msf);
      y1p <- (protect_ptr y1p ms);
      y2p <- (protect_ptr y2p ms);
      samplesp <- (protect_ptr samplesp ms);
      signsp <- (protect_ptr signsp ms);
      scalep <- (protect_ptr scalep ms);
      lcount <- (protect_64 lcount ms);
      total <- (protect_64 total ms);
      i <- (protect_64 i ms);
      y1p <- (BArray8192.set32 y1p (W64.to_uint i) r);
      i <- (i + (W64.of_int 1));
    }
    j <- (W64.of_int 0);
    while ((i \ult total)) {
      byte_idx <- i;
      byte_idx <- (byte_idx `>>` (W8.of_int 3));
      sign32 <- (zeroextu32 (BArray512.get8 signsp (W64.to_uint byte_idx)));
      shift <- (truncateu8 i);
      shift <- (shift `&` (W8.of_int 7));
      sign8 <@ __bit_at_u8 (sign32, shift);
      sample <- (BArray32768.get64 samplesp (W64.to_uint i));
      (* Erased call to spill *)
      (r, item_bad) <@ _hb_checked_mul_rnd13 (sample, scalep, sign8);
      (* Erased call to unspill *)
      bad <- (bad `|` item_bad);
      ms <- (init_msf);
      y1p <- (protect_ptr y1p ms);
      y2p <- (protect_ptr y2p ms);
      samplesp <- (protect_ptr samplesp ms);
      signsp <- (protect_ptr signsp ms);
      scalep <- (protect_ptr scalep ms);
      total <- (protect_64 total ms);
      i <- (protect_64 i ms);
      j <- (protect_64 j ms);
      y2p <- (BArray8192.set32 y2p (W64.to_uint j) r);
      i <- (i + (W64.of_int 1));
      j <- (j + (W64.of_int 1));
    }
    return (y1p, y2p, bad);
  }
  proc _hb_checked_sqnorm2_2048 (ap:BArray8192.t, acount:W64.t,
                                 bp:BArray8192.t, bcount:W64.t) : W64.t *
                                                                  W64.t = {
    var total:W64.t;
    var overflow:W64.t;
    var ms:W64.t;
    var i:W64.t;
    var a:W32.t;
    var coeff:W64.t;
    var prod:W64.t;
    var carry:bool;
    var  _0:bool;
    var  _1:bool;
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    ap <- (protect_ptr ap ms);
    bp <- (protect_ptr bp ms);
    acount <- (protect_64 acount ms);
    bcount <- (protect_64 bcount ms);
    total <- (W64.of_int 0);
    overflow <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult acount)) {
      a <- (BArray8192.get32 ap (W64.to_uint i));
      coeff <- (sigextu64 a);
      prod <- (coeff * coeff);
      (carry, total) <- (adc_64 total prod false);
      ( _0, prod) <- (sbb_64 prod prod carry);
      overflow <- (overflow `|` prod);
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    while ((i \ult bcount)) {
      a <- (BArray8192.get32 bp (W64.to_uint i));
      coeff <- (sigextu64 a);
      prod <- (coeff * coeff);
      (carry, total) <- (adc_64 total prod false);
      ( _1, prod) <- (sbb_64 prod prod carry);
      overflow <- (overflow `|` prod);
      i <- (i + (W64.of_int 1));
    }
    return (total, overflow);
  }
  proc _hb_checked_scale_and_check_values (y1p:BArray8192.t,
                                           y2p:BArray8192.t,
                                           samplesp:BArray32768.t,
                                           signsp:BArray512.t,
                                           scalep:BArray16.t, lcount:W64.t,
                                           total:W64.t, bound:W64.t) : 
  BArray8192.t * BArray8192.t * W64.t = {
    var accepted:W64.t;
    var ms:W64.t;
    var slcount:W64.t;
    var stotal:W64.t;
    var sbound:W64.t;
    var counts:W64.t;
    var bad:W64.t;
    var sy1p:BArray8192.t;
    var sy2p:BArray8192.t;
    var sbad:W64.t;
    var kcount:W64.t;
    var norm:W64.t;
    var overflow:W64.t;
    var compare:W64.t;
    var borrow:bool;
    var  _0:bool;
    sy1p <- witness;
    sy2p <- witness;
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    samplesp <- (protect_ptr samplesp ms);
    signsp <- (protect_ptr signsp ms);
    scalep <- (protect_ptr scalep ms);
    lcount <- (protect_64 lcount ms);
    total <- (protect_64 total ms);
    bound <- (protect_64 bound ms);
    slcount <- lcount;
    stotal <- total;
    sbound <- bound;
    counts <- total;
    counts <- (counts `<<` (W8.of_int 32));
    counts <- (counts `|` lcount);
    (y1p, y2p, bad) <@ _hb_checked_scale_samples (y1p, y2p, samplesp, 
    signsp, scalep, counts);
    sy1p <- y1p;
    sy2p <- y2p;
    sbad <- bad;
    lcount <- slcount;
    kcount <- stotal;
    kcount <- (kcount - lcount);
    (norm, overflow) <@ _hb_checked_sqnorm2_2048 (y1p, lcount, y2p, kcount);
    bad <- sbad;
    bad <- (bad `|` overflow);
    compare <- sbound;
    (borrow, compare) <- (sbb_64 compare norm false);
    ( _0, compare) <- (sbb_64 compare compare borrow);
    bad <- (bad `|` compare);
    bad <- (bad `^` (W64.of_int 18446744073709551615));
    accepted <- bad;
    accepted <- (accepted `&` (W64.of_int 1));
    (* Erased call to declassify *)
    ms <- (init_msf);
    accepted <- (protect_64 accepted ms);
    y1p <- sy1p;
    y2p <- sy2p;
    return (y1p, y2p, accepted);
  }
  proc _polyfixveclk_scale_and_check_values (y1p:BArray8192.t,
                                             y2p:BArray8192.t,
                                             samplesp:BArray32768.t,
                                             signsp:BArray512.t,
                                             scalep:BArray16.t, lcount:W64.t,
                                             total:W64.t, bound:W64.t) : 
  BArray8192.t * BArray8192.t * W64.t = {
    var accepted:W64.t;
    (y1p, y2p, accepted) <@ _hb_checked_scale_and_check_values (y1p, 
    y2p, samplesp, signsp, scalep, lcount, total, bound);
    return (y1p, y2p, accepted);
  }
  proc _hyperball_b_raw (bp:BArray1.t, seedu:int, nonce:W64.t) : BArray1.t = {
    var s:BArray200.t;
    var sp_0:BArray200.t;
    var i:W64.t;
    var b:W8.t;
    var t:W64.t;
    var lane:W64.t;
    var shift:W8.t;
    var src:int;
    s <- witness;
    sp_0 <- witness;
    sp_0 <- s;
    sp_0 <@ _keccak_init_state (sp_0);
    src <- seedu;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 64))) {
      b <- (loadW8 Glob.mem src);
      t <- (zeroextu64 b);
      lane <- i;
      lane <- (lane `>>` (W8.of_int 3));
      shift <- (truncateu8 i);
      shift <- (shift `&` (W8.of_int 7));
      shift <- (shift `<<` (W8.of_int 3));
      t <- (t `<<` (shift `&` (W8.of_int 63)));
      sp_0 <-
      (BArray200.set64 sp_0 (W64.to_uint lane)
      ((BArray200.get64 sp_0 (W64.to_uint lane)) `^` t));
      src <- (src + 1);
      i <- (i + (W64.of_int 1));
    }
    b <- (truncateu8 nonce);
    t <- (zeroextu64 b);
    sp_0 <- (BArray200.set64 sp_0 8 ((BArray200.get64 sp_0 8) `^` t));
    nonce <- (nonce `>>` (W8.of_int 8));
    b <- (truncateu8 nonce);
    t <- (zeroextu64 b);
    t <- (t `<<` (W8.of_int 8));
    sp_0 <- (BArray200.set64 sp_0 8 ((BArray200.get64 sp_0 8) `^` t));
    t <- (W64.of_int 31);
    t <- (t `<<` (W8.of_int 16));
    sp_0 <- (BArray200.set64 sp_0 8 ((BArray200.get64 sp_0 8) `^` t));
    t <- (W64.of_int 1);
    t <- (t `<<` (W8.of_int 63));
    sp_0 <- (BArray200.set64 sp_0 16 ((BArray200.get64 sp_0 16) `^` t));
    sp_0 <@ _keccakf1600 (sp_0);
    t <- (BArray200.get64 sp_0 0);
    b <- (truncateu8 t);
    bp <- (BArray1.set8 bp 0 b);
    return bp;
  }
  proc _hyperball_full (y1p:BArray8192.t, y2p:BArray8192.t, bp:BArray1.t,
                        counterp:BArray8.t, seedu:int, lcount:W64.t,
                        kcount:W64.t, scale_const:W64.t, bound_const:W64.t,
                        cube0:W64.t, cube1:W64.t, three0:W64.t, three1:W64.t) : 
  BArray8192.t * BArray8192.t * BArray1.t * BArray8.t = {
    var samples:BArray32768.t;
    var samplesp:BArray32768.t;
    var signs:BArray512.t;
    var signsp:BArray512.t;
    var sqsum:BArray16.t;
    var sqsump:BArray16.t;
    var invsqrt:BArray16.t;
    var invsqrtp:BArray16.t;
    var start_cube:BArray16.t;
    var cubep:BArray16.t;
    var start_three:BArray16.t;
    var threep:BArray16.t;
    var ni:W64.t;
    var accepted:W64.t;
    var len:W64.t;
    var sampleoff:W64.t;
    var signoff:W64.t;
    var total:W64.t;
    var idx:W64.t;
    var scale:W64.t;
    var lcoeffs:W64.t;
    var tcoeffs:W64.t;
    cubep <- witness;
    invsqrt <- witness;
    invsqrtp <- witness;
    samples <- witness;
    samplesp <- witness;
    signs <- witness;
    signsp <- witness;
    sqsum <- witness;
    sqsump <- witness;
    start_cube <- witness;
    start_three <- witness;
    threep <- witness;
    samplesp <- samples;
    signsp <- signs;
    sqsump <- sqsum;
    invsqrtp <- invsqrt;
    cubep <- start_cube;
    threep <- start_three;
    cubep <- (BArray16.set64 cubep 0 cube0);
    cubep <- (BArray16.set64 cubep 1 cube1);
    threep <- (BArray16.set64 threep 0 three0);
    threep <- (BArray16.set64 threep 1 three1);
    ni <- (BArray8.get64 counterp 0);
    accepted <- (W64.of_int 0);
    while ((accepted = (W64.of_int 0))) {
      sqsump <- (BArray16.set64 sqsump 0 (W64.of_int 0));
      sqsump <- (BArray16.set64 sqsump 1 (W64.of_int 0));
      len <- (W64.of_int 256);
      len <- (len + (W64.of_int 1));
      sampleoff <- (W64.of_int 0);
      signoff <- (W64.of_int 0);
      (samplesp, signsp, sqsump) <@ _sample_gauss_N_full_at (samplesp,
      signsp, sqsump, seedu, ni, len, sampleoff, signoff);
      ni <- (ni + (W64.of_int 1));
      sampleoff <- (W64.of_int 256);
      signoff <- (W64.of_int 32);
      (samplesp, signsp, sqsump) <@ _sample_gauss_N_full_at (samplesp,
      signsp, sqsump, seedu, ni, len, sampleoff, signoff);
      ni <- (ni + (W64.of_int 1));
      total <- lcount;
      total <- (total + kcount);
      idx <- (W64.of_int 2);
      while ((idx \ult total)) {
        len <- (W64.of_int 256);
        sampleoff <- idx;
        sampleoff <- (sampleoff * (W64.of_int 256));
        signoff <- idx;
        signoff <- (signoff * (W64.of_int 32));
        (samplesp, signsp, sqsump) <@ _sample_gauss_N_full_at (samplesp,
        signsp, sqsump, seedu, ni, len, sampleoff, signoff);
        ni <- (ni + (W64.of_int 1));
        idx <- (idx + (W64.of_int 1));
      }
      sqsump <@ _fixpoint_half_round (sqsump);
      invsqrtp <@ _fixpoint_newton_invsqrt (invsqrtp, sqsump, cubep, threep);
      scale <- scale_const;
      sqsump <@ _fixpoint_mul_high (sqsump, invsqrtp, scale);
      lcoeffs <- lcount;
      lcoeffs <- (lcoeffs `<<` (W8.of_int 8));
      tcoeffs <- total;
      tcoeffs <- (tcoeffs `<<` (W8.of_int 8));
      (y1p, y2p, accepted) <@ _polyfixveclk_scale_and_check_values (y1p, 
      y2p, samplesp, signsp, sqsump, lcoeffs, tcoeffs, bound_const);
    }
    bp <@ _hyperball_b_raw (bp, seedu, ni);
    counterp <- (BArray8.set64 counterp 0 ni);
    return (y1p, y2p, bp, counterp);
  }
  proc polyfixveclk_sample_hyperball_mode2_jazz (y1p:BArray8192.t,
                                                 y2p:BArray8192.t,
                                                 bp:BArray1.t,
                                                 counterp:BArray8.t,
                                                 seedu:int) : BArray8192.t *
                                                              BArray8192.t *
                                                              BArray1.t *
                                                              BArray8.t = {
    var lcount:W64.t;
    var kcount:W64.t;
    var scale_const:W64.t;
    var bound_const:W64.t;
    var cube0:W64.t;
    var cube1:W64.t;
    var three0:W64.t;
    var three1:W64.t;
    var ms:W64.t;
    lcount <- (W64.of_int 4);
    kcount <- (W64.of_int 2);
    scale_const <- (W64.of_int 2643021496320);
    bound_const <- (W64.of_int 6505809026482176);
    cube0 <- (W64.of_int 130843895063578);
    cube1 <- (W64.of_int 4450);
    three0 <- (W64.of_int 115690877850491);
    three1 <- (W64.of_int 10267222);
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    bp <- (protect_ptr bp ms);
    counterp <- (protect_ptr counterp ms);
    lcount <- (protect_64 lcount ms);
    kcount <- (protect_64 kcount ms);
    scale_const <- (protect_64 scale_const ms);
    bound_const <- (protect_64 bound_const ms);
    cube0 <- (protect_64 cube0 ms);
    cube1 <- (protect_64 cube1 ms);
    three0 <- (protect_64 three0 ms);
    three1 <- (protect_64 three1 ms);
    (y1p, y2p, bp, counterp) <@ _hyperball_full (y1p, y2p, bp, counterp,
    seedu, lcount, kcount, scale_const, bound_const, cube0, cube1, three0,
    three1);
    return (y1p, y2p, bp, counterp);
  }
  proc polyfixveclk_sample_hyperball_mode3_jazz (y1p:BArray8192.t,
                                                 y2p:BArray8192.t,
                                                 bp:BArray1.t,
                                                 counterp:BArray8.t,
                                                 seedu:int) : BArray8192.t *
                                                              BArray8192.t *
                                                              BArray1.t *
                                                              BArray8.t = {
    var lcount:W64.t;
    var kcount:W64.t;
    var scale_const:W64.t;
    var bound_const:W64.t;
    var cube0:W64.t;
    var cube1:W64.t;
    var three0:W64.t;
    var three1:W64.t;
    var ms:W64.t;
    lcount <- (W64.of_int 6);
    kcount <- (W64.of_int 3);
    scale_const <- (W64.of_int 4916390789120);
    bound_const <- (W64.of_int 22510896139993088);
    cube0 <- (W64.of_int 28764298784360);
    cube1 <- (W64.of_int 2424);
    three0 <- (W64.of_int 135042716239155);
    three1 <- (W64.of_int 8384969);
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    bp <- (protect_ptr bp ms);
    counterp <- (protect_ptr counterp ms);
    lcount <- (protect_64 lcount ms);
    kcount <- (protect_64 kcount ms);
    scale_const <- (protect_64 scale_const ms);
    bound_const <- (protect_64 bound_const ms);
    cube0 <- (protect_64 cube0 ms);
    cube1 <- (protect_64 cube1 ms);
    three0 <- (protect_64 three0 ms);
    three1 <- (protect_64 three1 ms);
    (y1p, y2p, bp, counterp) <@ _hyperball_full (y1p, y2p, bp, counterp,
    seedu, lcount, kcount, scale_const, bound_const, cube0, cube1, three0,
    three1);
    return (y1p, y2p, bp, counterp);
  }
  proc polyfixveclk_sample_hyperball_mode5_jazz (y1p:BArray8192.t,
                                                 y2p:BArray8192.t,
                                                 bp:BArray1.t,
                                                 counterp:BArray8.t,
                                                 seedu:int) : BArray8192.t *
                                                              BArray8192.t *
                                                              BArray1.t *
                                                              BArray8.t = {
    var lcount:W64.t;
    var kcount:W64.t;
    var scale_const:W64.t;
    var bound_const:W64.t;
    var cube0:W64.t;
    var cube1:W64.t;
    var three0:W64.t;
    var three1:W64.t;
    var ms:W64.t;
    lcount <- (W64.of_int 7);
    kcount <- (W64.of_int 4);
    scale_const <- (W64.of_int 5997831421952);
    bound_const <- (W64.of_int 33503371683954688);
    cube0 <- (W64.of_int 123213818923277);
    cube1 <- (W64.of_int 1794);
    three0 <- (W64.of_int 96105673977137);
    three1 <- (W64.of_int 7585088);
    ms <- (init_msf);
    y1p <- (protect_ptr y1p ms);
    y2p <- (protect_ptr y2p ms);
    bp <- (protect_ptr bp ms);
    counterp <- (protect_ptr counterp ms);
    lcount <- (protect_64 lcount ms);
    kcount <- (protect_64 kcount ms);
    scale_const <- (protect_64 scale_const ms);
    bound_const <- (protect_64 bound_const ms);
    cube0 <- (protect_64 cube0 ms);
    cube1 <- (protect_64 cube1 ms);
    three0 <- (protect_64 three0 ms);
    three1 <- (protect_64 three1 ms);
    (y1p, y2p, bp, counterp) <@ _hyperball_full (y1p, y2p, bp, counterp,
    seedu, lcount, kcount, scale_const, bound_const, cube0, cube1, three0,
    three1);
    return (y1p, y2p, bp, counterp);
  }
}.
