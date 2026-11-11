require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import BArray1024 BArray8192 BArray32768.

abbrev jzetas_inv =
(BArray1024.of_list32
[(W32.of_int 20175); (W32.of_int (-8241)); (W32.of_int (-26554));
(W32.of_int (-31612)); (W32.of_int (-29003)); (W32.of_int 12979);
(W32.of_int (-17463)); (W32.of_int (-7947)); (W32.of_int 12831);
(W32.of_int (-25492)); (W32.of_int 14203); (W32.of_int 21126);
(W32.of_int (-9217)); (W32.of_int (-2931)); (W32.of_int 8099);
(W32.of_int (-13803)); (W32.of_int (-23078)); (W32.of_int (-15822));
(W32.of_int 27740); (W32.of_int 22820); (W32.of_int 16251);
(W32.of_int (-7655)); (W32.of_int 20206); (W32.of_int 994);
(W32.of_int 5823); (W32.of_int 9488); (W32.of_int (-23224));
(W32.of_int 1035); (W32.of_int (-8889)); (W32.of_int 21944);
(W32.of_int 27010); (W32.of_int (-21921)); (W32.of_int (-26934));
(W32.of_int 23751); (W32.of_int (-8908)); (W32.of_int (-10770));
(W32.of_int (-65)); (W32.of_int 3528); (W32.of_int 22805);
(W32.of_int 17737); (W32.of_int 4800); (W32.of_int 27298);
(W32.of_int (-1761)); (W32.of_int 10226); (W32.of_int 7729);
(W32.of_int 11242); (W32.of_int (-12069)); (W32.of_int (-13882));
(W32.of_int 22243); (W32.of_int 31368); (W32.of_int 2202);
(W32.of_int (-18282)); (W32.of_int 3304); (W32.of_int 8253);
(W32.of_int 26851); (W32.of_int (-17261)); (W32.of_int (-25636));
(W32.of_int 10865); (W32.of_int 26985); (W32.of_int (-10639));
(W32.of_int (-3808)); (W32.of_int 10170); (W32.of_int 25912);
(W32.of_int 29735); (W32.of_int 17374); (W32.of_int (-6080));
(W32.of_int (-21454)); (W32.of_int (-10672)); (W32.of_int 9939);
(W32.of_int 20316); (W32.of_int (-13283)); (W32.of_int 28190);
(W32.of_int 30274); (W32.of_int (-21422)); (W32.of_int 18166);
(W32.of_int (-7382)); (W32.of_int (-13642)); (W32.of_int (-5920));
(W32.of_int (-17494)); (W32.of_int (-17182)); (W32.of_int (-7742));
(W32.of_int (-23439)); (W32.of_int 16630); (W32.of_int 30332);
(W32.of_int 12882); (W32.of_int (-12380)); (W32.of_int 16160);
(W32.of_int (-28521)); (W32.of_int (-28254)); (W32.of_int 25921);
(W32.of_int 12543); (W32.of_int 21900); (W32.of_int 2648);
(W32.of_int 23016); (W32.of_int (-10971)); (W32.of_int (-1025));
(W32.of_int 16319); (W32.of_int 31332); (W32.of_int 1311);
(W32.of_int (-689)); (W32.of_int 19194); (W32.of_int 24162);
(W32.of_int (-14864)); (W32.of_int 8796); (W32.of_int 11808);
(W32.of_int (-7682)); (W32.of_int (-28847)); (W32.of_int 30317);
(W32.of_int 7401); (W32.of_int (-13633)); (W32.of_int (-30980));
(W32.of_int (-5764)); (W32.of_int (-13666)); (W32.of_int (-23475));
(W32.of_int 15739); (W32.of_int (-16588)); (W32.of_int 28772);
(W32.of_int 3529); (W32.of_int (-25555)); (W32.of_int (-2464));
(W32.of_int 9190); (W32.of_int 7374); (W32.of_int 21224);
(W32.of_int (-1657)); (W32.of_int 13857); (W32.of_int (-787));
(W32.of_int (-3350)); (W32.of_int 27989); (W32.of_int (-17671));
(W32.of_int (-9560)); (W32.of_int 21442); (W32.of_int (-30362));
(W32.of_int (-23844)); (W32.of_int 9874); (W32.of_int 18586);
(W32.of_int 9522); (W32.of_int (-5876)); (W32.of_int (-29439));
(W32.of_int (-2844)); (W32.of_int 16405); (W32.of_int (-5322));
(W32.of_int (-5913)); (W32.of_int 31064); (W32.of_int (-29563));
(W32.of_int (-7929)); (W32.of_int 14501); (W32.of_int (-12050));
(W32.of_int 18832); (W32.of_int 4127); (W32.of_int 16186);
(W32.of_int (-18731)); (W32.of_int (-21502)); (W32.of_int 27727);
(W32.of_int 10623); (W32.of_int (-11261)); (W32.of_int (-24985));
(W32.of_int 31327); (W32.of_int (-1160)); (W32.of_int (-28710));
(W32.of_int 14941); (W32.of_int (-15510)); (W32.of_int (-6759));
(W32.of_int (-22131)); (W32.of_int 29051); (W32.of_int (-16507));
(W32.of_int (-29068)); (W32.of_int (-9790)); (W32.of_int 5342);
(W32.of_int (-1806)); (W32.of_int 17631); (W32.of_int (-31352));
(W32.of_int 12442); (W32.of_int (-8311)); (W32.of_int (-1488));
(W32.of_int 27685); (W32.of_int (-3970)); (W32.of_int (-15546));
(W32.of_int (-835)); (W32.of_int (-4538)); (W32.of_int 29942);
(W32.of_int (-598)); (W32.of_int 19555); (W32.of_int 16267);
(W32.of_int (-17456)); (W32.of_int (-20353)); (W32.of_int (-19813));
(W32.of_int 9604); (W32.of_int 3761); (W32.of_int (-32114));
(W32.of_int (-12697)); (W32.of_int (-7814)); (W32.of_int (-11591));
(W32.of_int 9430); (W32.of_int (-10615)); (W32.of_int 11459);
(W32.of_int (-7597)); (W32.of_int (-27690)); (W32.of_int 19129);
(W32.of_int (-26533)); (W32.of_int 7941); (W32.of_int (-19616));
(W32.of_int 16608); (W32.of_int 23970); (W32.of_int (-30608));
(W32.of_int 2391); (W32.of_int 15130); (W32.of_int 19646);
(W32.of_int 21464); (W32.of_int (-7893)); (W32.of_int 8577);
(W32.of_int (-29643)); (W32.of_int 17941); (W32.of_int (-11782));
(W32.of_int 32076); (W32.of_int 19725); (W32.of_int 1296);
(W32.of_int (-18239)); (W32.of_int (-16446)); (W32.of_int 12296);
(W32.of_int (-16304)); (W32.of_int (-9383)); (W32.of_int 10049);
(W32.of_int 6789); (W32.of_int 22562); (W32.of_int (-25252));
(W32.of_int (-30820)); (W32.of_int 11361); (W32.of_int (-20143));
(W32.of_int 20035); (W32.of_int 29133); (W32.of_int 27527);
(W32.of_int (-28147)); (W32.of_int 29104); (W32.of_int (-22431));
(W32.of_int (-22935)); (W32.of_int (-10681)); (W32.of_int 19553);
(W32.of_int (-6241)); (W32.of_int 22946); (W32.of_int 16039);
(W32.of_int (-17599)); (W32.of_int (-21408)); (W32.of_int (-13744));
(W32.of_int (-32144)); (W32.of_int 8851); (W32.of_int (-22859));
(W32.of_int 30985); (W32.of_int (-9395)); (W32.of_int 31218);
(W32.of_int (-19064)); (W32.of_int (-20243)); (W32.of_int (-30746));
(W32.of_int (-22229)); (W32.of_int 16505); (W32.of_int (-26964));
(W32.of_int (-29720))]).

abbrev jzetas =
(BArray1024.of_list32
[(W32.of_int 0); (W32.of_int 26964); (W32.of_int (-16505));
(W32.of_int 22229); (W32.of_int 30746); (W32.of_int 20243);
(W32.of_int 19064); (W32.of_int (-31218)); (W32.of_int 9395);
(W32.of_int (-30985)); (W32.of_int 22859); (W32.of_int (-8851));
(W32.of_int 32144); (W32.of_int 13744); (W32.of_int 21408);
(W32.of_int 17599); (W32.of_int (-16039)); (W32.of_int (-22946));
(W32.of_int 6241); (W32.of_int (-19553)); (W32.of_int 10681);
(W32.of_int 22935); (W32.of_int 22431); (W32.of_int (-29104));
(W32.of_int 28147); (W32.of_int (-27527)); (W32.of_int (-29133));
(W32.of_int (-20035)); (W32.of_int 20143); (W32.of_int (-11361));
(W32.of_int 30820); (W32.of_int 25252); (W32.of_int (-22562));
(W32.of_int (-6789)); (W32.of_int (-10049)); (W32.of_int 9383);
(W32.of_int 16304); (W32.of_int (-12296)); (W32.of_int 16446);
(W32.of_int 18239); (W32.of_int (-1296)); (W32.of_int (-19725));
(W32.of_int (-32076)); (W32.of_int 11782); (W32.of_int (-17941));
(W32.of_int 29643); (W32.of_int (-8577)); (W32.of_int 7893);
(W32.of_int (-21464)); (W32.of_int (-19646)); (W32.of_int (-15130));
(W32.of_int (-2391)); (W32.of_int 30608); (W32.of_int (-23970));
(W32.of_int (-16608)); (W32.of_int 19616); (W32.of_int (-7941));
(W32.of_int 26533); (W32.of_int (-19129)); (W32.of_int 27690);
(W32.of_int 7597); (W32.of_int (-11459)); (W32.of_int 10615);
(W32.of_int (-9430)); (W32.of_int 11591); (W32.of_int 7814);
(W32.of_int 12697); (W32.of_int 32114); (W32.of_int (-3761));
(W32.of_int (-9604)); (W32.of_int 19813); (W32.of_int 20353);
(W32.of_int 17456); (W32.of_int (-16267)); (W32.of_int (-19555));
(W32.of_int 598); (W32.of_int (-29942)); (W32.of_int 4538); (W32.of_int 835);
(W32.of_int 15546); (W32.of_int 3970); (W32.of_int (-27685));
(W32.of_int 1488); (W32.of_int 8311); (W32.of_int (-12442));
(W32.of_int 31352); (W32.of_int (-17631)); (W32.of_int 1806);
(W32.of_int (-5342)); (W32.of_int 9790); (W32.of_int 29068);
(W32.of_int 16507); (W32.of_int (-29051)); (W32.of_int 22131);
(W32.of_int 6759); (W32.of_int 15510); (W32.of_int (-14941));
(W32.of_int 28710); (W32.of_int 1160); (W32.of_int (-31327));
(W32.of_int 24985); (W32.of_int 11261); (W32.of_int (-10623));
(W32.of_int (-27727)); (W32.of_int 21502); (W32.of_int 18731);
(W32.of_int (-16186)); (W32.of_int (-4127)); (W32.of_int (-18832));
(W32.of_int 12050); (W32.of_int (-14501)); (W32.of_int 7929);
(W32.of_int 29563); (W32.of_int (-31064)); (W32.of_int 5913);
(W32.of_int 5322); (W32.of_int (-16405)); (W32.of_int 2844);
(W32.of_int 29439); (W32.of_int 5876); (W32.of_int (-9522));
(W32.of_int (-18586)); (W32.of_int (-9874)); (W32.of_int 23844);
(W32.of_int 30362); (W32.of_int (-21442)); (W32.of_int 9560);
(W32.of_int 17671); (W32.of_int (-27989)); (W32.of_int 3350);
(W32.of_int 787); (W32.of_int (-13857)); (W32.of_int 1657);
(W32.of_int (-21224)); (W32.of_int (-7374)); (W32.of_int (-9190));
(W32.of_int 2464); (W32.of_int 25555); (W32.of_int (-3529));
(W32.of_int (-28772)); (W32.of_int 16588); (W32.of_int (-15739));
(W32.of_int 23475); (W32.of_int 13666); (W32.of_int 5764);
(W32.of_int 30980); (W32.of_int 13633); (W32.of_int (-7401));
(W32.of_int (-30317)); (W32.of_int 28847); (W32.of_int 7682);
(W32.of_int (-11808)); (W32.of_int (-8796)); (W32.of_int 14864);
(W32.of_int (-24162)); (W32.of_int (-19194)); (W32.of_int 689);
(W32.of_int (-1311)); (W32.of_int (-31332)); (W32.of_int (-16319));
(W32.of_int 1025); (W32.of_int 10971); (W32.of_int (-23016));
(W32.of_int (-2648)); (W32.of_int (-21900)); (W32.of_int (-12543));
(W32.of_int (-25921)); (W32.of_int 28254); (W32.of_int 28521);
(W32.of_int (-16160)); (W32.of_int 12380); (W32.of_int (-12882));
(W32.of_int (-30332)); (W32.of_int (-16630)); (W32.of_int 23439);
(W32.of_int 7742); (W32.of_int 17182); (W32.of_int 17494); (W32.of_int 5920);
(W32.of_int 13642); (W32.of_int 7382); (W32.of_int (-18166));
(W32.of_int 21422); (W32.of_int (-30274)); (W32.of_int (-28190));
(W32.of_int 13283); (W32.of_int (-20316)); (W32.of_int (-9939));
(W32.of_int 10672); (W32.of_int 21454); (W32.of_int 6080);
(W32.of_int (-17374)); (W32.of_int (-29735)); (W32.of_int (-25912));
(W32.of_int (-10170)); (W32.of_int 3808); (W32.of_int 10639);
(W32.of_int (-26985)); (W32.of_int (-10865)); (W32.of_int 25636);
(W32.of_int 17261); (W32.of_int (-26851)); (W32.of_int (-8253));
(W32.of_int (-3304)); (W32.of_int 18282); (W32.of_int (-2202));
(W32.of_int (-31368)); (W32.of_int (-22243)); (W32.of_int 13882);
(W32.of_int 12069); (W32.of_int (-11242)); (W32.of_int (-7729));
(W32.of_int (-10226)); (W32.of_int 1761); (W32.of_int (-27298));
(W32.of_int (-4800)); (W32.of_int (-17737)); (W32.of_int (-22805));
(W32.of_int (-3528)); (W32.of_int 65); (W32.of_int 10770); (W32.of_int 8908);
(W32.of_int (-23751)); (W32.of_int 26934); (W32.of_int 21921);
(W32.of_int (-27010)); (W32.of_int (-21944)); (W32.of_int 8889);
(W32.of_int (-1035)); (W32.of_int 23224); (W32.of_int (-9488));
(W32.of_int (-5823)); (W32.of_int (-994)); (W32.of_int (-20206));
(W32.of_int 7655); (W32.of_int (-16251)); (W32.of_int (-22820));
(W32.of_int (-27740)); (W32.of_int 15822); (W32.of_int 23078);
(W32.of_int 13803); (W32.of_int (-8099)); (W32.of_int 2931);
(W32.of_int 9217); (W32.of_int (-21126)); (W32.of_int (-14203));
(W32.of_int 25492); (W32.of_int (-12831)); (W32.of_int 7947);
(W32.of_int 17463); (W32.of_int (-12979)); (W32.of_int 29003);
(W32.of_int 31612); (W32.of_int 26554); (W32.of_int 8241);
(W32.of_int (-20175))]).

module M = {
  proc __montgomery_reduce (a:W64.t) : W32.t = {
    var t32:W32.t;
    var t64:W64.t;
    t32 <- (truncateu32 a);
    t32 <- (t32 * (W32.of_int 940508161));
    t64 <- (sigextu64 t32);
    t64 <- (t64 * (W64.of_int 64513));
    a <- (a - t64);
    a <- (a `|>>` (W8.of_int 32));
    t32 <- (truncateu32 a);
    return t32;
  }
  proc __fqmul (a:W32.t, b:W32.t) : W32.t = {
    var r:W32.t;
    var ta:W64.t;
    var tb:W64.t;
    var t:W64.t;
    ta <- (sigextu64 a);
    tb <- (sigextu64 b);
    t <- (ta * tb);
    r <@ __montgomery_reduce (t);
    return r;
  }
  proc _polyvec_ntt (xp:BArray8192.t, count:W64.t) : BArray8192.t = {
    var zetasp:BArray1024.t;
    var poly:W64.t;
    var base:W64.t;
    var zetasctr:W64.t;
    var len:W64.t;
    var start:W64.t;
    var zeta_0:W32.t;
    var j:W64.t;
    var cmp:W64.t;
    var idx:W64.t;
    var s:W32.t;
    var offset:W64.t;
    var idx2:W64.t;
    var coeff:W32.t;
    var t:W32.t;
    zetasp <- witness;
    zetasp <- jzetas;
    poly <- (W64.of_int 0);
    base <- (W64.of_int 0);
    while ((poly \ult count)) {
      zetasctr <- (W64.of_int 0);
      len <- (W64.of_int 128);
      while (((W64.of_int 0) \ult len)) {
        start <- (W64.of_int 0);
        while ((start \ult (W64.of_int 256))) {
          zetasctr <- (zetasctr + (W64.of_int 1));
          zeta_0 <- (BArray1024.get32 zetasp (W64.to_uint zetasctr));
          j <- start;
          cmp <- start;
          cmp <- (cmp + len);
          while ((j \ult cmp)) {
            idx <- base;
            idx <- (idx + j);
            s <- (BArray8192.get32 xp (W64.to_uint idx));
            offset <- j;
            offset <- (offset + len);
            idx2 <- base;
            idx2 <- (idx2 + offset);
            coeff <- (BArray8192.get32 xp (W64.to_uint idx2));
            t <@ __fqmul (zeta_0, coeff);
            coeff <- s;
            coeff <- (coeff - t);
            xp <- (BArray8192.set32 xp (W64.to_uint idx2) coeff);
            s <- (s + t);
            xp <- (BArray8192.set32 xp (W64.to_uint idx) s);
            j <- (j + (W64.of_int 1));
          }
          start <- j;
          start <- (start + len);
        }
        len <- (len `>>` (W8.of_int 1));
      }
      base <- (base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return xp;
  }
  proc _polyvec_invntt (xp:BArray8192.t, count:W64.t) : BArray8192.t = {
    var zetasp:BArray1024.t;
    var poly:W64.t;
    var base:W64.t;
    var zetasctr:W64.t;
    var len:W64.t;
    var start:W64.t;
    var zeta_0:W32.t;
    var j:W64.t;
    var cmp:W64.t;
    var idx:W64.t;
    var t:W32.t;
    var offset:W64.t;
    var idx2:W64.t;
    var coeff:W32.t;
    var s:W32.t;
    zetasp <- witness;
    zetasp <- jzetas_inv;
    poly <- (W64.of_int 0);
    base <- (W64.of_int 0);
    while ((poly \ult count)) {
      zetasctr <- (W64.of_int 0);
      len <- (W64.of_int 1);
      while ((len \ult (W64.of_int 256))) {
        start <- (W64.of_int 0);
        while ((start \ult (W64.of_int 256))) {
          zeta_0 <- (BArray1024.get32 zetasp (W64.to_uint zetasctr));
          zetasctr <- (zetasctr + (W64.of_int 1));
          j <- start;
          cmp <- start;
          cmp <- (cmp + len);
          while ((j \ult cmp)) {
            idx <- base;
            idx <- (idx + j);
            t <- (BArray8192.get32 xp (W64.to_uint idx));
            offset <- j;
            offset <- (offset + len);
            idx2 <- base;
            idx2 <- (idx2 + offset);
            coeff <- (BArray8192.get32 xp (W64.to_uint idx2));
            s <- t;
            s <- (s + coeff);
            xp <- (BArray8192.set32 xp (W64.to_uint idx) s);
            t <- (t - coeff);
            t <@ __fqmul (zeta_0, t);
            xp <- (BArray8192.set32 xp (W64.to_uint idx2) t);
            j <- (j + (W64.of_int 1));
          }
          start <- j;
          start <- (start + len);
        }
        len <- (len `<<` (W8.of_int 1));
      }
      zeta_0 <- (BArray1024.get32 zetasp 255);
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        idx <- base;
        idx <- (idx + j);
        coeff <- (BArray8192.get32 xp (W64.to_uint idx));
        t <@ __fqmul (zeta_0, coeff);
        xp <- (BArray8192.set32 xp (W64.to_uint idx) t);
        j <- (j + (W64.of_int 1));
      }
      base <- (base + (W64.of_int 256));
      poly <- (poly + (W64.of_int 1));
    }
    return xp;
  }
  proc _polymat_pointwise_acc (tp:BArray8192.t, mp:BArray32768.t,
                               vp:BArray8192.t, rows:W64.t, cols:W64.t) : 
  BArray8192.t = {
    var row:W64.t;
    var row_out:W64.t;
    var row_mat:W64.t;
    var j:W64.t;
    var oidx:W64.t;
    var col:W64.t;
    var col_off:W64.t;
    var midx:W64.t;
    var vidx:W64.t;
    var a:W32.t;
    var b:W32.t;
    var t:W32.t;
    var acc:W32.t;
    row <- (W64.of_int 0);
    row_out <- (W64.of_int 0);
    row_mat <- (W64.of_int 0);
    while ((row \ult rows)) {
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        oidx <- row_out;
        oidx <- (oidx + j);
        tp <- (BArray8192.set32 tp (W64.to_uint oidx) (W32.of_int 0));
        j <- (j + (W64.of_int 1));
      }
      col <- (W64.of_int 0);
      col_off <- (W64.of_int 0);
      while ((col \ult cols)) {
        j <- (W64.of_int 0);
        while ((j \ult (W64.of_int 256))) {
          midx <- row_mat;
          midx <- (midx + col_off);
          midx <- (midx + j);
          vidx <- col_off;
          vidx <- (vidx + j);
          oidx <- row_out;
          oidx <- (oidx + j);
          a <- (BArray32768.get32 mp (W64.to_uint midx));
          b <- (BArray8192.get32 vp (W64.to_uint vidx));
          t <@ __fqmul (a, b);
          acc <- (BArray8192.get32 tp (W64.to_uint oidx));
          acc <- (acc + t);
          tp <- (BArray8192.set32 tp (W64.to_uint oidx) acc);
          j <- (j + (W64.of_int 1));
        }
        col_off <- (col_off + (W64.of_int 256));
        col <- (col + (W64.of_int 1));
      }
      row_mat <- (row_mat + col_off);
      row_out <- (row_out + (W64.of_int 256));
      row <- (row + (W64.of_int 1));
    }
    return tp;
  }
  proc _keypair_copy_vec (rp:BArray8192.t, ap:BArray8192.t, count:W64.t) : 
  BArray8192.t = {
    var i:W64.t;
    var a:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult count)) {
      a <- (BArray8192.get32 ap (W64.to_uint i));
      rp <- (BArray8192.set32 rp (W64.to_uint i) a);
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc keypair_m23_matrix_jazz (bp:BArray8192.t, s1hatp:BArray8192.t,
                                ap:BArray32768.t, s1p:BArray8192.t,
                                rows:W64.t, cols:W64.t) : BArray8192.t *
                                                          BArray8192.t = {
    var ms:W64.t;
    var count:W64.t;
    ms <- (init_msf);
    bp <- (protect_ptr bp ms);
    s1hatp <- (protect_ptr s1hatp ms);
    ap <- (protect_ptr ap ms);
    s1p <- (protect_ptr s1p ms);
    rows <- (protect_64 rows ms);
    cols <- (protect_64 cols ms);
    count <- cols;
    count <- (count * (W64.of_int 256));
    count <- (protect_64 count ms);
    s1hatp <@ _keypair_copy_vec (s1hatp, s1p, count);
    (* Erased call to spill *)
    s1hatp <@ _polyvec_ntt (s1hatp, cols);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    bp <- (protect_ptr bp ms);
    ap <- (protect_ptr ap ms);
    s1hatp <- (protect_ptr s1hatp ms);
    rows <- (protect_64 rows ms);
    cols <- (protect_64 cols ms);
    bp <@ _polymat_pointwise_acc (bp, ap, s1hatp, rows, cols);
    ms <- (init_msf);
    bp <- (protect_ptr bp ms);
    rows <- (protect_64 rows ms);
    bp <@ _polyvec_invntt (bp, rows);
    return (bp, s1hatp);
  }
  proc keypair_m5_matrix_jazz (bp:BArray8192.t, s1hatp:BArray8192.t,
                               ap:BArray32768.t, s1p:BArray8192.t,
                               rows:W64.t, cols:W64.t) : BArray8192.t *
                                                         BArray8192.t = {
    var ms:W64.t;
    var count:W64.t;
    ms <- (init_msf);
    bp <- (protect_ptr bp ms);
    s1hatp <- (protect_ptr s1hatp ms);
    ap <- (protect_ptr ap ms);
    s1p <- (protect_ptr s1p ms);
    rows <- (protect_64 rows ms);
    cols <- (protect_64 cols ms);
    count <- cols;
    count <- (count * (W64.of_int 256));
    count <- (protect_64 count ms);
    s1hatp <@ _keypair_copy_vec (s1hatp, s1p, count);
    (* Erased call to spill *)
    s1hatp <@ _polyvec_ntt (s1hatp, cols);
    (* Erased call to unspill *)
    (* Erased call to declassify *)
    (* Erased call to declassify *)
    ms <- (init_msf);
    bp <- (protect_ptr bp ms);
    ap <- (protect_ptr ap ms);
    s1hatp <- (protect_ptr s1hatp ms);
    rows <- (protect_64 rows ms);
    cols <- (protect_64 cols ms);
    bp <@ _polymat_pointwise_acc (bp, ap, s1hatp, rows, cols);
    return (bp, s1hatp);
  }
  proc keypair_copy_ntt_jazz (dstp:BArray8192.t, srcp:BArray8192.t,
                              count:W64.t) : BArray8192.t = {
    var ms:W64.t;
    var coeffs:W64.t;
    ms <- (init_msf);
    dstp <- (protect_ptr dstp ms);
    srcp <- (protect_ptr srcp ms);
    count <- (protect_64 count ms);
    coeffs <- count;
    coeffs <- (coeffs * (W64.of_int 256));
    coeffs <- (protect_64 coeffs ms);
    dstp <@ _keypair_copy_vec (dstp, srcp, coeffs);
    ms <- (init_msf);
    dstp <- (protect_ptr dstp ms);
    count <- (protect_64 count ms);
    dstp <@ _polyvec_ntt (dstp, count);
    return dstp;
  }
}.
