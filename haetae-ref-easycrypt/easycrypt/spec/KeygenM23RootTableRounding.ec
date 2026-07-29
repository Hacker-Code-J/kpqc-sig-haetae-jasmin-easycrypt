require import AllCore IntDiv List Ring StdOrder Real.

import RField RealOrder.

require import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23RootGeneratorCertificate.

import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23RootGeneratorCertificate.

theory KeygenM23RootTableRounding.

(* Every numerical datum below is a certificate, not an assumption.  The
   generic lemmas prove the checker sound; closed integer reduction checks
   the concrete 256-root chain and its Q16 cells. *)
type rcert = real * real.

op center (q : rcert) : real = q.`1.
op radius (q : rcert) : real = q.`2.

op holds (d x : real) (q : rcert) : bool =
  `|d * x - center q| <= radius q.

op mul_error (a ra b rb : real) : real =
  `|a| * rb + `|b| * ra + ra * rb.

lemma holds_mul_squared_scale
    (d x y a ra b rb : real) :
  holds d x (a, ra) =>
  holds d y (b, rb) =>
  holds (d * d) (x * y)
    (a * b, mul_error a ra b rb).
proof.
move=> hx hy.
rewrite /holds /center /radius /= in hx.
rewrite /holds /center /radius /= in hy.
rewrite /holds /center /radius /=.
rewrite /mul_error.
have he :
    d * d * (x * y) - a * b =
      a * (d * y - b)
    + b * (d * x - a)
    + (d * x - a) * (d * y - b) by ring.
rewrite he.
have hsum1 :=
  ler_norm_add
    (a * (d * y - b) + b * (d * x - a))
    ((d * x - a) * (d * y - b)).
have hsum0 :=
  ler_norm_add
    (a * (d * y - b))
    (b * (d * x - a)).
rewrite !normrM in hsum0.
rewrite !normrM in hsum1.
have hra : 0%r <= ra by
  have hn := RealOrder.normr_ge0 (d * x - a);
  smt().
have hrb : 0%r <= rb by
  have hn := RealOrder.normr_ge0 (d * y - b);
  smt().
have haxy :
  `|a| * `|d * y - b| <= `|a| * rb.
+ apply ler_wpmul2l.
  - exact (RealOrder.normr_ge0 a).
  - exact hy.
have hbxy :
  `|b| * `|d * x - a| <= `|b| * ra.
+ apply ler_wpmul2l.
  - exact (RealOrder.normr_ge0 b).
  - exact hx.
have hxy :
  `|d * x - a| * `|d * y - b| <= ra * rb.
+ apply ler_pmul.
  - exact (RealOrder.normr_ge0 (d * x - a)).
  - exact (RealOrder.normr_ge0 (d * y - b)).
  - exact hx.
  - exact hy.
by smt().
qed.

lemma holds_add
    (d x y a ra b rb : real) :
  holds d x (a, ra) =>
  holds d y (b, rb) =>
  holds d (x + y) (a + b, ra + rb).
proof.
move=> hx hy.
rewrite /holds /center /radius /= in hx.
rewrite /holds /center /radius /= in hy.
rewrite /holds /center /radius /=.
have he :
  d * (x + y) - (a + b) =
  (d * x - a) + (d * y - b) by ring.
rewrite he.
have hsum := ler_norm_add (d * x - a) (d * y - b).
by smt().
qed.

lemma holds_sub
    (d x y a ra b rb : real) :
  holds d x (a, ra) =>
  holds d y (b, rb) =>
  holds d (x - y) (a - b, ra + rb).
proof.
move=> hx hy.
rewrite /holds /center /radius /= in hx.
rewrite /holds /center /radius /= in hy.
rewrite /holds /center /radius /=.
have he :
  d * (x - y) - (a - b) =
  (d * x - a) - (d * y - b) by ring.
rewrite he.
have hsum :=
  ler_norm_add (d * x - a) (-(d * y - b)).
rewrite normrN in hsum.
by smt().
qed.

lemma holds_squared_recenter
    (d x a ra c rho : real) :
  0%r < d =>
  holds (d * d) x (a, ra) =>
  `|a - d * c| <= rho =>
  holds d x (c, (ra + rho) / d).
proof.
move=> hd hx hround.
rewrite /holds /center /radius /= in hx.
rewrite /holds /center /radius /=.
have hd0 : d <> 0%r by smt().
have he :
  d * x - c =
  (d * d * x - a + (a - d * c)) / d.
+ field.
  exact hd0.
rewrite he normrM normrV.
have hsum :=
  ler_norm_add (d * d * x - a) (a - d * c).
have hdabs : `|d| = d by rewrite ger0_norm 1:ltrW.
rewrite hdabs.
apply ler_wpmul2r.
+ by rewrite invr_ge0; apply ltrW.
+ by smt().
qed.

type ccert = rcert * rcert.

op real_cert (q : ccert) : rcert = q.`1.
op imag_cert (q : ccert) : rcert = q.`2.

op cholds (d : real) (z : complex) (q : ccert) : bool =
  holds d (creal z) (real_cert q) /\
  holds d (cimag z) (imag_cert q).

op cmul_real_center
    (ar ai br bi : real) : real =
  ar * br - ai * bi.

op cmul_imag_center
    (ar ai br bi : real) : real =
  ar * bi + ai * br.

op cmul_real_error
    (ar rr ai ri br sr bi si : real) : real =
  mul_error ar rr br sr + mul_error ai ri bi si.

op cmul_imag_error
    (ar rr ai ri br sr bi si : real) : real =
  mul_error ar rr bi si + mul_error ai ri br sr.

lemma cholds_mul_squared_scale
    (d : real) (z w : complex)
    (ar rr ai ri br sr bi si : real) :
  cholds d z ((ar, rr), (ai, ri)) =>
  cholds d w ((br, sr), (bi, si)) =>
  cholds (d * d) (cmul z w)
    ((cmul_real_center ar ai br bi,
      cmul_real_error ar rr ai ri br sr bi si),
     (cmul_imag_center ar ai br bi,
      cmul_imag_error ar rr ai ri br sr bi si)).
proof.
move=> [hzr hzi] [hwr hwi].
rewrite /cholds /real_cert /imag_cert /=.
rewrite creal_mul cimag_mul.
split.
+ apply holds_sub.
  - exact (holds_mul_squared_scale d
      (creal z) (creal w) ar rr br sr hzr hwr).
  - exact (holds_mul_squared_scale d
      (cimag z) (cimag w) ai ri bi si hzi hwi).
+ apply holds_add.
  - exact (holds_mul_squared_scale d
      (creal z) (cimag w) ar rr bi si hzr hwi).
  - exact (holds_mul_squared_scale d
      (cimag z) (creal w) ai ri br sr hzi hwr).
qed.

lemma holds_weaken_radius
    (d x c r s : real) :
  holds d x (c, r) =>
  r <= s =>
  holds d x (c, s).
proof.
rewrite /holds /center /radius /=.
by move=> hrc hrs; apply (ler_trans r).
qed.

lemma cholds_mul_budget
    (d : real) (z w : complex)
    (ar rr ai ri br sr bi si cr rrout ci riout : real) :
  0%r < d =>
  cholds d z ((ar, rr), (ai, ri)) =>
  cholds d w ((br, sr), (bi, si)) =>
  cmul_real_error ar rr ai ri br sr bi si +
    `|cmul_real_center ar ai br bi - d * cr| <= d * rrout =>
  cmul_imag_error ar rr ai ri br sr bi si +
    `|cmul_imag_center ar ai br bi - d * ci| <= d * riout =>
  cholds d (cmul z w) ((cr, rrout), (ci, riout)).
proof.
move=> hd hz hw hr hi.
have hp :=
  cholds_mul_squared_scale d z w
    ar rr ai ri br sr bi si hz hw.
move: hp => [hpr hpi].
rewrite /cholds /real_cert /imag_cert /=.
split.
+ apply (holds_weaken_radius d (creal (cmul z w)) cr
    ((cmul_real_error ar rr ai ri br sr bi si +
      `|cmul_real_center ar ai br bi - d * cr|) / d)
    rrout).
  - apply (holds_squared_recenter d
      (creal (cmul z w))
      (cmul_real_center ar ai br bi)
      (cmul_real_error ar rr ai ri br sr bi si)
      cr
      `|cmul_real_center ar ai br bi - d * cr|
      hd hpr (lerr _)).
  - rewrite ler_pdivr_mulr 1:hd.
    by smt().
+ apply (holds_weaken_radius d (cimag (cmul z w)) ci
    ((cmul_imag_error ar rr ai ri br sr bi si +
      `|cmul_imag_center ar ai br bi - d * ci|) / d)
    riout).
  - apply (holds_squared_recenter d
      (cimag (cmul z w))
      (cmul_imag_center ar ai br bi)
      (cmul_imag_error ar rr ai ri br sr bi si)
      ci
      `|cmul_imag_center ar ai br bi - d * ci|
      hd hpi (lerr _)).
  - rewrite ler_pdivr_mulr 1:hd.
    by smt().
qed.

type icert = (int * int) * (int * int).

op ire (q : icert) : int = q.`1.`1.
op irr (q : icert) : int = q.`1.`2.
op iim (q : icert) : int = q.`2.`1.
op iir (q : icert) : int = q.`2.`2.

op ccert_of_icert (q : icert) : ccert =
  (((ire q)%r, (irr q)%r), ((iim q)%r, (iir q)%r)).

op imul_error (a ra b rb : int) : int =
  `|a| * rb + `|b| * ra + ra * rb.

op icmul_real_center
    (ar ai br bi : int) : int =
  ar * br - ai * bi.

op icmul_imag_center
    (ar ai br bi : int) : int =
  ar * bi + ai * br.

op icmul_real_error
    (ar rr ai ri br sr bi si : int) : int =
  imul_error ar rr br sr + imul_error ai ri bi si.

op icmul_imag_error
    (ar rr ai ri br sr bi si : int) : int =
  imul_error ar rr bi si + imul_error ai ri br sr.

op transition_ok (d : int) (q w next : icert) : bool =
  0 < d /\
  icmul_real_error
      (ire q) (irr q) (iim q) (iir q)
      (ire w) (irr w) (iim w) (iir w)
    + `|icmul_real_center (ire q) (iim q) (ire w) (iim w)
          - d * ire next|
      <= d * irr next /\
  icmul_imag_error
      (ire q) (irr q) (iim q) (iir q)
      (ire w) (irr w) (iim w) (iir w)
    + `|icmul_imag_center (ire q) (iim q) (ire w) (iim w)
          - d * iim next|
      <= d * iir next.

lemma imul_error_to_real (a ra b rb : int) :
  (imul_error a ra b rb)%r =
  mul_error a%r ra%r b%r rb%r.
proof.
by rewrite /imul_error /mul_error
           !fromintD !fromintM !fromint_abs.
qed.

lemma icmul_real_center_to_real (ar ai br bi : int) :
  (icmul_real_center ar ai br bi)%r =
  cmul_real_center ar%r ai%r br%r bi%r.
proof.
by rewrite /icmul_real_center /cmul_real_center
           fromintB !fromintM.
qed.

lemma icmul_imag_center_to_real (ar ai br bi : int) :
  (icmul_imag_center ar ai br bi)%r =
  cmul_imag_center ar%r ai%r br%r bi%r.
proof.
by rewrite /icmul_imag_center /cmul_imag_center
           fromintD !fromintM.
qed.

lemma icmul_real_error_to_real
    (ar rr ai ri br sr bi si : int) :
  (icmul_real_error ar rr ai ri br sr bi si)%r =
  cmul_real_error ar%r rr%r ai%r ri%r
    br%r sr%r bi%r si%r.
proof.
by rewrite /icmul_real_error /cmul_real_error
           fromintD !imul_error_to_real.
qed.

lemma icmul_imag_error_to_real
    (ar rr ai ri br sr bi si : int) :
  (icmul_imag_error ar rr ai ri br sr bi si)%r =
  cmul_imag_error ar%r rr%r ai%r ri%r
    br%r sr%r bi%r si%r.
proof.
by rewrite /icmul_imag_error /cmul_imag_error
           fromintD !imul_error_to_real.
qed.

lemma transition_ok_sound
    (d : int) (z w : complex) (q qw next : icert) :
  transition_ok d q qw next =>
  cholds d%r z (ccert_of_icert q) =>
  cholds d%r w (ccert_of_icert qw) =>
  cholds d%r (cmul z w) (ccert_of_icert next).
proof.
move=> [hd [hr hi]] hz hw.
have hdr : 0%r < d%r by rewrite lt_fromint.
have hrr :
  (icmul_real_error
      (ire q) (irr q) (iim q) (iir q)
      (ire qw) (irr qw) (iim qw) (iir qw)
    + `|icmul_real_center (ire q) (iim q) (ire qw) (iim qw)
          - d * ire next|)%r
  <= (d * irr next)%r.
+ by rewrite le_fromint.
have hir :
  (icmul_imag_error
      (ire q) (irr q) (iim q) (iir q)
      (ire qw) (irr qw) (iim qw) (iir qw)
    + `|icmul_imag_center (ire q) (iim q) (ire qw) (iim qw)
          - d * iim next|)%r
  <= (d * iir next)%r.
+ by rewrite le_fromint.
rewrite fromintD fromint_abs fromintB !fromintM
        icmul_real_error_to_real
        icmul_real_center_to_real in hrr.
rewrite fromintD fromint_abs fromintB !fromintM
        icmul_imag_error_to_real
        icmul_imag_center_to_real in hir.
rewrite /ccert_of_icert /ire /irr /iim /iir /= in hz.
rewrite /ccert_of_icert /ire /irr /iim /iir /= in hw.
rewrite /ccert_of_icert /ire /irr /iim /iir /=.
apply (cholds_mul_budget d%r z w
  (ire q)%r (irr q)%r (iim q)%r (iir q)%r
  (ire qw)%r (irr qw)%r (iim qw)%r (iir qw)%r
  (ire next)%r (irr next)%r (iim next)%r (iir next)%r
  hdr hz hw).
+ exact hrr.
+ exact hir.
qed.

op generator_certificate : icert =
  ((999924701839144541, 1), (-12271538285719928, 21)).

lemma generator_certificate_sound :
  cholds certificate_scale%r omega512
    (ccert_of_icert generator_certificate).
proof.
have [hrlo hrhi] := omega512_re_interval.
have [hilo hihi] := omega512_im_interval.
rewrite /cholds /ccert_of_icert /generator_certificate
        /real_cert /imag_cert /ire /irr /iim /iir
        /holds /center /radius /=.
rewrite /certificate_scale in hrlo.
rewrite /certificate_scale in hrhi.
rewrite /certificate_scale in hilo.
rewrite /certificate_scale in hihi.
rewrite /certificate_scale.
split.
+ rewrite ler_norml.
  smt().
+ rewrite ler_norml.
  smt().
qed.

(* Centers are obtained by integer nearest re-centering after each multiply.
   Radii are the least integers accepted by [transition_ok] for that step. *)
op root_certificates : icert list = [
  ((1000000000000000000, 0), (0, 0));
  ((999924701839144541, 1), (-12271538285719928, 21));
  ((999698818696204220, 3), (-24541228522912292, 43));
  ((999322384588349501, 6), (-36807222941358838, 65));
  ((998795456205172393, 9), (-49067674327418022, 87));
  ((998118112900149207, 13), (-61320736302208587, 109));
  ((997290456678690216, 17), (-73564563599667435, 131));
  ((996312612182778012, 22), (-85797312344439904, 153));
  ((995184726672196885, 28), (-98017140329560617, 175));
  ((993906970002356040, 34), (-110222207293883076, 197));
  ((992479534598709996, 40), (-122410675199216218, 219));
  ((990902635427780023, 47), (-134580708507126208, 241));
  ((989176509964780971, 54), (-146730474455361775, 263));
  ((987301418157858379, 62), (-158858143333861467, 285));
  ((985277642388941241, 70), (-170961888760301254, 308));
  ((983105487431216323, 79), (-183039887955140988, 330));
  ((980785280403230444, 89), (-195090322016128299, 352));
  ((978317370719627627, 99), (-207111376192218583, 375));
  ((975702130038528538, 110), (-219101240156869832, 398));
  ((972939952205560138, 121), (-231058108280671156, 421));
  ((970031253194543984, 133), (-242980179903263928, 444));
  ((966976471044852100, 145), (-254865659604514611, 467));
  ((963776065795439857, 158), (-266712757474898428, 490));
  ((960430519415565801, 172), (-278519689385053149, 513));
  ((956940335732208854, 186), (-290284677254462413, 536));
  ((953306040354193825, 200), (-302005949319228114, 559));
  ((949528180593036654, 215), (-313681740398891525, 583));
  ((945607325380521311, 231), (-325310292162262984, 607));
  ((941544065183020763, 247), (-336889853392220102, 631));
  ((937339011912574907, 264), (-348418680249434621, 655));
  ((932992798834738870, 281), (-359895036534988203, 679));
  ((928506080473215547, 298), (-371317193951837599, 703));
  ((923879532511286736, 316), (-382683432365089829, 727));
  ((919113851690057722, 335), (-393992040061048167, 752));
  ((914209755703530631, 354), (-405241314004989931, 776));
  ((909167983090522351, 374), (-416429560097637244, 801));
  ((903989293123443305, 394), (-427555093430282157, 826));
  ((898674465693953815, 415), (-438616238538527702, 851));
  ((893224301195515291, 436), (-449611329654606666, 876));
  ((887639620402853917, 458), (-460538710958240091, 901));
  ((881921264348354997, 480), (-471396736825997717, 926));
  ((876070094195406573, 503), (-482183772079122818, 952));
  ((870086991108711383, 526), (-492898192229784108, 978));
  ((863972856121586701, 550), (-503538383725717631, 1004));
  ((857728610000272031, 574), (-514102744193221800, 1030));
  ((851355193105265102, 599), (-524589682678468981, 1056));
  ((844853565249707031, 624), (-534997619887097287, 1083));
  ((838224705554837999, 650), (-545324988422046500, 1110));
  ((831469612302545191, 676), (-555570233019602304, 1137));
  ((824589302785025216, 703), (-565731810783613278, 1164));
  ((817584813151583646, 730), (-575808191417845382, 1191));
  ((810457198252594739, 758), (-585797857456438943, 1219));
  ((803207531480644855, 787), (-595699304492433427, 1246));
  ((795836904608883479, 816), (-605511041404325598, 1274));
  ((788346427626606203, 846), (-615231590580626930, 1302));
  ((780737228572094417, 876), (-624859488142386462, 1330));
  ((773010453362736897, 907), (-634393284163645584, 1358));
  ((765167265622458860, 938), (-643831542889791552, 1387));
  ((757208846506484479, 970), (-653172842953776852, 1416));
  ((749136394523459255, 1003), (-662415777590171850, 1445));
  ((740951125354959018, 1036), (-671558954847018490, 1474));
  ((732654271672412759, 1069), (-680600997795453141, 1504));
  ((724247082951466843, 1103), (-689540544737067016, 1534));
  ((715730825283818574, 1138), (-698376249408972945, 1564));
  ((707106781186547442, 1173), (-707106781186547616, 1594));
  ((698376249408972769, 1209), (-715730825283818746, 1624));
  ((689540544737066838, 1245), (-724247082951467013, 1655));
  ((680600997795452962, 1282), (-732654271672412927, 1686));
  ((671558954847018310, 1320), (-740951125354959184, 1717));
  ((662415777590171668, 1358), (-749136394523459419, 1749));
  ((653172842953776668, 1397), (-757208846506484641, 1781));
  ((643831542889791366, 1436), (-765167265622459019, 1813));
  ((634393284163645397, 1476), (-773010453362737054, 1845));
  ((624859488142386273, 1516), (-780737228572094572, 1878));
  ((615231590580626739, 1557), (-788346427626606356, 1911));
  ((605511041404325405, 1598), (-795836904608883630, 1944));
  ((595699304492433232, 1640), (-803207531480645003, 1978));
  ((585797857456438746, 1682), (-810457198252594885, 2012));
  ((575808191417845184, 1725), (-817584813151583790, 2047));
  ((565731810783613078, 1768), (-824589302785025358, 2082));
  ((555570233019602103, 1812), (-831469612302545330, 2117));
  ((545324988422046298, 1856), (-838224705554838136, 2152));
  ((534997619887097084, 1901), (-844853565249707166, 2188));
  ((524589682678468777, 1947), (-851355193105265235, 2224));
  ((514102744193221595, 1993), (-857728610000272162, 2260));
  ((503538383725717424, 2040), (-863972856121586829, 2297));
  ((492898192229783899, 2088), (-870086991108711509, 2334));
  ((482183772079122608, 2136), (-876070094195406697, 2371));
  ((471396736825997505, 2185), (-881921264348355119, 2409));
  ((460538710958239877, 2234), (-887639620402854036, 2447));
  ((449611329654606451, 2284), (-893224301195515408, 2486));
  ((438616238538527486, 2334), (-898674465693953930, 2525));
  ((427555093430281940, 2385), (-903989293123443418, 2564));
  ((416429560097637025, 2437), (-909167983090522462, 2603));
  ((405241314004989711, 2489), (-914209755703530739, 2643));
  ((393992040061047946, 2541), (-919113851690057827, 2683));
  ((382683432365089606, 2594), (-923879532511286838, 2724));
  ((371317193951837375, 2648), (-928506080473215647, 2766));
  ((359895036534987978, 2702), (-932992798834738967, 2808));
  ((348418680249434395, 2757), (-937339011912575001, 2850));
  ((336889853392219875, 2813), (-941544065183020855, 2893));
  ((325310292162262756, 2869), (-945607325380521401, 2936));
  ((313681740398891296, 2926), (-949528180593036741, 2979));
  ((302005949319227884, 2983), (-953306040354193909, 3023));
  ((290284677254462182, 3041), (-956940335732208935, 3068));
  ((278519689385052917, 3099), (-960430519415565880, 3113));
  ((266712757474898195, 3158), (-963776065795439934, 3158));
  ((254865659604514378, 3218), (-966976471044852175, 3204));
  ((242980179903263694, 3278), (-970031253194544057, 3250));
  ((231058108280670921, 3339), (-972939952205560208, 3297));
  ((219101240156869596, 3400), (-975702130038528605, 3344));
  ((207111376192218346, 3462), (-978317370719627692, 3392));
  ((195090322016128062, 3525), (-980785280403230506, 3440));
  ((183039887955140750, 3588), (-983105487431216382, 3489));
  ((170961888760301015, 3652), (-985277642388941297, 3539));
  ((158858143333861228, 3717), (-987301418157858432, 3589));
  ((146730474455361535, 3783), (-989176509964781021, 3639));
  ((134580708507125967, 3849), (-990902635427780070, 3690));
  ((122410675199215977, 3916), (-992479534598710041, 3742));
  ((110222207293882835, 3983), (-993906970002356082, 3794));
  ((98017140329560376, 4051), (-995184726672196924, 3847));
  ((85797312344439662, 4120), (-996312612182778048, 3900));
  ((73564563599667193, 4189), (-997290456678690249, 3954));
  ((61320736302208345, 4259), (-998118112900149237, 4009));
  ((49067674327417779, 4330), (-998795456205172420, 4064));
  ((36807222941358595, 4401), (-999322384588349525, 4120));
  ((24541228522912049, 4473), (-999698818696204241, 4176));
  ((12271538285719685, 4546), (-999924701839144559, 4233));
  ((-243, 4619), (-1000000000000000015, 4290));
  ((-12271538285720171, 4693), (-999924701839144553, 4348));
  ((-24541228522912535, 4768), (-999698818696204229, 4407));
  ((-36807222941359081, 4844), (-999322384588349507, 4467));
  ((-49067674327418265, 4920), (-998795456205172396, 4529));
  ((-61320736302208830, 4997), (-998118112900149207, 4592));
  ((-73564563599667678, 5075), (-997290456678690213, 4656));
  ((-85797312344440147, 5153), (-996312612182778006, 4721));
  ((-98017140329560860, 5232), (-995184726672196876, 4788));
  ((-110222207293883319, 5312), (-993906970002356028, 4855));
  ((-122410675199216460, 5393), (-992479534598709981, 4924));
  ((-134580708507126450, 5475), (-990902635427780005, 4994));
  ((-146730474455362017, 5557), (-989176509964780950, 5065));
  ((-158858143333861709, 5641), (-987301418157858355, 5138));
  ((-170961888760301495, 5725), (-985277642388941214, 5212));
  ((-183039887955141229, 5810), (-983105487431216293, 5287));
  ((-195090322016128540, 5896), (-980785280403230411, 5364));
  ((-207111376192218823, 5983), (-978317370719627591, 5442));
  ((-219101240156870072, 6071), (-975702130038528499, 5521));
  ((-231058108280671396, 6160), (-972939952205560096, 5601));
  ((-242980179903264168, 6250), (-970031253194543939, 5683));
  ((-254865659604514851, 6341), (-966976471044852052, 5766));
  ((-266712757474898667, 6432), (-963776065795439806, 5850));
  ((-278519689385053387, 6524), (-960430519415565747, 5936));
  ((-290284677254462650, 6618), (-956940335732208797, 6023));
  ((-302005949319228350, 6713), (-953306040354193765, 6111));
  ((-313681740398891761, 6809), (-949528180593036591, 6201));
  ((-325310292162263219, 6906), (-945607325380521246, 6293));
  ((-336889853392220336, 7004), (-941544065183020695, 6386));
  ((-348418680249434855, 7103), (-937339011912574836, 6480));
  ((-359895036534988436, 7203), (-932992798834738796, 6576));
  ((-371317193951837831, 7304), (-928506080473215470, 6673));
  ((-382683432365090060, 7406), (-923879532511286656, 6771));
  ((-393992040061048397, 7509), (-919113851690057640, 6871));
  ((-405241314004990160, 7613), (-914209755703530547, 6973));
  ((-416429560097637472, 7718), (-909167983090522265, 7076));
  ((-427555093430282384, 7824), (-903989293123443216, 7181));
  ((-438616238538527928, 7932), (-898674465693953723, 7287));
  ((-449611329654606891, 8041), (-893224301195515196, 7394));
  ((-460538710958240315, 8151), (-887639620402853819, 7503));
  ((-471396736825997940, 8262), (-881921264348354897, 7614));
  ((-482183772079123040, 8374), (-876070094195406470, 7726));
  ((-492898192229784328, 8488), (-870086991108711277, 7840));
  ((-503538383725717850, 8603), (-863972856121586592, 7955));
  ((-514102744193222018, 8719), (-857728610000271920, 8072));
  ((-524589682678469197, 8837), (-851355193105264988, 8191));
  ((-534997619887097501, 8956), (-844853565249706915, 8312));
  ((-545324988422046712, 9076), (-838224705554837880, 8434));
  ((-555570233019602514, 9198), (-831469612302545069, 8558));
  ((-565731810783613486, 9321), (-824589302785025092, 8683));
  ((-575808191417845589, 9445), (-817584813151583519, 8810));
  ((-585797857456439148, 9571), (-810457198252594610, 8939));
  ((-595699304492433630, 9699), (-803207531480644724, 9070));
  ((-605511041404325800, 9828), (-795836904608883346, 9202));
  ((-615231590580627131, 9958), (-788346427626606067, 9336));
  ((-624859488142386662, 10090), (-780737228572094279, 9472));
  ((-634393284163645782, 10223), (-773010453362736757, 9610));
  ((-643831542889791748, 10358), (-765167265622458717, 9750));
  ((-653172842953777046, 10494), (-757208846506484334, 9891));
  ((-662415777590172042, 10632), (-749136394523459107, 10034));
  ((-671558954847018680, 10772), (-740951125354958868, 10179));
  ((-680600997795453329, 10913), (-732654271672412607, 10326));
  ((-689540544737067202, 11056), (-724247082951466689, 10475));
  ((-698376249408973130, 11201), (-715730825283818418, 10626));
  ((-707106781186547799, 11347), (-707106781186547284, 10779));
  ((-715730825283818927, 11495), (-698376249408972608, 10934));
  ((-724247082951467192, 11644), (-689540544737066674, 11091));
  ((-732654271672413104, 11795), (-680600997795452795, 11250));
  ((-740951125354959359, 11948), (-671558954847018140, 11411));
  ((-749136394523459591, 12103), (-662415777590171496, 11574));
  ((-757208846506484811, 12259), (-653172842953776494, 11739));
  ((-765167265622459187, 12417), (-643831542889791190, 11906));
  ((-773010453362737220, 12577), (-634393284163645219, 12075));
  ((-780737228572094735, 12739), (-624859488142386093, 12246));
  ((-788346427626606516, 12903), (-615231590580626557, 12419));
  ((-795836904608883788, 13069), (-605511041404325221, 12594));
  ((-803207531480645159, 13237), (-595699304492433046, 12771));
  ((-810457198252595038, 13407), (-585797857456438558, 12951));
  ((-817584813151583940, 13579), (-575808191417844994, 13133));
  ((-824589302785025505, 13753), (-565731810783612886, 13317));
  ((-831469612302545475, 13929), (-555570233019601909, 13503));
  ((-838224705554838278, 14107), (-545324988422046102, 13692));
  ((-844853565249707305, 14287), (-534997619887096886, 13883));
  ((-851355193105265371, 14469), (-524589682678468577, 14076));
  ((-857728610000272296, 14653), (-514102744193221393, 14271));
  ((-863972856121586961, 14839), (-503538383725717221, 14469));
  ((-870086991108711639, 15028), (-492898192229783695, 14669));
  ((-876070094195406824, 15219), (-482183772079122402, 14872));
  ((-881921264348355243, 15412), (-471396736825997298, 15077));
  ((-887639620402854158, 15607), (-460538710958239669, 15285));
  ((-893224301195515527, 15805), (-449611329654606241, 15495));
  ((-898674465693954046, 16005), (-438616238538527274, 15708));
  ((-903989293123443531, 16207), (-427555093430281727, 15924));
  ((-909167983090522572, 16412), (-416429560097636811, 16142));
  ((-914209755703530846, 16619), (-405241314004989495, 16362));
  ((-919113851690057931, 16829), (-393992040061047729, 16585));
  ((-923879532511286939, 17041), (-382683432365089388, 16811));
  ((-928506080473215745, 17256), (-371317193951837156, 17039));
  ((-932992798834739063, 17473), (-359895036534987757, 17270));
  ((-937339011912575094, 17693), (-348418680249434173, 17504));
  ((-941544065183020945, 17915), (-336889853392219651, 17741));
  ((-945607325380521488, 18140), (-325310292162262531, 17980));
  ((-949528180593036825, 18368), (-313681740398891070, 18222));
  ((-953306040354193990, 18599), (-302005949319227657, 18467));
  ((-956940335732209014, 18832), (-290284677254461954, 18715));
  ((-960430519415565956, 19068), (-278519689385052688, 18966));
  ((-963776065795440007, 19307), (-266712757474897966, 19220));
  ((-966976471044852245, 19549), (-254865659604514148, 19477));
  ((-970031253194544124, 19793), (-242980179903263463, 19737));
  ((-972939952205560272, 20040), (-231058108280670689, 20000));
  ((-975702130038528666, 20290), (-219101240156869363, 20266));
  ((-978317370719627750, 20543), (-207111376192218112, 20535));
  ((-980785280403230561, 20799), (-195090322016127827, 20807));
  ((-983105487431216434, 21058), (-183039887955140514, 21082));
  ((-985277642388941347, 21321), (-170961888760300779, 21360));
  ((-987301418157858480, 21587), (-158858143333860991, 21642));
  ((-989176509964781066, 21856), (-146730474455361298, 21927));
  ((-990902635427780112, 22128), (-134580708507125730, 22215));
  ((-992479534598710080, 22403), (-122410675199215739, 22507));
  ((-993906970002356118, 22682), (-110222207293882596, 22802));
  ((-995184726672196957, 22964), (-98017140329560136, 23100));
  ((-996312612182778078, 23249), (-85797312344439422, 23402));
  ((-997290456678690276, 23538), (-73564563599666952, 23707));
  ((-998118112900149261, 23831), (-61320736302208104, 24016));
  ((-998795456205172441, 24127), (-49067674327417538, 24328));
  ((-999322384588349544, 24427), (-36807222941358354, 24644));
  ((-999698818696204257, 24730), (-24541228522911807, 24964));
  ((-999924701839144572, 25037), (-12271538285719443, 25287))].

(* Signed Q16 coordinates, paired exactly as the extracted flat root table. *)
op root_q16_pairs : (int * int) list = [
  (65536, 0);
  (65531, -804);
  (65516, -1608);
  (65492, -2412);
  (65457, -3216);
  (65413, -4019);
  (65358, -4821);
  (65294, -5623);
  (65220, -6424);
  (65137, -7224);
  (65043, -8022);
  (64940, -8820);
  (64827, -9616);
  (64704, -10411);
  (64571, -11204);
  (64429, -11996);
  (64277, -12785);
  (64115, -13573);
  (63944, -14359);
  (63763, -15143);
  (63572, -15924);
  (63372, -16703);
  (63162, -17479);
  (62943, -18253);
  (62714, -19024);
  (62476, -19792);
  (62228, -20557);
  (61971, -21320);
  (61705, -22078);
  (61429, -22834);
  (61145, -23586);
  (60851, -24335);
  (60547, -25080);
  (60235, -25821);
  (59914, -26558);
  (59583, -27291);
  (59244, -28020);
  (58896, -28745);
  (58538, -29466);
  (58172, -30182);
  (57798, -30893);
  (57414, -31600);
  (57022, -32303);
  (56621, -33000);
  (56212, -33692);
  (55794, -34380);
  (55368, -35062);
  (54934, -35738);
  (54491, -36410);
  (54040, -37076);
  (53581, -37736);
  (53114, -38391);
  (52639, -39040);
  (52156, -39683);
  (51665, -40320);
  (51166, -40951);
  (50660, -41576);
  (50146, -42194);
  (49624, -42806);
  (49095, -43412);
  (48559, -44011);
  (48015, -44604);
  (47464, -45190);
  (46906, -45769);
  (46341, -46341);
  (45769, -46906);
  (45190, -47464);
  (44604, -48015);
  (44011, -48559);
  (43412, -49095);
  (42806, -49624);
  (42194, -50146);
  (41576, -50660);
  (40951, -51166);
  (40320, -51665);
  (39683, -52156);
  (39040, -52639);
  (38391, -53114);
  (37736, -53581);
  (37076, -54040);
  (36410, -54491);
  (35738, -54934);
  (35062, -55368);
  (34380, -55794);
  (33692, -56212);
  (33000, -56621);
  (32303, -57022);
  (31600, -57414);
  (30893, -57798);
  (30182, -58172);
  (29466, -58538);
  (28745, -58896);
  (28020, -59244);
  (27291, -59583);
  (26558, -59914);
  (25821, -60235);
  (25080, -60547);
  (24335, -60851);
  (23586, -61145);
  (22834, -61429);
  (22078, -61705);
  (21320, -61971);
  (20557, -62228);
  (19792, -62476);
  (19024, -62714);
  (18253, -62943);
  (17479, -63162);
  (16703, -63372);
  (15924, -63572);
  (15143, -63763);
  (14359, -63944);
  (13573, -64115);
  (12785, -64277);
  (11996, -64429);
  (11204, -64571);
  (10411, -64704);
  (9616, -64827);
  (8820, -64940);
  (8022, -65043);
  (7224, -65137);
  (6424, -65220);
  (5623, -65294);
  (4821, -65358);
  (4019, -65413);
  (3216, -65457);
  (2412, -65492);
  (1608, -65516);
  (804, -65531);
  (0, -65536);
  (-804, -65531);
  (-1608, -65516);
  (-2412, -65492);
  (-3216, -65457);
  (-4019, -65413);
  (-4821, -65358);
  (-5623, -65294);
  (-6424, -65220);
  (-7224, -65137);
  (-8022, -65043);
  (-8820, -64940);
  (-9616, -64827);
  (-10411, -64704);
  (-11204, -64571);
  (-11996, -64429);
  (-12785, -64277);
  (-13573, -64115);
  (-14359, -63944);
  (-15143, -63763);
  (-15924, -63572);
  (-16703, -63372);
  (-17479, -63162);
  (-18253, -62943);
  (-19024, -62714);
  (-19792, -62476);
  (-20557, -62228);
  (-21320, -61971);
  (-22078, -61705);
  (-22834, -61429);
  (-23586, -61145);
  (-24335, -60851);
  (-25080, -60547);
  (-25821, -60235);
  (-26558, -59914);
  (-27291, -59583);
  (-28020, -59244);
  (-28745, -58896);
  (-29466, -58538);
  (-30182, -58172);
  (-30893, -57798);
  (-31600, -57414);
  (-32303, -57022);
  (-33000, -56621);
  (-33692, -56212);
  (-34380, -55794);
  (-35062, -55368);
  (-35738, -54934);
  (-36410, -54491);
  (-37076, -54040);
  (-37736, -53581);
  (-38391, -53114);
  (-39040, -52639);
  (-39683, -52156);
  (-40320, -51665);
  (-40951, -51166);
  (-41576, -50660);
  (-42194, -50146);
  (-42806, -49624);
  (-43412, -49095);
  (-44011, -48559);
  (-44604, -48015);
  (-45190, -47464);
  (-45769, -46906);
  (-46341, -46341);
  (-46906, -45769);
  (-47464, -45190);
  (-48015, -44604);
  (-48559, -44011);
  (-49095, -43412);
  (-49624, -42806);
  (-50146, -42194);
  (-50660, -41576);
  (-51166, -40951);
  (-51665, -40320);
  (-52156, -39683);
  (-52639, -39040);
  (-53114, -38391);
  (-53581, -37736);
  (-54040, -37076);
  (-54491, -36410);
  (-54934, -35738);
  (-55368, -35062);
  (-55794, -34380);
  (-56212, -33692);
  (-56621, -33000);
  (-57022, -32303);
  (-57414, -31600);
  (-57798, -30893);
  (-58172, -30182);
  (-58538, -29466);
  (-58896, -28745);
  (-59244, -28020);
  (-59583, -27291);
  (-59914, -26558);
  (-60235, -25821);
  (-60547, -25080);
  (-60851, -24335);
  (-61145, -23586);
  (-61429, -22834);
  (-61705, -22078);
  (-61971, -21320);
  (-62228, -20557);
  (-62476, -19792);
  (-62714, -19024);
  (-62943, -18253);
  (-63162, -17479);
  (-63372, -16703);
  (-63572, -15924);
  (-63763, -15143);
  (-63944, -14359);
  (-64115, -13573);
  (-64277, -12785);
  (-64429, -11996);
  (-64571, -11204);
  (-64704, -10411);
  (-64827, -9616);
  (-64940, -8820);
  (-65043, -8022);
  (-65137, -7224);
  (-65220, -6424);
  (-65294, -5623);
  (-65358, -4821);
  (-65413, -4019);
  (-65457, -3216);
  (-65492, -2412);
  (-65516, -1608);
  (-65531, -804)].

op transition_pair_ok (p : icert * icert) : bool =
  transition_ok certificate_scale p.`1 generator_certificate p.`2.

lemma root_certificates_size :
  size root_certificates = 256.
proof. trivial. qed.

lemma root_certificate_transitions :
  all transition_pair_ok
    (zip (take 255 root_certificates) (drop 1 root_certificates)).
proof.
rewrite /transition_pair_ok /transition_ok
        /certificate_scale /generator_certificate
        /icmul_real_error /icmul_imag_error
        /imul_error /icmul_real_center /icmul_imag_center
        /ire /irr /iim /iir
        /root_certificates /=.
trivial.
qed.

lemma transition_at
    (rows : icert list) (i : int) :
  size rows = 256 =>
  all transition_pair_ok
    (zip (take 255 rows) (drop 1 rows)) =>
  0 <= i < 255 =>
  transition_ok certificate_scale
    (nth (((0, 0), (0, 0))) rows i)
    generator_certificate
    (nth (((0, 0), (0, 0))) rows (i + 1)).
proof.
move=> hsize hall hi.
have htake : size (take 255 rows) = 255 by
  rewrite size_takel 1:/#.
have hdrop : size (drop 1 rows) = 255 by
  rewrite size_drop 1:// hsize /=.
have hsides :
  size (take 255 rows) = size (drop 1 rows) by
  rewrite htake hdrop.
have halln :
  forall j,
    0 <= j <
      size (zip (take 255 rows) (drop 1 rows)) =>
    transition_pair_ok
      (nth
        ((((0, 0), (0, 0))), (((0, 0), (0, 0))))
        (zip (take 255 rows) (drop 1 rows)) j).
+ rewrite
    (all_nthP transition_pair_ok
      (zip (take 255 rows) (drop 1 rows))
      ((((0, 0), (0, 0))), (((0, 0), (0, 0))))).
  exact hall.
have h := halln i _.
+ by rewrite size_zip htake hdrop.
rewrite
  (nth_zip (((0, 0), (0, 0))) (((0, 0), (0, 0)))
    (take 255 rows) (drop 1 rows) i hsides) in h.
rewrite /transition_pair_ok /= in h.
rewrite (nth_take (((0, 0), (0, 0))) 255 rows i) 1:// 1:/# in h.
rewrite (nth_drop (((0, 0), (0, 0))) 1 rows i) 1:// 1:/# in h.
rewrite addzC in h.
exact h.
qed.

lemma root_certificate_zero :
  cholds certificate_scale%r (ideal_root 0)
    (ccert_of_icert
      (nth (((0, 0), (0, 0))) root_certificates 0)).
proof.
rewrite /root_certificates /= /ideal_root C.expr0.
rewrite /cholds /ccert_of_icert /holds
        /real_cert /imag_cert /center /radius
        /ire /irr /iim /iir /certificate_scale
        /cone /creal /cimag /=.
trivial.
qed.

lemma ideal_root_certificate (j : int) :
  0 <= j < 256 =>
  cholds certificate_scale%r (ideal_root j)
    (ccert_of_icert
      (nth (((0, 0), (0, 0))) root_certificates j)).
proof.
move=> hj.
have hj0 : 0 <= j by smt().
elim/intind: j hj0 hj => [|j hj0 ih] hnext.
+ exact root_certificate_zero.
have hjrange : 0 <= j < 255 by smt().
have hjprev : 0 <= j < 256 by smt().
have hcur := ih hjprev.
have hstep :=
  transition_at root_certificates j
    root_certificates_size root_certificate_transitions hjrange.
have hmul :=
  transition_ok_sound certificate_scale
    (ideal_root j) omega512
    (nth (((0, 0), (0, 0))) root_certificates j)
    generator_certificate
    (nth (((0, 0), (0, 0))) root_certificates (j + 1))
    hstep hcur generator_certificate_sound.
rewrite /ideal_root C.exprSr 1:hj0.
exact hmul.
qed.

op coordinate_cell_ok (c r q : int) : bool =
  2 * (65536 * r + `|65536 * c - q * certificate_scale|)
    < certificate_scale.

op root_cell_ok (p : icert * (int * int)) : bool =
  coordinate_cell_ok (ire p.`1) (irr p.`1) p.`2.`1 /\
  coordinate_cell_ok (iim p.`1) (iir p.`1) p.`2.`2.

lemma root_q16_pairs_size :
  size root_q16_pairs = 256.
proof. trivial. qed.

lemma root_q16_cells :
  all root_cell_ok (zip root_certificates root_q16_pairs).
proof.
rewrite /root_cell_ok /coordinate_cell_ok
        /certificate_scale /ire /irr /iim /iir
        /root_certificates /root_q16_pairs /=.
trivial.
qed.

lemma root_cell_at (j : int) :
  0 <= j < 256 =>
  root_cell_ok
    (nth (((0, 0), (0, 0))) root_certificates j,
     nth (0, 0) root_q16_pairs j).
proof.
move=> hj.
have hsides :
  size root_certificates = size root_q16_pairs by
  rewrite root_certificates_size root_q16_pairs_size.
have halln :
  forall i,
    0 <= i < size (zip root_certificates root_q16_pairs) =>
    root_cell_ok
      (nth ((((0, 0), (0, 0))), (0, 0))
        (zip root_certificates root_q16_pairs) i).
+ rewrite
    (all_nthP root_cell_ok
      (zip root_certificates root_q16_pairs)
      ((((0, 0), (0, 0))), (0, 0))).
  exact root_q16_cells.
have h := halln j _.
+ by rewrite size_zip root_certificates_size root_q16_pairs_size.
rewrite
  (nth_zip (((0, 0), (0, 0))) (0, 0)
    root_certificates root_q16_pairs j hsides) in h.
rewrite /root_cell_ok /= in h.
exact h.
qed.

lemma holds_radius_nonnegative (d x c r : real) :
  holds d x (c, r) =>
  0%r <= r.
proof.
rewrite /holds /center /radius /=.
move=> h.
have hn := normr_ge0 (d * x - c).
by smt().
qed.

lemma cancel_half (d a : real) :
  0%r < d => d * a < d / 2%r => a < 1%r / 2%r.
proof.
move=> hd h.
apply (iffLR _ _ (ltr_pmul2l d hd a (1%r / 2%r))).
have heq : d * (1%r / 2%r) = d / 2%r by field; trivial.
by rewrite heq.
qed.

lemma cancel_scaled_half (d k a : real) :
  0%r < d => d * k * a < d / 2%r => k * a < 1%r / 2%r.
proof.
move=> hd h.
apply (cancel_half d (k * a) hd).
have heq : d * (k * a) = d * k * a by ring.
by rewrite heq.
qed.

lemma coordinate_cell_sound (d c r q : int) (x : real) :
  0 < d =>
  holds d%r x (c%r, r%r) =>
  0 <= r =>
  2 * (65536 * r + `|65536 * c - q * d|) < d =>
  `|x - q%r / 65536%r| < 1%r / 131072%r.
proof.
move=> hd hx hr hcell.
rewrite /holds /center /radius /= in hx.
have hdr : 0%r < d%r by rewrite lt_fromint.
have hrr : 0%r <= r%r by rewrite le_fromint.
have hcellr :
  (2 * (65536 * r + `|65536 * c - q * d|))%r < d%r
  by rewrite lt_fromint.
have htri := ler_norm_add
  (65536%r * (d%r * x - c%r)) ((65536 * c - q * d)%r).
rewrite normrM fromintB !fromintM in htri.
have hbound :
  `|65536%r * (d%r * x - c%r)
      + (65536%r * c%r - q%r * d%r)| < d%r / 2%r by smt().
have he :
  d%r * 65536%r * (x - q%r / 65536%r) =
    65536%r * (d%r * x - c%r)
      + (65536%r * c%r - q%r * d%r) by field.
have hscaled :
  `|d%r * 65536%r * (x - q%r / 65536%r)| < d%r / 2%r
  by rewrite he.
have hdn : `|d%r| = d%r by rewrite ger0_norm 1:ltrW.
have hmul :
  d%r * 65536%r * `|x - q%r / 65536%r| < d%r / 2%r by
  move: hscaled; rewrite !normrM hdn ger0_norm 1://.
have hhalf :
  65536%r * `|x - q%r / 65536%r| < 1%r / 2%r by
  exact (cancel_scaled_half d%r 65536%r
    `|x - q%r / 65536%r| hdr hmul).
have heq : 65536%r * (1%r / 131072%r) = 1%r / 2%r by
  field; trivial.
have htarget :
  65536%r * `|x - q%r / 65536%r| <
    65536%r * (1%r / 131072%r) by rewrite heq.
have hk : 0%r < 65536%r by trivial.
exact (iffLR _ _
  (ltr_pmul2l 65536%r hk `|x - q%r / 65536%r|
    (1%r / 131072%r)) htarget).
qed.

lemma q16_error_rounds (q : int) (x : real) :
  `|x - q%r / 65536%r| < 1%r / 131072%r =>
  floor (65536%r * x + 1%r / 2%r) = q.
proof.
move=> h.
have hb : -(1%r / 131072%r) < x - q%r / 65536%r
    < 1%r / 131072%r by move: h; rewrite ltr_norml.
rewrite floorP.
by smt().
qed.

lemma q16_strict_cell_unique (q k : int) (x : real) :
  `|x - q%r / 65536%r| < 1%r / 131072%r =>
  `|x - k%r / 65536%r| < 1%r / 131072%r =>
  q = k.
proof.
move=> hq hk.
have hqr := q16_error_rounds q x hq.
have hkr := q16_error_rounds k x hk.
by smt().
qed.

lemma ideal_root_q16_error (j : int) :
  0 <= j < 256 =>
  let q = nth (0, 0) root_q16_pairs j in
  `|creal (ideal_root j) - q.`1%r / 65536%r|
    < 1%r / 131072%r /\
  `|cimag (ideal_root j) - q.`2%r / 65536%r|
    < 1%r / 131072%r.
proof.
move=> hj /=.
pose cert := nth (((0, 0), (0, 0))) root_certificates j.
pose q := nth (0, 0) root_q16_pairs j.
have hcert := ideal_root_certificate j hj.
have hcell := root_cell_at j hj.
have hd : 0 < certificate_scale by rewrite /certificate_scale.
rewrite /cholds /ccert_of_icert /real_cert /imag_cert /= in hcert.
rewrite /root_cell_ok /coordinate_cell_ok /= in hcell.
move: hcert => [hcert_re hcert_im].
move: hcell => [hcell_re hcell_im].
have hrre : 0 <= irr cert.
+ have h := holds_radius_nonnegative certificate_scale%r
      (creal (ideal_root j)) (ire cert)%r (irr cert)%r hcert_re.
  by rewrite le_fromint in h.
have hrim : 0 <= iir cert.
+ have h := holds_radius_nonnegative certificate_scale%r
      (cimag (ideal_root j)) (iim cert)%r (iir cert)%r hcert_im.
  by rewrite le_fromint in h.
split.
+ exact (coordinate_cell_sound
    certificate_scale (ire cert) (irr cert) q.`1
    (creal (ideal_root j))
    hd hcert_re hrre hcell_re).
+ exact (coordinate_cell_sound
    certificate_scale (iim cert) (iir cert) q.`2
    (cimag (ideal_root j))
    hd hcert_im hrim hcell_im).
qed.

lemma ideal_root_q16_rounds (j : int) :
  0 <= j < 256 =>
  let q = nth (0, 0) root_q16_pairs j in
  floor (65536%r * creal (ideal_root j) + 1%r / 2%r) = q.`1 /\
  floor (65536%r * cimag (ideal_root j) + 1%r / 2%r) = q.`2.
proof.
move=> hj /=.
have h := ideal_root_q16_error j hj.
move: h => [hre him].
split.
+ exact (q16_error_rounds
    (nth (0, 0) root_q16_pairs j).`1
    (creal (ideal_root j)) hre).
+ exact (q16_error_rounds
    (nth (0, 0) root_q16_pairs j).`2
    (cimag (ideal_root j)) him).
qed.

end KeygenM23RootTableRounding.
