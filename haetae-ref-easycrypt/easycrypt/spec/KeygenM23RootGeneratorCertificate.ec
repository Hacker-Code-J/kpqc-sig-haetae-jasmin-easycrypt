require import AllCore IntDiv List Ring StdOrder Real RealExp.

require import KeygenM23ComplexReal KeygenM23IdealRootDFT.

import RField RealOrder.
import KeygenM23ComplexReal KeygenM23IdealRootDFT.

theory KeygenM23RootGeneratorCertificate.

op certificate_scale : int = 1000000000000000000.

lemma sqrt_between (lo hi x : real) :
  0%r <= lo =>
  0%r <= hi =>
  0%r <= x =>
  lo ^ 2 <= x =>
  x <= hi ^ 2 =>
  lo <= sqrt x /\ sqrt x <= hi.
proof.
move=> hlo hhi hx hlo2 hhi2.
have hlo_sq : 0%r <= lo ^ 2.
+ rewrite expr2.
  exact (mulr_ge0 lo lo hlo hlo).
have hhi_sq : 0%r <= hi ^ 2.
+ rewrite expr2.
  exact (mulr_ge0 hi hi hhi hhi).
have hl := sqrt_mono (lo ^ 2) x hlo_sq hx.
have hu := sqrt_mono x (hi ^ 2) hx hhi_sq.
rewrite sqrtsq_ge0 1:hlo in hl.
rewrite sqrtsq_ge0 1:hhi in hu.
by split; [apply hl | apply hu].
qed.

lemma omega8_re_interval :
  707106781186547524%r / certificate_scale%r <= creal omega8 /\
  creal omega8 <= 707106781186547525%r / certificate_scale%r.
proof.
rewrite /omega8 creal_chalf_neg /chalf_re /omega4
        /creal /cneg /ci /=.
apply sqrt_between.
+ rewrite /certificate_scale; smt().
+ rewrite /certificate_scale; smt().
+ smt().
+ rewrite /certificate_scale; smt().
+ rewrite /certificate_scale; smt().
qed.

lemma omega16_re_interval :
  923879532511286756%r / certificate_scale%r <= creal omega16 /\
  creal omega16 <= 923879532511286757%r / certificate_scale%r.
proof.
rewrite /omega16 creal_chalf_neg /chalf_re.
have [hlo hhi] := omega8_re_interval.
apply sqrt_between.
+ rewrite /certificate_scale; smt().
+ rewrite /certificate_scale; smt().
+ smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
qed.

lemma omega32_re_interval :
  980785280403230449%r / certificate_scale%r <= creal omega32 /\
  creal omega32 <= 980785280403230450%r / certificate_scale%r.
proof.
rewrite /omega32 creal_chalf_neg /chalf_re.
have [hlo hhi] := omega16_re_interval.
apply sqrt_between.
+ rewrite /certificate_scale; smt().
+ rewrite /certificate_scale; smt().
+ smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
qed.

lemma omega64_re_interval :
  995184726672196886%r / certificate_scale%r <= creal omega64 /\
  creal omega64 <= 995184726672196887%r / certificate_scale%r.
proof.
rewrite /omega64 creal_chalf_neg /chalf_re.
have [hlo hhi] := omega32_re_interval.
apply sqrt_between.
+ rewrite /certificate_scale; smt().
+ rewrite /certificate_scale; smt().
+ smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
qed.

lemma omega128_re_interval :
  998795456205172392%r / certificate_scale%r <= creal omega128 /\
  creal omega128 <= 998795456205172393%r / certificate_scale%r.
proof.
rewrite /omega128 creal_chalf_neg /chalf_re.
have [hlo hhi] := omega64_re_interval.
apply sqrt_between.
+ rewrite /certificate_scale; smt().
+ rewrite /certificate_scale; smt().
+ smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
qed.

lemma omega256_re_interval :
  999698818696204219%r / certificate_scale%r <= creal omega256 /\
  creal omega256 <= 999698818696204221%r / certificate_scale%r.
proof.
rewrite /omega256 creal_chalf_neg /chalf_re.
have [hlo hhi] := omega128_re_interval.
apply sqrt_between.
+ rewrite /certificate_scale; smt().
+ rewrite /certificate_scale; smt().
+ smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
qed.

lemma omega512_re_interval :
  999924701839144540%r / certificate_scale%r <= creal omega512 /\
  creal omega512 <= 999924701839144542%r / certificate_scale%r.
proof.
rewrite /omega512 creal_chalf_neg /chalf_re.
have [hlo hhi] := omega256_re_interval.
apply sqrt_between.
+ rewrite /certificate_scale; smt().
+ rewrite /certificate_scale; smt().
+ smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
+ rewrite /certificate_scale in hlo.
  rewrite /certificate_scale in hhi.
  rewrite /certificate_scale; smt().
qed.

lemma omega512_im_interval :
  (-12271538285719949)%r / certificate_scale%r <= cimag omega512 /\
  cimag omega512 <= (-12271538285719908)%r / certificate_scale%r.
proof.
rewrite /omega512 cimag_chalf_neg /chalf_im.
have [hlo hhi] := omega256_re_interval.
have hs :
  12271538285719908%r / certificate_scale%r <=
    sqrt ((1%r - creal omega256) / 2%r) /\
  sqrt ((1%r - creal omega256) / 2%r) <=
    12271538285719949%r / certificate_scale%r.
+ apply sqrt_between.
  - rewrite /certificate_scale; smt().
  - rewrite /certificate_scale; smt().
  - rewrite /certificate_scale in hlo.
    rewrite /certificate_scale in hhi.
    rewrite /certificate_scale; smt().
  - rewrite /certificate_scale in hlo.
    rewrite /certificate_scale in hhi.
    rewrite /certificate_scale; smt().
  - rewrite /certificate_scale in hlo.
    rewrite /certificate_scale in hhi.
    rewrite /certificate_scale; smt().
rewrite /certificate_scale in hs.
rewrite /certificate_scale.
smt().
qed.

end KeygenM23RootGeneratorCertificate.
