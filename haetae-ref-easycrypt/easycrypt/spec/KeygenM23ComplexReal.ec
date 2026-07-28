require import AllCore Ring StdOrder Real RealExp.

import RField RealOrder.

theory KeygenM23ComplexReal.

(* A deliberately small complex-number surface.  Keeping the representation
   transparent makes later DFT statements reduce to the installed real
   theory instead of introducing a second, axiomatized number system. *)
type complex = real * real.

op creal (z : complex) : real = z.`1.
op cimag (z : complex) : real = z.`2.

op czero : complex = (0%r, 0%r).
op cone  : complex = (1%r, 0%r).
op ci    : complex = (0%r, 1%r).

op cof_real (x : real) : complex = (x, 0%r).
op cof_int (n : int) : complex = cof_real n%r.

op cadd (z w : complex) : complex =
  (creal z + creal w, cimag z + cimag w).

op cneg (z : complex) : complex =
  (- creal z, - cimag z).

op csub (z w : complex) : complex =
  cadd z (cneg w).

op cmul (z w : complex) : complex =
  (creal z * creal w - cimag z * cimag w,
   creal z * cimag w + cimag z * creal w).

op cconj (z : complex) : complex =
  (creal z, - cimag z).

op cnorm2 (z : complex) : real =
  creal z * creal z + cimag z * cimag z.

op cscale (a : real) (z : complex) : complex =
  (a * creal z, a * cimag z).

op cscale_int (n : int) (z : complex) : complex =
  cscale n%r z.

(* Coordinatewise error is sufficient for the fixed-point FFT: each
   butterfly can propagate separate real and imaginary error bounds. *)
op cclose (eps : real) (z w : complex) : bool =
  `|creal z - creal w| <= eps /\
  `|cimag z - cimag w| <= eps.

lemma complex_ext (z w : complex) :
  creal z = creal w =>
  cimag z = cimag w =>
  z = w.
proof.
move: z w => [zr zi] [wr wi].
rewrite /creal /cimag /=.
by move=> -> ->.
qed.

lemma complex_eta (z : complex) :
  z = (creal z, cimag z).
proof. by move: z => [zr zi]. qed.

lemma creal_zero : creal czero = 0%r by done.
lemma cimag_zero : cimag czero = 0%r by done.
lemma creal_one : creal cone = 1%r by done.
lemma cimag_one : cimag cone = 0%r by done.
lemma creal_i : creal ci = 0%r by done.
lemma cimag_i : cimag ci = 1%r by done.

lemma creal_of_real (x : real) : creal (cof_real x) = x by done.
lemma cimag_of_real (x : real) : cimag (cof_real x) = 0%r by done.
lemma creal_of_int (n : int) : creal (cof_int n) = n%r by done.
lemma cimag_of_int (n : int) : cimag (cof_int n) = 0%r by done.

lemma creal_add (z w : complex) :
  creal (cadd z w) = creal z + creal w by done.

lemma cimag_add (z w : complex) :
  cimag (cadd z w) = cimag z + cimag w by done.

lemma creal_neg (z : complex) :
  creal (cneg z) = - creal z by done.

lemma cimag_neg (z : complex) :
  cimag (cneg z) = - cimag z by done.

lemma creal_sub (z w : complex) :
  creal (csub z w) = creal z - creal w by done.

lemma cimag_sub (z w : complex) :
  cimag (csub z w) = cimag z - cimag w by done.

lemma creal_mul (z w : complex) :
  creal (cmul z w) =
    creal z * creal w - cimag z * cimag w by done.

lemma cimag_mul (z w : complex) :
  cimag (cmul z w) =
    creal z * cimag w + cimag z * creal w by done.

lemma creal_conj (z : complex) :
  creal (cconj z) = creal z by done.

lemma cimag_conj (z : complex) :
  cimag (cconj z) = - cimag z by done.

lemma creal_scale (a : real) (z : complex) :
  creal (cscale a z) = a * creal z by done.

lemma cimag_scale (a : real) (z : complex) :
  cimag (cscale a z) = a * cimag z by done.

lemma caddA (x y z : complex) :
  cadd (cadd x y) z = cadd x (cadd y z).
proof.
apply complex_ext.
+ rewrite !creal_add.
  ring.
+ rewrite !cimag_add.
  ring.
qed.

lemma caddC (x y : complex) :
  cadd x y = cadd y x.
proof.
apply complex_ext.
+ rewrite !creal_add.
  ring.
+ rewrite !cimag_add.
  ring.
qed.

lemma cadd0 (z : complex) :
  cadd czero z = z.
proof.
apply complex_ext.
+ rewrite creal_add creal_zero.
  ring.
+ rewrite cimag_add cimag_zero.
  ring.
qed.

lemma cadd0r (z : complex) :
  cadd z czero = z.
proof. by rewrite caddC cadd0. qed.

lemma caddN (z : complex) :
  cadd (cneg z) z = czero.
proof.
apply complex_ext.
+ rewrite creal_add creal_neg creal_zero.
  ring.
+ rewrite cimag_add cimag_neg cimag_zero.
  ring.
qed.

lemma caddNr (z : complex) :
  cadd z (cneg z) = czero.
proof. by rewrite caddC caddN. qed.

lemma cnegK (z : complex) :
  cneg (cneg z) = z.
proof.
apply complex_ext.
+ rewrite !creal_neg.
  ring.
+ rewrite !cimag_neg.
  ring.
qed.

lemma cneg0 :
  cneg czero = czero.
proof. by rewrite /cneg /czero /creal /cimag /=. qed.

lemma cneg_add (z w : complex) :
  cneg (cadd z w) = cadd (cneg z) (cneg w).
proof.
apply complex_ext.
+ rewrite creal_neg !creal_add !creal_neg.
  ring.
+ rewrite cimag_neg !cimag_add !cimag_neg.
  ring.
qed.

lemma csub_self (z : complex) :
  csub z z = czero.
proof. by rewrite /csub caddNr. qed.

lemma csub_zero (z : complex) :
  csub z czero = z.
proof. by rewrite /csub cneg0 cadd0r. qed.

lemma cmulA (x y z : complex) :
  cmul (cmul x y) z = cmul x (cmul y z).
proof.
apply complex_ext.
+ rewrite !creal_mul !cimag_mul.
  ring.
+ rewrite !cimag_mul !creal_mul.
  ring.
qed.

lemma cmulC (x y : complex) :
  cmul x y = cmul y x.
proof.
apply complex_ext.
+ rewrite !creal_mul.
  ring.
+ rewrite !cimag_mul.
  ring.
qed.

lemma cmul1 (z : complex) :
  cmul cone z = z.
proof.
apply complex_ext.
+ rewrite creal_mul creal_one cimag_one.
  ring.
+ rewrite cimag_mul creal_one cimag_one.
  ring.
qed.

lemma cmul1r (z : complex) :
  cmul z cone = z.
proof. by rewrite cmulC cmul1. qed.

lemma cmul0 (z : complex) :
  cmul czero z = czero.
proof.
apply complex_ext.
+ rewrite creal_mul creal_zero cimag_zero.
  ring.
+ rewrite cimag_mul creal_zero cimag_zero.
  ring.
qed.

lemma cmul0r (z : complex) :
  cmul z czero = czero.
proof. by rewrite cmulC cmul0. qed.

lemma cmul_add (x y z : complex) :
  cmul x (cadd y z) = cadd (cmul x y) (cmul x z).
proof.
apply complex_ext.
+ rewrite creal_mul !creal_add !cimag_add
           !creal_mul.
  ring.
+ rewrite cimag_mul !creal_add !cimag_add
           !cimag_mul.
  ring.
qed.

lemma cmul_addl (x y z : complex) :
  cmul (cadd x y) z = cadd (cmul x z) (cmul y z).
proof. by rewrite cmulC cmul_add !(@cmulC z). qed.

lemma cmul_neg (z w : complex) :
  cmul z (cneg w) = cneg (cmul z w).
proof.
apply complex_ext.
+ rewrite /cmul /cneg /creal /cimag /=.
  ring.
+ rewrite /cmul /cneg /creal /cimag /=.
  ring.
qed.

lemma cmul_negl (z w : complex) :
  cmul (cneg z) w = cneg (cmul z w).
proof. by rewrite cmulC cmul_neg cmulC. qed.

lemma ci_square :
  cmul ci ci = cneg cone.
proof. by rewrite /cmul /ci /cone /cneg /creal /cimag /=. qed.

lemma cof_real_zero :
  cof_real 0%r = czero by done.

lemma cof_real_one :
  cof_real 1%r = cone by done.

lemma cof_real_add (x y : real) :
  cof_real (x + y) = cadd (cof_real x) (cof_real y).
proof.
apply complex_ext.
+ rewrite creal_of_real creal_add !creal_of_real.
  ring.
+ rewrite cimag_of_real cimag_add !cimag_of_real.
  ring.
qed.

lemma cof_real_neg (x : real) :
  cof_real (-x) = cneg (cof_real x).
proof.
apply complex_ext.
+ rewrite creal_of_real creal_neg creal_of_real.
  ring.
+ rewrite cimag_of_real cimag_neg cimag_of_real.
  ring.
qed.

lemma cof_real_mul (x y : real) :
  cof_real (x * y) = cmul (cof_real x) (cof_real y).
proof.
apply complex_ext.
+ rewrite creal_of_real creal_mul !creal_of_real !cimag_of_real.
  ring.
+ rewrite cimag_of_real cimag_mul !creal_of_real !cimag_of_real.
  ring.
qed.

lemma cmul_of_real (a : real) (z : complex) :
  cmul (cof_real a) z = cscale a z.
proof.
apply complex_ext.
+ rewrite creal_mul creal_of_real cimag_of_real creal_scale.
  ring.
+ rewrite cimag_mul creal_of_real cimag_of_real cimag_scale.
  ring.
qed.

lemma cscale0 (z : complex) :
  cscale 0%r z = czero.
proof.
apply complex_ext.
+ rewrite creal_scale creal_zero.
  ring.
+ rewrite cimag_scale cimag_zero.
  ring.
qed.

lemma cscale1 (z : complex) :
  cscale 1%r z = z.
proof.
apply complex_ext.
+ rewrite creal_scale.
  ring.
+ rewrite cimag_scale.
  ring.
qed.

lemma cscaleA (a b : real) (z : complex) :
  cscale a (cscale b z) = cscale (a * b) z.
proof.
apply complex_ext.
+ rewrite !creal_scale.
  ring.
+ rewrite !cimag_scale.
  ring.
qed.

lemma cscale_add (a : real) (z w : complex) :
  cscale a (cadd z w) = cadd (cscale a z) (cscale a w).
proof.
apply complex_ext.
+ rewrite creal_scale !creal_add !creal_scale.
  ring.
+ rewrite cimag_scale !cimag_add !cimag_scale.
  ring.
qed.

lemma cscale_add_scalar (a b : real) (z : complex) :
  cscale (a + b) z = cadd (cscale a z) (cscale b z).
proof.
apply complex_ext;
rewrite /cscale /cadd /creal /cimag /=;
ring.
qed.

lemma cscale_mul (a : real) (z w : complex) :
  cscale a (cmul z w) = cmul (cscale a z) w.
proof.
apply complex_ext;
rewrite /cscale /cmul /creal /cimag /=;
ring.
qed.

lemma cconjK (z : complex) :
  cconj (cconj z) = z.
proof.
apply complex_ext.
+ rewrite !creal_conj.
  done.
+ rewrite !cimag_conj.
  ring.
qed.

lemma cconj_zero :
  cconj czero = czero by done.

lemma cconj_one :
  cconj cone = cone by done.

lemma cconj_add (z w : complex) :
  cconj (cadd z w) = cadd (cconj z) (cconj w).
proof.
apply complex_ext.
+ rewrite creal_conj !creal_add !creal_conj.
  done.
+ rewrite cimag_conj !cimag_add !cimag_conj.
  ring.
qed.

lemma cconj_neg (z : complex) :
  cconj (cneg z) = cneg (cconj z).
proof.
apply complex_ext.
+ rewrite creal_conj !creal_neg creal_conj.
  done.
+ rewrite cimag_conj !cimag_neg cimag_conj.
  ring.
qed.

lemma cconj_mul (z w : complex) :
  cconj (cmul z w) = cmul (cconj z) (cconj w).
proof.
apply complex_ext.
+ rewrite creal_conj !creal_mul !creal_conj !cimag_conj.
  ring.
+ rewrite cimag_conj !cimag_mul !creal_conj !cimag_conj.
  ring.
qed.

lemma cmul_conj (z : complex) :
  cmul z (cconj z) = cof_real (cnorm2 z).
proof.
apply complex_ext.
+ rewrite creal_mul creal_conj cimag_conj creal_of_real /cnorm2.
  ring.
+ rewrite cimag_mul creal_conj cimag_conj cimag_of_real.
  ring.
qed.

lemma cnorm2_zero :
  cnorm2 czero = 0%r.
proof. by rewrite /cnorm2 /czero /creal /cimag /=. qed.

lemma cnorm2_one :
  cnorm2 cone = 1%r.
proof. by rewrite /cnorm2 /cone /creal /cimag /=. qed.

lemma cnorm2_i :
  cnorm2 ci = 1%r.
proof. by rewrite /cnorm2 /ci /creal /cimag /=. qed.

lemma cnorm2_ge0 (z : complex) :
  0%r <= cnorm2 z.
proof.
move: z => [zr zi].
rewrite /cnorm2 /creal /cimag /=.
have hr : 0%r <= zr ^ 2 by apply ge0_sqr.
have hi : 0%r <= zi ^ 2 by apply ge0_sqr.
rewrite expr2 in hr.
rewrite expr2 in hi.
by smt().
qed.

lemma cnorm2_eq0 (z : complex) :
  cnorm2 z = 0%r <=> z = czero.
proof.
move: z => [zr zi].
rewrite /cnorm2 /czero /creal /cimag /=.
have hr : 0%r <= zr * zr.
+ rewrite -expr2.
  apply ge0_sqr.
have hi : 0%r <= zi * zi.
+ rewrite -expr2.
  apply ge0_sqr.
split.
+ move=> hsum.
  have hzr2 : zr * zr = 0%r by smt().
  have hzi2 : zi * zi = 0%r by smt().
  rewrite mulf_eq0 in hzr2.
  rewrite mulf_eq0 in hzi2.
  by case: hzr2 => ->; case: hzi2 => ->.
+ move=> [-> ->].
  ring.
qed.

lemma cnorm2_conj (z : complex) :
  cnorm2 (cconj z) = cnorm2 z.
proof.
by move: z => [zr zi];
   rewrite /cnorm2 /cconj /creal /cimag /=; ring.
qed.

lemma cnorm2_mul (z w : complex) :
  cnorm2 (cmul z w) = cnorm2 z * cnorm2 w.
proof.
by move: z w => [zr zi] [wr wi];
   rewrite /cnorm2 /cmul /creal /cimag /=; ring.
qed.

lemma cnorm2_scale (a : real) (z : complex) :
  cnorm2 (cscale a z) = (a * a) * cnorm2 z.
proof.
by move: z => [zr zi];
   rewrite /cnorm2 /cscale /creal /cimag /=; ring.
qed.

lemma cclose_ge0 (eps : real) (z w : complex) :
  cclose eps z w => 0%r <= eps.
proof.
rewrite /cclose.
move=> [h _].
have h0 : 0%r <= `|creal z - creal w| by
  apply RealOrder.normr_ge0.
by smt().
qed.

lemma cclose_refl (eps : real) (z : complex) :
  0%r <= eps =>
  cclose eps z z.
proof.
by move=> heps; rewrite /cclose !subrr !normr0.
qed.

lemma cclose_sym (eps : real) (z w : complex) :
  cclose eps z w =>
  cclose eps w z.
proof.
move: z w => [zr zi] [wr wi].
rewrite /cclose /creal /cimag /=.
have hr : wr - zr = -(zr - wr) by ring.
have hi : wi - zi = -(zi - wi) by ring.
by rewrite hr hi !normrN.
qed.

lemma cclose_triangle (eps1 eps2 : real) (x y z : complex) :
  cclose eps1 x y =>
  cclose eps2 y z =>
  cclose (eps1 + eps2) x z.
proof.
move=> hxy hyz.
rewrite /cclose in hxy.
rewrite /cclose in hyz.
rewrite /cclose.
have hr := ler_dist_add (creal y) (creal x) (creal z).
have hi := ler_dist_add (cimag y) (cimag x) (cimag z).
by smt().
qed.

lemma cclose_neg (eps : real) (z w : complex) :
  cclose eps z w =>
  cclose eps (cneg z) (cneg w).
proof.
move: z w => [zr zi] [wr wi].
rewrite /cclose /cneg /creal /cimag /=.
have hr : -zr - -wr = -(zr - wr) by ring.
have hi : -zi - -wi = -(zi - wi) by ring.
by rewrite hr hi !normrN.
qed.

lemma cclose_add
    (eps1 eps2 : real) (x x' y y' : complex) :
  cclose eps1 x x' =>
  cclose eps2 y y' =>
  cclose (eps1 + eps2) (cadd x y) (cadd x' y').
proof.
move=> hx hy.
rewrite /cclose in hx.
rewrite /cclose in hy.
rewrite /cclose.
rewrite !creal_add !cimag_add.
have hr :
  creal x + creal y - (creal x' + creal y') =
  (creal x - creal x') + (creal y - creal y') by ring.
have hi :
  cimag x + cimag y - (cimag x' + cimag y') =
  (cimag x - cimag x') + (cimag y - cimag y') by ring.
rewrite hr hi.
have hnr :=
  ler_norm_add (creal x - creal x') (creal y - creal y').
have hni :=
  ler_norm_add (cimag x - cimag x') (cimag y - cimag y').
by smt().
qed.

lemma cclose_sub
    (eps1 eps2 : real) (x x' y y' : complex) :
  cclose eps1 x x' =>
  cclose eps2 y y' =>
  cclose (eps1 + eps2) (csub x y) (csub x' y').
proof.
move=> hx hy.
rewrite /csub.
exact (cclose_add eps1 eps2 x x' (cneg y) (cneg y')
         hx (cclose_neg eps2 y y' hy)).
qed.

lemma cclose_scale (a eps : real) (z w : complex) :
  cclose eps z w =>
  cclose (`|a| * eps) (cscale a z) (cscale a w).
proof.
move=> h.
rewrite /cclose in h.
move: h => [hre him].
rewrite /cclose.
rewrite !creal_scale !cimag_scale.
have hr : a * creal z - a * creal w =
  a * (creal z - creal w) by ring.
have hi : a * cimag z - a * cimag w =
  a * (cimag z - cimag w) by ring.
rewrite hr hi !normrM.
split.
+ apply ler_wpmul2l.
  + apply RealOrder.normr_ge0.
  + exact hre.
+ apply ler_wpmul2l.
  + apply RealOrder.normr_ge0.
  + exact him.
qed.

lemma cclose_of_real (eps : real) (x y : real) :
  `|x - y| <= eps =>
  cclose eps (cof_real x) (cof_real y).
proof.
move=> h.
rewrite /cclose /cof_real /creal /cimag /=.
split.
+ exact h.
+ have h0 : 0%r <= `|x - y| by
    apply RealOrder.normr_ge0.
  by smt().
qed.

end KeygenM23ComplexReal.
