require import AllCore IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal KeygenM23IdealRootDFT.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentClassSensitiveProfilePostFreeze.
import Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalKernelPostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalClassProfilePostFreeze.

(* This file lifts the exact class-sensitive scalar FFT moment recurrence into
   the certified center-radius interval kernel. It assumes certified real or
   imaginary root-component balls, but provides no concrete numerical root
   table and makes no fixed-point FFT, random-context, or security-level
   claim. *)

op root_interval_certificate
    (root : int -> real) (balls : int -> rinterval) (n : int) : bool =
  forall j, 0 <= j < n =>
    interval_valid (balls j) /\ interval_holds (balls j) (root j).

op interval_scale_mul (c : real) (qa qb : rinterval) : rinterval =
  interval_mul (interval_point c) (interval_mul qa qb).

op interval_add3 (q1 q2 q3 : rinterval) : rinterval =
  interval_add (interval_add q1 q2) q3.

op interval_add4 (q1 q2 q3 q4 : rinterval) : rinterval =
  interval_add (interval_add3 q1 q2 q3) q4.

op interval_add6 (q1 q2 q3 q4 q5 q6 : rinterval) : rinterval =
  interval_add (interval_add4 q1 q2 q3 q4) (interval_add q5 q6).

op root_class_moment2_term
    (trace : int -> int) (root : int -> real) (j : int) : real =
  root j ^ 2 * ideal_final_s2_class_moment2_oracle (trace j).

op root_class_moment3_term
    (trace : int -> int) (root : int -> real) (j : int) : real =
  root j ^ 3 * ideal_final_s2_class_moment3_oracle (trace j).

op root_class_moment4_term
    (trace : int -> int) (root : int -> real) (j : int) : real =
  root j ^ 4 * ideal_final_s2_class_moment4_oracle (trace j).

op root_class_moment5_term
    (trace : int -> int) (root : int -> real) (j : int) : real =
  root j ^ 5 * ideal_final_s2_class_moment5_oracle (trace j).

op root_class_moment6_term
    (trace : int -> int) (root : int -> real) (j : int) : real =
  root j ^ 6 * ideal_final_s2_class_moment6_oracle (trace j).

op root_class_moment8_term
    (trace : int -> int) (root : int -> real) (j : int) : real =
  root j ^ 8 * ideal_final_s2_class_moment8_oracle (trace j).

op class_moment2_point_interval (trace : int -> int) (j : int) : rinterval =
  interval_point (ideal_final_s2_class_moment2_oracle (trace j)).

op class_moment3_point_interval (trace : int -> int) (j : int) : rinterval =
  interval_point (ideal_final_s2_class_moment3_oracle (trace j)).

op class_moment4_point_interval (trace : int -> int) (j : int) : rinterval =
  interval_point (ideal_final_s2_class_moment4_oracle (trace j)).

op class_moment5_point_interval (trace : int -> int) (j : int) : rinterval =
  interval_point (ideal_final_s2_class_moment5_oracle (trace j)).

op class_moment6_point_interval (trace : int -> int) (j : int) : rinterval =
  interval_point (ideal_final_s2_class_moment6_oracle (trace j)).

op class_moment8_point_interval (trace : int -> int) (j : int) : rinterval =
  interval_point (ideal_final_s2_class_moment8_oracle (trace j)).

op root_class_moment2_interval
    (trace : int -> int) (balls : int -> rinterval) (j : int) : rinterval =
  interval_mul
    (interval_pow2 (balls j))
    (class_moment2_point_interval trace j).

op root_class_moment3_interval
    (trace : int -> int) (balls : int -> rinterval) (j : int) : rinterval =
  interval_mul
    (interval_pow3 (balls j))
    (class_moment3_point_interval trace j).

op root_class_moment4_interval
    (trace : int -> int) (balls : int -> rinterval) (j : int) : rinterval =
  interval_mul
    (interval_pow4 (balls j))
    (class_moment4_point_interval trace j).

op root_class_moment5_interval
    (trace : int -> int) (balls : int -> rinterval) (j : int) : rinterval =
  interval_mul
    (interval_pow5 (balls j))
    (class_moment5_point_interval trace j).

op root_class_moment6_interval
    (trace : int -> int) (balls : int -> rinterval) (j : int) : rinterval =
  interval_mul
    (interval_pow6 (balls j))
    (class_moment6_point_interval trace j).

op root_class_moment8_interval
    (trace : int -> int) (balls : int -> rinterval) (j : int) : rinterval =
  interval_mul
    (interval_pow8 (balls j))
    (class_moment8_point_interval trace j).

op root_class_profile2
    (trace : int -> int) (root : int -> real) (n : int) : real =
  BRA.bigi predT (fun j => root_class_moment2_term trace root j) 0 n.

op root_class_profile3
    (trace : int -> int) (root : int -> real) (n : int) : real =
  BRA.bigi predT (fun j => root_class_moment3_term trace root j) 0 n.

op root_class_profile4_step
    (trace : int -> int) (root : int -> real) (j : int) : real =
  6%r * root_class_profile2 trace root j *
    root_class_moment2_term trace root j +
  root_class_moment4_term trace root j.

op root_class_profile4
    (trace : int -> int) (root : int -> real) (n : int) : real =
  BRA.bigi predT (fun j => root_class_profile4_step trace root j) 0 n.

op root_class_profile5_step
    (trace : int -> int) (root : int -> real) (j : int) : real =
  10%r * root_class_profile3 trace root j *
    root_class_moment2_term trace root j +
  10%r * root_class_profile2 trace root j *
    root_class_moment3_term trace root j +
  root_class_moment5_term trace root j.

op root_class_profile5
    (trace : int -> int) (root : int -> real) (n : int) : real =
  BRA.bigi predT (fun j => root_class_profile5_step trace root j) 0 n.

op root_class_profile6_step
    (trace : int -> int) (root : int -> real) (j : int) : real =
  15%r * root_class_profile4 trace root j *
    root_class_moment2_term trace root j +
  20%r * root_class_profile3 trace root j *
    root_class_moment3_term trace root j +
  15%r * root_class_profile2 trace root j *
    root_class_moment4_term trace root j +
  root_class_moment6_term trace root j.

op root_class_profile6
    (trace : int -> int) (root : int -> real) (n : int) : real =
  BRA.bigi predT (fun j => root_class_profile6_step trace root j) 0 n.

op root_class_profile8_step
    (trace : int -> int) (root : int -> real) (j : int) : real =
  28%r * root_class_profile6 trace root j *
    root_class_moment2_term trace root j +
  56%r * root_class_profile5 trace root j *
    root_class_moment3_term trace root j +
  70%r * root_class_profile4 trace root j *
    root_class_moment4_term trace root j +
  56%r * root_class_profile3 trace root j *
    root_class_moment5_term trace root j +
  28%r * root_class_profile2 trace root j *
    root_class_moment6_term trace root j +
  root_class_moment8_term trace root j.

op root_class_profile8
    (trace : int -> int) (root : int -> real) (n : int) : real =
  BRA.bigi predT (fun j => root_class_profile8_step trace root j) 0 n.

op root_class_profile2_interval
    (trace : int -> int) (balls : int -> rinterval) (n : int) : rinterval =
  interval_bigi (fun j => root_class_moment2_interval trace balls j) n.

op root_class_profile3_interval
    (trace : int -> int) (balls : int -> rinterval) (n : int) : rinterval =
  interval_bigi (fun j => root_class_moment3_interval trace balls j) n.

op root_class_profile4_interval_step
    (trace : int -> int) (balls : int -> rinterval) (j : int) : rinterval =
  interval_add
    (interval_scale_mul 6%r
      (root_class_profile2_interval trace balls j)
      (root_class_moment2_interval trace balls j))
    (root_class_moment4_interval trace balls j).

op root_class_profile4_interval
    (trace : int -> int) (balls : int -> rinterval) (n : int) : rinterval =
  interval_bigi (fun j => root_class_profile4_interval_step trace balls j) n.

op root_class_profile5_interval_step
    (trace : int -> int) (balls : int -> rinterval) (j : int) : rinterval =
  interval_add3
    (interval_scale_mul 10%r
      (root_class_profile3_interval trace balls j)
      (root_class_moment2_interval trace balls j))
    (interval_scale_mul 10%r
      (root_class_profile2_interval trace balls j)
      (root_class_moment3_interval trace balls j))
    (root_class_moment5_interval trace balls j).

op root_class_profile5_interval
    (trace : int -> int) (balls : int -> rinterval) (n : int) : rinterval =
  interval_bigi (fun j => root_class_profile5_interval_step trace balls j) n.

op root_class_profile6_interval_step
    (trace : int -> int) (balls : int -> rinterval) (j : int) : rinterval =
  interval_add4
    (interval_scale_mul 15%r
      (root_class_profile4_interval trace balls j)
      (root_class_moment2_interval trace balls j))
    (interval_scale_mul 20%r
      (root_class_profile3_interval trace balls j)
      (root_class_moment3_interval trace balls j))
    (interval_scale_mul 15%r
      (root_class_profile2_interval trace balls j)
      (root_class_moment4_interval trace balls j))
    (root_class_moment6_interval trace balls j).

op root_class_profile6_interval
    (trace : int -> int) (balls : int -> rinterval) (n : int) : rinterval =
  interval_bigi (fun j => root_class_profile6_interval_step trace balls j) n.

op root_class_profile8_interval_step
    (trace : int -> int) (balls : int -> rinterval) (j : int) : rinterval =
  interval_add6
    (interval_scale_mul 28%r
      (root_class_profile6_interval trace balls j)
      (root_class_moment2_interval trace balls j))
    (interval_scale_mul 56%r
      (root_class_profile5_interval trace balls j)
      (root_class_moment3_interval trace balls j))
    (interval_scale_mul 70%r
      (root_class_profile4_interval trace balls j)
      (root_class_moment4_interval trace balls j))
    (interval_scale_mul 56%r
      (root_class_profile3_interval trace balls j)
      (root_class_moment5_interval trace balls j))
    (interval_scale_mul 28%r
      (root_class_profile2_interval trace balls j)
      (root_class_moment6_interval trace balls j))
    (root_class_moment8_interval trace balls j).

op root_class_profile8_interval
    (trace : int -> int) (balls : int -> rinterval) (n : int) : rinterval =
  interval_bigi (fun j => root_class_profile8_interval_step trace balls j) n.

lemma root_interval_certificate_at root balls n j :
  root_interval_certificate root balls n =>
  0 <= j < n =>
  interval_valid (balls j) /\ interval_holds (balls j) (root j).
proof.
rewrite /root_interval_certificate.
move=> hcert hj.
exact (hcert j hj).
qed.

lemma root_interval_certificate_prefix root balls n m :
  root_interval_certificate root balls n =>
  0 <= m <= n =>
  root_interval_certificate root balls m.
proof.
rewrite /root_interval_certificate.
move=> hcert [hm0 hmn] j [hj0 hjm].
have hj : 0 <= j < n by smt().
exact (hcert j hj).
qed.

lemma interval_scale_mul_valid c qa qb :
  interval_valid qa =>
  interval_valid qb =>
  interval_valid (interval_scale_mul c qa qb).
proof.
move=> hva hvb.
rewrite /interval_scale_mul.
apply interval_mul_valid.
+ exact (interval_point_valid c).
exact (interval_mul_valid qa qb hva hvb).
qed.

lemma interval_scale_mul_holds c qa qb x y :
  interval_valid qa =>
  interval_valid qb =>
  interval_holds qa x =>
  interval_holds qb y =>
  interval_holds (interval_scale_mul c qa qb) (c * x * y).
proof.
move=> hva hvb hxa hyb.
rewrite /interval_scale_mul.
have hvab := interval_mul_valid qa qb hva hvb.
have hab := interval_mul_holds qa qb x y hva hvb hxa hyb.
have hc :=
  interval_mul_holds
    (interval_point c) (interval_mul qa qb) c (x * y)
    (interval_point_valid c) hvab (interval_point_holds c) hab.
have -> : c * x * y = c * (x * y) by ring.
exact hc.
qed.

lemma interval_add3_valid q1 q2 q3 :
  interval_valid q1 => interval_valid q2 => interval_valid q3 =>
  interval_valid (interval_add3 q1 q2 q3).
proof.
move=> h1 h2 h3.
rewrite /interval_add3.
exact (interval_add_valid (interval_add q1 q2) q3
  (interval_add_valid q1 q2 h1 h2) h3).
qed.

lemma interval_add3_holds q1 q2 q3 x1 x2 x3 :
  interval_holds q1 x1 =>
  interval_holds q2 x2 =>
  interval_holds q3 x3 =>
  interval_holds (interval_add3 q1 q2 q3) (x1 + x2 + x3).
proof.
move=> h1 h2 h3.
rewrite /interval_add3.
exact (interval_add_holds (interval_add q1 q2) q3
  (x1 + x2) x3 (interval_add_holds q1 q2 x1 x2 h1 h2) h3).
qed.

lemma interval_add4_valid q1 q2 q3 q4 :
  interval_valid q1 => interval_valid q2 =>
  interval_valid q3 => interval_valid q4 =>
  interval_valid (interval_add4 q1 q2 q3 q4).
proof.
move=> h1 h2 h3 h4.
rewrite /interval_add4.
exact (interval_add_valid (interval_add3 q1 q2 q3) q4
  (interval_add3_valid q1 q2 q3 h1 h2 h3) h4).
qed.

lemma interval_add4_holds q1 q2 q3 q4 x1 x2 x3 x4 :
  interval_holds q1 x1 => interval_holds q2 x2 =>
  interval_holds q3 x3 => interval_holds q4 x4 =>
  interval_holds (interval_add4 q1 q2 q3 q4) (x1 + x2 + x3 + x4).
proof.
move=> h1 h2 h3 h4.
rewrite /interval_add4.
exact (interval_add_holds (interval_add3 q1 q2 q3) q4
  (x1 + x2 + x3) x4
  (interval_add3_holds q1 q2 q3 x1 x2 x3 h1 h2 h3) h4).
qed.

lemma interval_add6_valid q1 q2 q3 q4 q5 q6 :
  interval_valid q1 => interval_valid q2 => interval_valid q3 =>
  interval_valid q4 => interval_valid q5 => interval_valid q6 =>
  interval_valid (interval_add6 q1 q2 q3 q4 q5 q6).
proof.
move=> h1 h2 h3 h4 h5 h6.
rewrite /interval_add6.
exact (interval_add_valid
  (interval_add4 q1 q2 q3 q4) (interval_add q5 q6)
  (interval_add4_valid q1 q2 q3 q4 h1 h2 h3 h4)
  (interval_add_valid q5 q6 h5 h6)).
qed.

lemma interval_add6_holds q1 q2 q3 q4 q5 q6 x1 x2 x3 x4 x5 x6 :
  interval_holds q1 x1 => interval_holds q2 x2 =>
  interval_holds q3 x3 => interval_holds q4 x4 =>
  interval_holds q5 x5 => interval_holds q6 x6 =>
  interval_holds (interval_add6 q1 q2 q3 q4 q5 q6)
    (x1 + x2 + x3 + x4 + x5 + x6).
proof.
move=> h1 h2 h3 h4 h5 h6.
rewrite /interval_add6.
have hleft := interval_add4_holds q1 q2 q3 q4 x1 x2 x3 x4
  h1 h2 h3 h4.
have hright := interval_add_holds q5 q6 x5 x6 h5 h6.
have hsum := interval_add_holds
  (interval_add4 q1 q2 q3 q4) (interval_add q5 q6)
  (x1 + x2 + x3 + x4) (x5 + x6) hleft hright.
have -> : x1 + x2 + x3 + x4 + x5 + x6 =
    (x1 + x2 + x3 + x4) + (x5 + x6) by ring.
exact hsum.
qed.

lemma root_class_moment2_interval_sound trace root balls n j :
  root_interval_certificate root balls n =>
  0 <= j < n =>
  interval_valid (root_class_moment2_interval trace balls j) /\
  interval_holds (root_class_moment2_interval trace balls j)
    (root_class_moment2_term trace root j).
proof.
move=> hcert hj.
have [hv hx] := root_interval_certificate_at root balls n j hcert hj.
rewrite /root_class_moment2_interval /root_class_moment2_term
        /class_moment2_point_interval.
split.
+ exact (interval_mul_valid
    (interval_pow2 (balls j))
    (interval_point (ideal_final_s2_class_moment2_oracle (trace j)))
    (interval_pow2_valid (balls j) hv)
    (interval_point_valid _)).
exact (interval_mul_holds
  (interval_pow2 (balls j))
  (interval_point (ideal_final_s2_class_moment2_oracle (trace j)))
  (root j ^ 2) (ideal_final_s2_class_moment2_oracle (trace j))
  (interval_pow2_valid (balls j) hv) (interval_point_valid _)
  (interval_pow2_holds (balls j) (root j) hv hx)
  (interval_point_holds _)).
qed.

lemma root_class_moment3_interval_sound trace root balls n j :
  root_interval_certificate root balls n =>
  0 <= j < n =>
  interval_valid (root_class_moment3_interval trace balls j) /\
  interval_holds (root_class_moment3_interval trace balls j)
    (root_class_moment3_term trace root j).
proof.
move=> hcert hj.
have [hv hx] := root_interval_certificate_at root balls n j hcert hj.
rewrite /root_class_moment3_interval /root_class_moment3_term
        /class_moment3_point_interval.
split.
+ exact (interval_mul_valid
    (interval_pow3 (balls j))
    (interval_point (ideal_final_s2_class_moment3_oracle (trace j)))
    (interval_pow3_valid (balls j) hv)
    (interval_point_valid _)).
exact (interval_mul_holds
  (interval_pow3 (balls j))
  (interval_point (ideal_final_s2_class_moment3_oracle (trace j)))
  (root j ^ 3) (ideal_final_s2_class_moment3_oracle (trace j))
  (interval_pow3_valid (balls j) hv) (interval_point_valid _)
  (interval_pow3_holds (balls j) (root j) hv hx)
  (interval_point_holds _)).
qed.

lemma root_class_moment4_interval_sound trace root balls n j :
  root_interval_certificate root balls n =>
  0 <= j < n =>
  interval_valid (root_class_moment4_interval trace balls j) /\
  interval_holds (root_class_moment4_interval trace balls j)
    (root_class_moment4_term trace root j).
proof.
move=> hcert hj.
have [hv hx] := root_interval_certificate_at root balls n j hcert hj.
rewrite /root_class_moment4_interval /root_class_moment4_term
        /class_moment4_point_interval.
split.
+ exact (interval_mul_valid
    (interval_pow4 (balls j))
    (interval_point (ideal_final_s2_class_moment4_oracle (trace j)))
    (interval_pow4_valid (balls j) hv)
    (interval_point_valid _)).
exact (interval_mul_holds
  (interval_pow4 (balls j))
  (interval_point (ideal_final_s2_class_moment4_oracle (trace j)))
  (root j ^ 4) (ideal_final_s2_class_moment4_oracle (trace j))
  (interval_pow4_valid (balls j) hv) (interval_point_valid _)
  (interval_pow4_holds (balls j) (root j) hv hx)
  (interval_point_holds _)).
qed.

lemma root_class_moment5_interval_sound trace root balls n j :
  root_interval_certificate root balls n =>
  0 <= j < n =>
  interval_valid (root_class_moment5_interval trace balls j) /\
  interval_holds (root_class_moment5_interval trace balls j)
    (root_class_moment5_term trace root j).
proof.
move=> hcert hj.
have [hv hx] := root_interval_certificate_at root balls n j hcert hj.
rewrite /root_class_moment5_interval /root_class_moment5_term
        /class_moment5_point_interval.
split.
+ exact (interval_mul_valid
    (interval_pow5 (balls j))
    (interval_point (ideal_final_s2_class_moment5_oracle (trace j)))
    (interval_pow5_valid (balls j) hv)
    (interval_point_valid _)).
exact (interval_mul_holds
  (interval_pow5 (balls j))
  (interval_point (ideal_final_s2_class_moment5_oracle (trace j)))
  (root j ^ 5) (ideal_final_s2_class_moment5_oracle (trace j))
  (interval_pow5_valid (balls j) hv) (interval_point_valid _)
  (interval_pow5_holds (balls j) (root j) hv hx)
  (interval_point_holds _)).
qed.

lemma root_class_moment6_interval_sound trace root balls n j :
  root_interval_certificate root balls n =>
  0 <= j < n =>
  interval_valid (root_class_moment6_interval trace balls j) /\
  interval_holds (root_class_moment6_interval trace balls j)
    (root_class_moment6_term trace root j).
proof.
move=> hcert hj.
have [hv hx] := root_interval_certificate_at root balls n j hcert hj.
rewrite /root_class_moment6_interval /root_class_moment6_term
        /class_moment6_point_interval.
split.
+ exact (interval_mul_valid
    (interval_pow6 (balls j))
    (interval_point (ideal_final_s2_class_moment6_oracle (trace j)))
    (interval_pow6_valid (balls j) hv)
    (interval_point_valid _)).
exact (interval_mul_holds
  (interval_pow6 (balls j))
  (interval_point (ideal_final_s2_class_moment6_oracle (trace j)))
  (root j ^ 6) (ideal_final_s2_class_moment6_oracle (trace j))
  (interval_pow6_valid (balls j) hv) (interval_point_valid _)
  (interval_pow6_holds (balls j) (root j) hv hx)
  (interval_point_holds _)).
qed.

lemma root_class_moment8_interval_sound trace root balls n j :
  root_interval_certificate root balls n =>
  0 <= j < n =>
  interval_valid (root_class_moment8_interval trace balls j) /\
  interval_holds (root_class_moment8_interval trace balls j)
    (root_class_moment8_term trace root j).
proof.
move=> hcert hj.
have [hv hx] := root_interval_certificate_at root balls n j hcert hj.
rewrite /root_class_moment8_interval /root_class_moment8_term
        /class_moment8_point_interval.
split.
+ exact (interval_mul_valid
    (interval_pow8 (balls j))
    (interval_point (ideal_final_s2_class_moment8_oracle (trace j)))
    (interval_pow8_valid (balls j) hv)
    (interval_point_valid _)).
exact (interval_mul_holds
  (interval_pow8 (balls j))
  (interval_point (ideal_final_s2_class_moment8_oracle (trace j)))
  (root j ^ 8) (ideal_final_s2_class_moment8_oracle (trace j))
  (interval_pow8_valid (balls j) hv) (interval_point_valid _)
  (interval_pow8_holds (balls j) (root j) hv hx)
  (interval_point_holds _)).
qed.

lemma root_class_profile2_interval_sound trace root balls n :
  root_interval_certificate root balls n =>
  interval_valid (root_class_profile2_interval trace balls n) /\
  interval_holds (root_class_profile2_interval trace balls n)
    (root_class_profile2 trace root n).
proof.
move=> hcert.
rewrite /root_class_profile2_interval /root_class_profile2.
split.
+ apply interval_bigi_valid => j hj.
  have [hv _] :=
    root_class_moment2_interval_sound trace root balls n j hcert hj.
  exact hv.
apply interval_bigi_holds.
+ move=> j hj.
  have [hv _] :=
    root_class_moment2_interval_sound trace root balls n j hcert hj.
  exact hv.
move=> j hj.
have [_ hh] :=
  root_class_moment2_interval_sound trace root balls n j hcert hj.
exact hh.
qed.

lemma root_class_profile3_interval_sound trace root balls n :
  root_interval_certificate root balls n =>
  interval_valid (root_class_profile3_interval trace balls n) /\
  interval_holds (root_class_profile3_interval trace balls n)
    (root_class_profile3 trace root n).
proof.
move=> hcert.
rewrite /root_class_profile3_interval /root_class_profile3.
split.
+ apply interval_bigi_valid => j hj.
  have [hv _] :=
    root_class_moment3_interval_sound trace root balls n j hcert hj.
  exact hv.
apply interval_bigi_holds.
+ move=> j hj.
  have [hv _] :=
    root_class_moment3_interval_sound trace root balls n j hcert hj.
  exact hv.
move=> j hj.
have [_ hh] :=
  root_class_moment3_interval_sound trace root balls n j hcert hj.
exact hh.
qed.

lemma root_class_profile4_interval_step_sound trace root balls n j :
  root_interval_certificate root balls n =>
  0 <= j < n =>
  interval_valid (root_class_profile4_interval_step trace balls j) /\
  interval_holds (root_class_profile4_interval_step trace balls j)
    (root_class_profile4_step trace root j).
proof.
move=> hcert hj.
have hjprefix : 0 <= j <= n by smt().
have hcertj := root_interval_certificate_prefix root balls n j hcert hjprefix.
have [hp2v hp2h] :=
  root_class_profile2_interval_sound trace root balls j hcertj.
have [ht2v ht2h] :=
  root_class_moment2_interval_sound trace root balls n j hcert hj.
have [ht4v ht4h] :=
  root_class_moment4_interval_sound trace root balls n j hcert hj.
rewrite /root_class_profile4_interval_step /root_class_profile4_step.
split.
+ apply interval_add_valid.
  + exact (interval_scale_mul_valid 6%r
      (root_class_profile2_interval trace balls j)
      (root_class_moment2_interval trace balls j) hp2v ht2v).
  exact ht4v.
apply interval_add_holds.
+ exact (interval_scale_mul_holds 6%r
    (root_class_profile2_interval trace balls j)
    (root_class_moment2_interval trace balls j)
    (root_class_profile2 trace root j)
    (root_class_moment2_term trace root j)
    hp2v ht2v hp2h ht2h).
exact ht4h.
qed.

lemma root_class_profile4_interval_sound trace root balls n :
  root_interval_certificate root balls n =>
  interval_valid (root_class_profile4_interval trace balls n) /\
  interval_holds (root_class_profile4_interval trace balls n)
    (root_class_profile4 trace root n).
proof.
move=> hcert.
rewrite /root_class_profile4_interval /root_class_profile4.
split.
+ apply interval_bigi_valid => j hj.
  have [hv _] :=
    root_class_profile4_interval_step_sound trace root balls n j hcert hj.
  exact hv.
apply interval_bigi_holds.
+ move=> j hj.
  have [hv _] :=
    root_class_profile4_interval_step_sound trace root balls n j hcert hj.
  exact hv.
move=> j hj.
have [_ hh] :=
  root_class_profile4_interval_step_sound trace root balls n j hcert hj.
exact hh.
qed.

lemma root_class_profile5_interval_step_sound trace root balls n j :
  root_interval_certificate root balls n =>
  0 <= j < n =>
  interval_valid (root_class_profile5_interval_step trace balls j) /\
  interval_holds (root_class_profile5_interval_step trace balls j)
    (root_class_profile5_step trace root j).
proof.
move=> hcert hj.
have hjprefix : 0 <= j <= n by smt().
have hcertj := root_interval_certificate_prefix root balls n j hcert hjprefix.
have [hp3v hp3h] :=
  root_class_profile3_interval_sound trace root balls j hcertj.
have [hp2v hp2h] :=
  root_class_profile2_interval_sound trace root balls j hcertj.
have [ht2v ht2h] :=
  root_class_moment2_interval_sound trace root balls n j hcert hj.
have [ht3v ht3h] :=
  root_class_moment3_interval_sound trace root balls n j hcert hj.
have [ht5v ht5h] :=
  root_class_moment5_interval_sound trace root balls n j hcert hj.
rewrite /root_class_profile5_interval_step /root_class_profile5_step.
split.
+ apply interval_add3_valid.
  + exact (interval_scale_mul_valid 10%r
      (root_class_profile3_interval trace balls j)
      (root_class_moment2_interval trace balls j) hp3v ht2v).
  + exact (interval_scale_mul_valid 10%r
      (root_class_profile2_interval trace balls j)
      (root_class_moment3_interval trace balls j) hp2v ht3v).
  exact ht5v.
apply interval_add3_holds.
+ exact (interval_scale_mul_holds 10%r
    (root_class_profile3_interval trace balls j)
    (root_class_moment2_interval trace balls j)
    (root_class_profile3 trace root j)
    (root_class_moment2_term trace root j)
    hp3v ht2v hp3h ht2h).
+ exact (interval_scale_mul_holds 10%r
    (root_class_profile2_interval trace balls j)
    (root_class_moment3_interval trace balls j)
    (root_class_profile2 trace root j)
    (root_class_moment3_term trace root j)
    hp2v ht3v hp2h ht3h).
exact ht5h.
qed.

lemma root_class_profile5_interval_sound trace root balls n :
  root_interval_certificate root balls n =>
  interval_valid (root_class_profile5_interval trace balls n) /\
  interval_holds (root_class_profile5_interval trace balls n)
    (root_class_profile5 trace root n).
proof.
move=> hcert.
rewrite /root_class_profile5_interval /root_class_profile5.
split.
+ apply interval_bigi_valid => j hj.
  have [hv _] :=
    root_class_profile5_interval_step_sound trace root balls n j hcert hj.
  exact hv.
apply interval_bigi_holds.
+ move=> j hj.
  have [hv _] :=
    root_class_profile5_interval_step_sound trace root balls n j hcert hj.
  exact hv.
move=> j hj.
have [_ hh] :=
  root_class_profile5_interval_step_sound trace root balls n j hcert hj.
exact hh.
qed.

lemma root_class_profile6_interval_step_sound trace root balls n j :
  root_interval_certificate root balls n =>
  0 <= j < n =>
  interval_valid (root_class_profile6_interval_step trace balls j) /\
  interval_holds (root_class_profile6_interval_step trace balls j)
    (root_class_profile6_step trace root j).
proof.
move=> hcert hj.
have hjprefix : 0 <= j <= n by smt().
have hcertj := root_interval_certificate_prefix root balls n j hcert hjprefix.
have [hp4v hp4h] :=
  root_class_profile4_interval_sound trace root balls j hcertj.
have [hp3v hp3h] :=
  root_class_profile3_interval_sound trace root balls j hcertj.
have [hp2v hp2h] :=
  root_class_profile2_interval_sound trace root balls j hcertj.
have [ht2v ht2h] :=
  root_class_moment2_interval_sound trace root balls n j hcert hj.
have [ht3v ht3h] :=
  root_class_moment3_interval_sound trace root balls n j hcert hj.
have [ht4v ht4h] :=
  root_class_moment4_interval_sound trace root balls n j hcert hj.
have [ht6v ht6h] :=
  root_class_moment6_interval_sound trace root balls n j hcert hj.
rewrite /root_class_profile6_interval_step /root_class_profile6_step.
split.
+ apply interval_add4_valid.
  + exact (interval_scale_mul_valid 15%r
      (root_class_profile4_interval trace balls j)
      (root_class_moment2_interval trace balls j) hp4v ht2v).
  + exact (interval_scale_mul_valid 20%r
      (root_class_profile3_interval trace balls j)
      (root_class_moment3_interval trace balls j) hp3v ht3v).
  + exact (interval_scale_mul_valid 15%r
      (root_class_profile2_interval trace balls j)
      (root_class_moment4_interval trace balls j) hp2v ht4v).
  exact ht6v.
apply interval_add4_holds.
+ exact (interval_scale_mul_holds 15%r
    (root_class_profile4_interval trace balls j)
    (root_class_moment2_interval trace balls j)
    (root_class_profile4 trace root j)
    (root_class_moment2_term trace root j)
    hp4v ht2v hp4h ht2h).
+ exact (interval_scale_mul_holds 20%r
    (root_class_profile3_interval trace balls j)
    (root_class_moment3_interval trace balls j)
    (root_class_profile3 trace root j)
    (root_class_moment3_term trace root j)
    hp3v ht3v hp3h ht3h).
+ exact (interval_scale_mul_holds 15%r
    (root_class_profile2_interval trace balls j)
    (root_class_moment4_interval trace balls j)
    (root_class_profile2 trace root j)
    (root_class_moment4_term trace root j)
    hp2v ht4v hp2h ht4h).
exact ht6h.
qed.

lemma root_class_profile6_interval_sound trace root balls n :
  root_interval_certificate root balls n =>
  interval_valid (root_class_profile6_interval trace balls n) /\
  interval_holds (root_class_profile6_interval trace balls n)
    (root_class_profile6 trace root n).
proof.
move=> hcert.
rewrite /root_class_profile6_interval /root_class_profile6.
split.
+ apply interval_bigi_valid => j hj.
  have [hv _] :=
    root_class_profile6_interval_step_sound trace root balls n j hcert hj.
  exact hv.
apply interval_bigi_holds.
+ move=> j hj.
  have [hv _] :=
    root_class_profile6_interval_step_sound trace root balls n j hcert hj.
  exact hv.
move=> j hj.
have [_ hh] :=
  root_class_profile6_interval_step_sound trace root balls n j hcert hj.
exact hh.
qed.

lemma root_class_profile8_interval_step_sound trace root balls n j :
  root_interval_certificate root balls n =>
  0 <= j < n =>
  interval_valid (root_class_profile8_interval_step trace balls j) /\
  interval_holds (root_class_profile8_interval_step trace balls j)
    (root_class_profile8_step trace root j).
proof.
move=> hcert hj.
have hjprefix : 0 <= j <= n by smt().
have hcertj := root_interval_certificate_prefix root balls n j hcert hjprefix.
have [hp6v hp6h] :=
  root_class_profile6_interval_sound trace root balls j hcertj.
have [hp5v hp5h] :=
  root_class_profile5_interval_sound trace root balls j hcertj.
have [hp4v hp4h] :=
  root_class_profile4_interval_sound trace root balls j hcertj.
have [hp3v hp3h] :=
  root_class_profile3_interval_sound trace root balls j hcertj.
have [hp2v hp2h] :=
  root_class_profile2_interval_sound trace root balls j hcertj.
have [ht2v ht2h] :=
  root_class_moment2_interval_sound trace root balls n j hcert hj.
have [ht3v ht3h] :=
  root_class_moment3_interval_sound trace root balls n j hcert hj.
have [ht4v ht4h] :=
  root_class_moment4_interval_sound trace root balls n j hcert hj.
have [ht5v ht5h] :=
  root_class_moment5_interval_sound trace root balls n j hcert hj.
have [ht6v ht6h] :=
  root_class_moment6_interval_sound trace root balls n j hcert hj.
have [ht8v ht8h] :=
  root_class_moment8_interval_sound trace root balls n j hcert hj.
rewrite /root_class_profile8_interval_step /root_class_profile8_step.
split.
+ apply interval_add6_valid.
  + exact (interval_scale_mul_valid 28%r
      (root_class_profile6_interval trace balls j)
      (root_class_moment2_interval trace balls j) hp6v ht2v).
  + exact (interval_scale_mul_valid 56%r
      (root_class_profile5_interval trace balls j)
      (root_class_moment3_interval trace balls j) hp5v ht3v).
  + exact (interval_scale_mul_valid 70%r
      (root_class_profile4_interval trace balls j)
      (root_class_moment4_interval trace balls j) hp4v ht4v).
  + exact (interval_scale_mul_valid 56%r
      (root_class_profile3_interval trace balls j)
      (root_class_moment5_interval trace balls j) hp3v ht5v).
  + exact (interval_scale_mul_valid 28%r
      (root_class_profile2_interval trace balls j)
      (root_class_moment6_interval trace balls j) hp2v ht6v).
  exact ht8v.
apply interval_add6_holds.
+ exact (interval_scale_mul_holds 28%r
    (root_class_profile6_interval trace balls j)
    (root_class_moment2_interval trace balls j)
    (root_class_profile6 trace root j)
    (root_class_moment2_term trace root j)
    hp6v ht2v hp6h ht2h).
+ exact (interval_scale_mul_holds 56%r
    (root_class_profile5_interval trace balls j)
    (root_class_moment3_interval trace balls j)
    (root_class_profile5 trace root j)
    (root_class_moment3_term trace root j)
    hp5v ht3v hp5h ht3h).
+ exact (interval_scale_mul_holds 70%r
    (root_class_profile4_interval trace balls j)
    (root_class_moment4_interval trace balls j)
    (root_class_profile4 trace root j)
    (root_class_moment4_term trace root j)
    hp4v ht4v hp4h ht4h).
+ exact (interval_scale_mul_holds 56%r
    (root_class_profile3_interval trace balls j)
    (root_class_moment5_interval trace balls j)
    (root_class_profile3 trace root j)
    (root_class_moment5_term trace root j)
    hp3v ht5v hp3h ht5h).
+ exact (interval_scale_mul_holds 28%r
    (root_class_profile2_interval trace balls j)
    (root_class_moment6_interval trace balls j)
    (root_class_profile2 trace root j)
    (root_class_moment6_term trace root j)
    hp2v ht6v hp2h ht6h).
exact ht8h.
qed.

lemma root_class_profile8_interval_sound trace root balls n :
  root_interval_certificate root balls n =>
  interval_valid (root_class_profile8_interval trace balls n) /\
  interval_holds (root_class_profile8_interval trace balls n)
    (root_class_profile8 trace root n).
proof.
move=> hcert.
rewrite /root_class_profile8_interval /root_class_profile8.
split.
+ apply interval_bigi_valid => j hj.
  have [hv _] :=
    root_class_profile8_interval_step_sound trace root balls n j hcert hj.
  exact hv.
apply interval_bigi_holds.
+ move=> j hj.
  have [hv _] :=
    root_class_profile8_interval_step_sound trace root balls n j hcert hj.
  exact hv.
move=> j hj.
have [_ hh] :=
  root_class_profile8_interval_step_sound trace root balls n j hcert hj.
exact hh.
qed.

op odd_root_re_component (k j : int) : real =
  KeygenM23ComplexReal.creal
    (KeygenM23IdealRootDFT.cpow (KeygenM23IdealRootDFT.odd_root k) j).

op odd_root_im_component (k j : int) : real =
  KeygenM23ComplexReal.cimag
    (KeygenM23IdealRootDFT.cpow (KeygenM23IdealRootDFT.odd_root k) j).

op odd_root_re_interval_certificate
    (balls : int -> rinterval) (k n : int) : bool =
  root_interval_certificate (odd_root_re_component k) balls n.

op odd_root_im_interval_certificate
    (balls : int -> rinterval) (k n : int) : bool =
  root_interval_certificate (odd_root_im_component k) balls n.

lemma root_class_re_profile8E trace k n :
  root_class_profile8 trace (odd_root_re_component k) n =
  ideal_final_s2_class_re_profile8 trace k n.
proof.
rewrite /root_class_profile8 /root_class_profile8_step
        /root_class_profile6 /root_class_profile6_step
        /root_class_profile5 /root_class_profile5_step
        /root_class_profile4 /root_class_profile4_step
        /root_class_profile3 /root_class_profile2
        /root_class_moment2_term /root_class_moment3_term
        /root_class_moment4_term /root_class_moment5_term
        /root_class_moment6_term /root_class_moment8_term
        /odd_root_re_component
        /ideal_final_s2_class_re_profile8
        /ideal_final_s2_class_re_profile6
        /ideal_final_s2_class_re_profile5
        /ideal_final_s2_class_re_profile4
        /ideal_final_s2_class_re_profile3
        /ideal_final_s2_class_re_profile2
        /ideal_final_s2_class_re_moment2_term
        /ideal_final_s2_class_re_moment3_term
        /ideal_final_s2_class_re_moment4_term
        /ideal_final_s2_class_re_moment5_term
        /ideal_final_s2_class_re_moment6_term
        /ideal_final_s2_class_re_moment8_term.
trivial.
qed.

lemma root_class_im_profile8E trace k n :
  root_class_profile8 trace (odd_root_im_component k) n =
  ideal_final_s2_class_im_profile8 trace k n.
proof.
rewrite /root_class_profile8 /root_class_profile8_step
        /root_class_profile6 /root_class_profile6_step
        /root_class_profile5 /root_class_profile5_step
        /root_class_profile4 /root_class_profile4_step
        /root_class_profile3 /root_class_profile2
        /root_class_moment2_term /root_class_moment3_term
        /root_class_moment4_term /root_class_moment5_term
        /root_class_moment6_term /root_class_moment8_term
        /odd_root_im_component
        /ideal_final_s2_class_im_profile8
        /ideal_final_s2_class_im_profile6
        /ideal_final_s2_class_im_profile5
        /ideal_final_s2_class_im_profile4
        /ideal_final_s2_class_im_profile3
        /ideal_final_s2_class_im_profile2
        /ideal_final_s2_class_im_moment2_term
        /ideal_final_s2_class_im_moment3_term
        /ideal_final_s2_class_im_moment4_term
        /ideal_final_s2_class_im_moment5_term
        /ideal_final_s2_class_im_moment6_term
        /ideal_final_s2_class_im_moment8_term.
trivial.
qed.

lemma odd_root_re_class_profile8_interval_sound trace balls k n :
  odd_root_re_interval_certificate balls k n =>
  interval_valid (root_class_profile8_interval trace balls n) /\
  interval_holds (root_class_profile8_interval trace balls n)
    (ideal_final_s2_class_re_profile8 trace k n).
proof.
rewrite /odd_root_re_interval_certificate.
move=> hcert.
have [hv hh] :=
  root_class_profile8_interval_sound
    trace (odd_root_re_component k) balls n hcert.
split; first exact hv.
rewrite -root_class_re_profile8E.
exact hh.
qed.

lemma odd_root_im_class_profile8_interval_sound trace balls k n :
  odd_root_im_interval_certificate balls k n =>
  interval_valid (root_class_profile8_interval trace balls n) /\
  interval_holds (root_class_profile8_interval trace balls n)
    (ideal_final_s2_class_im_profile8 trace k n).
proof.
rewrite /odd_root_im_interval_certificate.
move=> hcert.
have [hv hh] :=
  root_class_profile8_interval_sound
    trace (odd_root_im_component k) balls n hcert.
split; first exact hv.
rewrite -root_class_im_profile8E.
exact hh.
qed.

lemma ideal_final_s2_row_residual_profile8_interval_sound
    pre_bp avec row k n re_balls im_balls :
  odd_root_re_interval_certificate re_balls k n =>
  odd_root_im_interval_certificate im_balls k n =>
  (interval_valid
      (root_class_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) re_balls n) /\
   interval_holds
      (root_class_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) re_balls n)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k n)) /\
  (interval_valid
      (root_class_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) im_balls n) /\
   interval_holds
      (root_class_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) im_balls n)
      (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
        .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k n)).
proof.
move=> hre_cert him_cert.
have [hre_valid hre_holds] :=
  odd_root_re_class_profile8_interval_sound
    (ideal_final_s2_row_class_trace pre_bp avec row) re_balls k n hre_cert.
have [him_valid him_holds] :=
  odd_root_im_class_profile8_interval_sound
    (ideal_final_s2_row_class_trace pre_bp avec row) im_balls k n him_cert.
have [hreE himE] :=
  ideal_final_s2_row_residual_profile8_class_traceE pre_bp avec row k n.
split.
+ split; first exact hre_valid.
  rewrite hreE.
  exact hre_holds.
split; first exact him_valid.
rewrite himE.
exact him_holds.
qed.

lemma ideal_final_s2_row_residual_profile8_interval_abs_upper
    pre_bp avec row k n re_balls im_balls :
  odd_root_re_interval_certificate re_balls k n =>
  odd_root_im_interval_certificate im_balls k n =>
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k n| <=
    interval_abs_upper
      (root_class_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) re_balls n) /\
  `|Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k n| <=
    interval_abs_upper
      (root_class_profile8_interval
        (ideal_final_s2_row_class_trace pre_bp avec row) im_balls n).
proof.
move=> hre_cert him_cert.
have [[_ hre_holds] [_ him_holds]] :=
  ideal_final_s2_row_residual_profile8_interval_sound
    pre_bp avec row k n re_balls im_balls hre_cert him_cert.
split.
+ exact (interval_holds_abs_le
    (root_class_profile8_interval
      (ideal_final_s2_row_class_trace pre_bp avec row) re_balls n)
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
      .ideal_final_s2_row_residual_re_profile8 pre_bp avec row k n)
    hre_holds).
exact (interval_holds_abs_le
  (root_class_profile8_interval
    (ideal_final_s2_row_class_trace pre_bp avec row) im_balls n)
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentPostFreeze
    .ideal_final_s2_row_residual_im_profile8 pre_bp avec row k n)
  him_holds).
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualFFTEighthMomentRootIntervalClassProfilePostFreeze.
