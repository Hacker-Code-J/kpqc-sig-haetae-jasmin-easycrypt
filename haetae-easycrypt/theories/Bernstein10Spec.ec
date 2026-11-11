require import AllCore List Real.

(* Fixed degree-ten power and Bernstein bases.  Entries beyond index ten
   are irrelevant to evaluation; certificates require exactly eleven. *)
op power_eval (a : int list) (t : real) : real =
  (nth 0 a 0)%r +
  (nth 0 a 1)%r * t +
  (nth 0 a 2)%r * t^2 +
  (nth 0 a 3)%r * t^3 +
  (nth 0 a 4)%r * t^4 +
  (nth 0 a 5)%r * t^5 +
  (nth 0 a 6)%r * t^6 +
  (nth 0 a 7)%r * t^7 +
  (nth 0 a 8)%r * t^8 +
  (nth 0 a 9)%r * t^9 +
  (nth 0 a 10)%r * t^10.

op bernstein_eval (b : int list) (t : real) : real =
  (nth 0 b 0)%r * (1%r-t)^10 +
  10%r * (nth 0 b 1)%r * t * (1%r-t)^9 +
  45%r * (nth 0 b 2)%r * t^2 * (1%r-t)^8 +
  120%r * (nth 0 b 3)%r * t^3 * (1%r-t)^7 +
  210%r * (nth 0 b 4)%r * t^4 * (1%r-t)^6 +
  252%r * (nth 0 b 5)%r * t^5 * (1%r-t)^5 +
  210%r * (nth 0 b 6)%r * t^6 * (1%r-t)^4 +
  120%r * (nth 0 b 7)%r * t^7 * (1%r-t)^3 +
  45%r * (nth 0 b 8)%r * t^8 * (1%r-t)^2 +
  10%r * (nth 0 b 9)%r * t^9 * (1%r-t) +
  (nth 0 b 10)%r * t^10.

(* The k-th entry is C(10,k) times the k-th forward difference
   sum_{i=0}^k (-1)^(k-i) C(k,i) b_i.  These are integer operations;
   their algebraic meaning is proved independently of certificate data. *)
op bernstein10_power_coefficients (b : int list) : int list =
  let b0 = nth 0 b 0 in let b1 = nth 0 b 1 in
  let b2 = nth 0 b 2 in let b3 = nth 0 b 3 in
  let b4 = nth 0 b 4 in let b5 = nth 0 b 5 in
  let b6 = nth 0 b 6 in let b7 = nth 0 b 7 in
  let b8 = nth 0 b 8 in let b9 = nth 0 b 9 in
  let b10 = nth 0 b 10 in
  [b0;
   10 * (-b0+b1);
   45 * (b0-2*b1+b2);
   120 * (-b0+3*b1-3*b2+b3);
   210 * (b0-4*b1+6*b2-4*b3+b4);
   252 * (-b0+5*b1-10*b2+10*b3-5*b4+b5);
   210 * (b0-6*b1+15*b2-20*b3+15*b4-6*b5+b6);
   120 * (-b0+7*b1-21*b2+35*b3-35*b4+21*b5-7*b6+b7);
   45 * (b0-8*b1+28*b2-56*b3+70*b4-56*b5+28*b6-8*b7+b8);
   10 * (-b0+9*b1-36*b2+84*b3-126*b4+126*b5-84*b6+36*b7-9*b8+b9);
   b0-10*b1+45*b2-120*b3+210*b4-252*b5+210*b6-120*b7+45*b8-10*b9+b10].

op bernstein10_check (a b : int list) : bool =
  size a = 11 /\ size b = 11 /\
  a = bernstein10_power_coefficients b /\ all (fun x => 0 <= x) b.
