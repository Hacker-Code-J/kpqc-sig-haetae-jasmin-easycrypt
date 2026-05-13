require import AllCore List IntDiv Ring StdOrder BitEncoding.
require import Array256.
require import Fq Fastexp.
require import GFq Rq.
import Zq IntOrder BitReverse.

theory InvScratch.

module NTT = {
 proc invntt(r : coeff Array256.t, zetas_inv : coeff Array256.t) : coeff Array256.t = {
   var len, start, j, zetasctr;
   var t, zeta_;

   zetasctr <- 0;
   len <- 1;
   while (len < 256) {
    start <- 0;
    while(start < 256) {
       zeta_ <- zetas_inv.[zetasctr];
       zetasctr <- zetasctr + 1;
       j <- start;
       while (j < start + len) {
        t <- r.[j];
        r.[j]       <- t + r.[j + len];
        r.[j + len] <- t + (-r.[j + len]);
        r.[j + len] <- zeta_ * r.[j + len];
         j <- j + 1;
       }
       start <- j + len;
     }
     len <- len * 2;
   }
   j <- 0;
   while (j < 256) {
     r.[j] <- r.[j] * zetas_inv.[255];
     j <- j + 1;
   }
   return r;
 }
}.

lemma inv_final_progress j :
  j < 256 =>
  256 - (j + 1) < 256 - j.
proof.
  move=> hj.
  have -> : 256 - j = (256 - (j + 1)) + 1 by ring.
  rewrite ltz_addl.
  trivial.
qed.

lemma inv_middle_right start len j0 :
  0 < len =>
  ! j0 < start + len =>
  256 - (j0 + len) < 256 - start.
proof.
  move=> hlen0 hj0.
  have hle : start + len <= j0 by rewrite -lezNgt in hj0.
  rewrite ltr_subr_addr.
  have -> : 256 - (j0 + len) + start = start - (j0 + len) + 256 by ring.
  have -> : 256 = 0 + 256 by ring.
  rewrite ltr_add2r ltr_subl_addr add0r.
  have hsj0 : start <= j0.
  + apply (lez_trans _ _ _ _ hle).
    rewrite lez_addl.
    apply ltrW.
    exact hlen0.
  have hj0len : j0 < j0 + len.
  + rewrite ltz_addl.
    exact hlen0.
  exact (ler_lt_trans _ _ _ hsj0 hj0len).
qed.

lemma inv_outer_progress len :
  0 < len =>
  len < 256 =>
  forall start0,
    (256 - start0 <= 0 => ! start0 < 256) /\
    (! start0 < 256 => 0 < len * 2 /\ 256 - len * 2 < 256 - len).
proof.
move=> hlen hlt256 start0; split.
+ move=> h.
  rewrite -lezNgt.
  move: h.
  rewrite ler_subl_addr add0r.
  trivial.
move=> _.
split.
+ have -> : len * 2 = len + len by ring.
  have -> : 0 = 0 + 0 by ring.
  have h00 : 0 + 0 < len + len by exact (ltr_add _ _ _ _ hlen hlen).
  exact h00.
have -> : 256 - len * 2 = 256 - (len + len) by ring.
have -> : 256 - len = (256 - (len + len)) + len by ring.
rewrite ltr_addl.
exact hlen.
qed.

lemma invntt_spec_ll : islossless NTT.invntt.
proof.
proc.
wp.
while (true) (256 - j).
+ move=> z.
  wp.
  skip => &hr [hj hz] /=.
  rewrite -hz.
  have -> : 256 - j{hr} = (256 - (j{hr} + 1)) + 1 by ring.
  rewrite ltz_addl.
  trivial.
wp.
while (0 < len) (256 - len).
+ move=> z.
  wp.
  while (0 < len) (256 - start).
  + move=> z'.
    wp.
    while (0 < len) (start + len - j).
    + move=> z''.
      wp.
      skip => &hr [[hlen hj] hz] /=.
      split; first exact hlen.
      rewrite -hz.
      have -> : start{hr} + len{hr} - (j{hr} + 1) = start{hr} + len{hr} - j{hr} - 1 by ring.
      have -> : start{hr} + len{hr} - j{hr} = (start{hr} + len{hr} - j{hr} - 1) + 1 by ring.
      rewrite ltz_addl.
      trivial.
    wp.
    skip => &hr [[hlen0 hstart0] hz'] /=.
    split; first exact hlen0.
    move=> j0; split.
    + move=> h.
      rewrite -lezNgt.
      move: h.
      rewrite ler_subl_addr add0r.
      trivial.
    move=> hj0.
    move=> hlen1.
    split; first exact hlen1.
    rewrite -hz'.
    apply (inv_middle_right start{hr} len{hr} j0); first exact hlen1.
    exact hj0.
  auto => />.
  move=> &hr hlen hlt256.
  exact (inv_outer_progress len{hr} hlen hlt256).
wp.
skip => &hr /=.
move=> len0.
split.
+ move=> _ h.
  rewrite -lezNgt.
  move: h.
  rewrite ler_subl_addr add0r.
  trivial.
+ move=> _ _ j0 h.
  rewrite -lezNgt.
  move: h.
  rewrite ler_subl_addr add0r.
  trivial.
qed.

end InvScratch.
