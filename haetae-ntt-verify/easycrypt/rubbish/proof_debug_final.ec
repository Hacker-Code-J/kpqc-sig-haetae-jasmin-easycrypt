require import AllCore List IntDiv Ring StdOrder BitEncoding.
require import Array256.
require import Fq Fastexp.
require import GFq Rq.
import Zq IntOrder BitReverse.

theory DebugFinal.

module NTT = {
 proc ntt(r : coeff Array256.t, zetas : coeff Array256.t) : coeff Array256.t = {
   var len, start, j, zetasctr;
   var t, zeta_;
   zetasctr <- 0;
   len <- 128;
   while (1 <= len) {
    start <- 0;
    while(start < 256) {
       zetasctr <- zetasctr + 1;
       zeta_ <- zetas.[zetasctr];
       j <- start;
       while (j < start + len) {
         t <- zeta_ * r.[j + len];
         r.[j + len] <- r.[j] + (-t);
         r.[j]       <- r.[j] + t;
         j <- j + 1;
       }
       start <- j + len;
     }
     len <- len %/ 2;
   }
   return r;
 }
}.

lemma ntt_middle_right start len j0 :
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
  + apply (ler_trans _ _ _ _ hle).
    rewrite lez_addl.
    apply ltrW.
    exact hlen0.
  have hj0len : j0 < j0 + len.
  + rewrite ltz_addl.
    exact hlen0.
  exact (ler_lt_trans _ _ _ hsj0 hj0len).
qed.

lemma ntt_spec_ll : islossless NTT.ntt.
proof.
proc.
wp.
while (true) len.
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
    apply (ntt_middle_right start{hr} len{hr} j0); first exact hlen1.
    exact hj0.
  wp.
  skip => &hr /=.
  print goal 1.
abort.

end DebugFinal.
