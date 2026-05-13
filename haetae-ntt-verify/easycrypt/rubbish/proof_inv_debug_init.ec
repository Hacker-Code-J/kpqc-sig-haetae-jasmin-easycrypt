require import AllCore List IntDiv Ring StdOrder BitEncoding.
require import Array256.
require import Fq Fastexp.
require import GFq Rq.
import Zq IntOrder BitReverse.

theory InvDebugInit.

module NTT = {
 proc invntt(r : coeff Array256.t, zetas_inv : coeff Array256.t) : coeff Array256.t = {
   var len, start, j, zetasctr;
   var t, zeta_;
   zetasctr <- 0;
   len <- 1;
   while (len < 256) { start <- 0; while(start < 256) { zeta_ <- zetas_inv.[zetasctr]; zetasctr <- zetasctr + 1; j <- start; while (j < start + len) { t <- r.[j]; r.[j] <- t + r.[j + len]; r.[j + len] <- t + (-r.[j + len]); r.[j + len] <- zeta_ * r.[j + len]; j <- j + 1; } start <- j + len; } len <- len * 2; }
   j <- 0;
   while (j < 256) { r.[j] <- r.[j] * zetas_inv.[255]; j <- j + 1; }
   return r;
 }
}.

lemma t : islossless NTT.invntt.
proof.
proc.
wp.
while (true) (256 - j).
+ move=> z. wp. skip => &hr [hj hz] /=. rewrite -hz. have -> : 256 - j{hr} = (256 - (j{hr} + 1)) + 1 by ring. rewrite ltz_addl. trivial.
wp.
while (0 < len) (256 - len).
+ move=> z.
  wp.
  while (0 < len) (256 - start).
  + move=> z'. wp.
    while (0 < len) (start + len - j).
    + move=> z''. wp. skip => &hr [[hlen hj] hz] /=. split; first exact hlen. rewrite -hz. have -> : start{hr} + len{hr} - (j{hr} + 1) = start{hr} + len{hr} - j{hr} - 1 by ring. have -> : start{hr} + len{hr} - j{hr} = (start{hr} + len{hr} - j{hr} - 1) + 1 by ring. rewrite ltz_addl. trivial.
    wp. skip => &hr [[hlen0 hstart0] hz'] /=. split; first exact hlen0. move=> j0; split. + move=> h. rewrite -lezNgt. move: h. rewrite ler_subl_addr add0r. trivial. move=> hj0 hlen1. split; first exact hlen1. rewrite -hz'. apply (inv_middle_right start{hr} len{hr} j0); first exact hlen1. exact hj0.
  auto => />.
wp.
skip => &hr /=.
print goal 1.
abort.

end InvDebugInit.
