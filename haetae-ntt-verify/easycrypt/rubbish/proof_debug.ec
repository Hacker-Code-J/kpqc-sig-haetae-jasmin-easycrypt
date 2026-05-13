require import AllCore List IntDiv Ring StdOrder BitEncoding.
require import Array256.
require import Fq Fastexp.
require import GFq Rq.
import Zq IntOrder BitReverse.

theory Debug.

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
    auto => />.
    move=> *.
    print goal 1.
abort.

end Debug.
