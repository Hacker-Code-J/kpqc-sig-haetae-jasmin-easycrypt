require import AllCore List IntDiv Ring StdOrder BitEncoding.
require import Array256.
require import Fq Fastexp.
require import GFq Rq.
import Zq IntOrder BitReverse.

theory InvDebugFinal.

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

lemma t : islossless NTT.invntt.
proof.
proc.
wp.
while (true) (256 - j).
+ move=> z.
  wp.
  skip => &hr hj.
  print goal 1.
abort.

end InvDebugFinal.
