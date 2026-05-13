require import AllCore List IntDiv Ring StdOrder BitEncoding.
require import Array256.
require import Fq Fastexp.
require import GFq Rq.
import Zq IntOrder BitReverse.

theory Debug11.

module NTT = {
 proc ntt(r : coeff Array256.t, zetas : coeff Array256.t) : coeff Array256.t = {
   var len, start, j, zetasctr;
   var t, zeta_;
   zetasctr <- 0;
   len <- 128;
   while (1 <= len) { start <- 0; while(start < 256) { j <- start; while (j < start + len) { j <- j + 1; } start <- j + len; } len <- len %/ 2; }
   return r;
 }
}.

lemma t : islossless NTT.ntt.
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
      wp. skip => &hr [[hlen hj] hz] /=.
      split; first exact hlen.
      rewrite -hz.
      have -> : start{hr} + len{hr} - (j{hr} + 1) = start{hr} + len{hr} - j{hr} - 1 by ring.
      have -> : start{hr} + len{hr} - j{hr} = (start{hr} + len{hr} - j{hr} - 1) + 1 by ring.
      rewrite ltz_addl.
      trivial.
    wp. skip => &hr [[hlen0 hstart0] hz'] /=.
      split; first exact hlen0.
      move=> j0; split.
      + move=> h. rewrite -lezNgt. move: h. rewrite ler_subl_addr add0r. trivial.
      move=> hj0 hlen1. split; first exact hlen1. rewrite -hz'. apply (ntt_middle_right start{hr} len{hr} j0); first exact hlen1. exact hj0.
  auto => />.
  print goal 1.
abort.

end Debug11.
