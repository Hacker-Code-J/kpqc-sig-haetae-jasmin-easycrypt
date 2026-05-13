require import AllCore List IntDiv Ring StdOrder BitEncoding.
require import Array256.
require import Fq Fastexp.
require import GFq Rq.
import Zq IntOrder BitReverse.

theory Debug8.

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

lemma tail_goal : forall len0:int, (len0 <= 0 => ! 1 <= len0) /\ true.
proof.
move=> len0.
print goal 1.
abort.

end Debug8.
