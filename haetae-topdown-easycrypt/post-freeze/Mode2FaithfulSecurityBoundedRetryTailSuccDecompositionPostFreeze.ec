require import AllCore.

from Jasmin require import JModel_x86.

require import BArray128 BArray8192 BArray32768.
require import Mode2FaithfulSecurityBoundedRetryTailPostFreeze
               Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze.

theory Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze.

import Mode2FaithfulSecurityBoundedRetryTailPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze.

module BoundedTail =
  Mode2FaithfulSecurityBoundedRetryTailPostFreeze
    .CheckedMode2BoundedRetryTail.

module OneMore =
  Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze
    .CheckedMode2RetryOneMoreObserver.

(* This proof-only composition exposes the [fuel] result before conditionally
   taking the adjacent retry.  The decomposition theorem below connects its
   large projection to the actual bounded-tail driver at [fuel + 1].  It does
   not claim retry independence, a contraction factor, unbounded termination,
   packing, full key generation, or equality with [HAETAE.kg]. *)

module CheckedMode2BoundedRetryTailThenOneMore = {
  proc run
      (seedbuf : BArray128.t, mat : BArray32768.t,
       avec : BArray8192.t, s1 : BArray8192.t, s2 : BArray8192.t,
       bp : BArray8192.t, s1hatp : BArray8192.t,
       counter : W64.t, retry fuel : int)
      : checked_mode2_retry_one_more_pair = {
    var small : checked_mode2_bounded_retry_tail_result;
    var pair : checked_mode2_retry_one_more_pair;

    small <@ BoundedTail.run
      (seedbuf, mat, avec, s1, s2, bp, s1hatp,
       counter, retry, fuel);
    pair <@ OneMore.run(small);
    return pair;
  }
}.

lemma checked_mode2_bounded_retry_tail_succ_decomposition :
  equiv [BoundedTail.run ~ CheckedMode2BoundedRetryTailThenOneMore.run :
    ={seedbuf, mat, avec, s1, s2, bp, s1hatp, counter, retry} /\
    fuel{1} = fuel{2} + 1 /\ 0 <= fuel{2}
    ==>
    res{1} = res{2}.`2].
proof.
proc.
inline BoundedTail.run OneMore.run.
splitwhile{1} 4 : (1 < fuel).
sp 3 13.
seq 1 1 :
  (seedbuf{1} = seedbuf0{!2} /\ mat{1} = mat0{!2} /\
   avec{1} = avec0{!2} /\ s1{1} = s10{!2} /\
   s2{1} = s20{!2} /\ bp{1} = bp0{!2} /\
   s1hatp{1} = s1hatp0{2} /\ counter{1} = counter0{!2} /\
   reject{1} = reject{2} /\ retry{1} = retry0{!2} /\
   fuel{1} = fuel0{!2} + 1 /\ steps{1} = steps{2} /\
   0 <= fuel0{!2} /\
   ! (((0 < fuel{1} /\ reject{1} = W64.one) /\ 1 < fuel{1})) /\
   ! (0 < fuel0{!2} /\ reject{2} = W64.one)).
+ while
    (seedbuf{1} = seedbuf0{!2} /\ mat{1} = mat0{!2} /\
     avec{1} = avec0{!2} /\ s1{1} = s10{!2} /\
     s2{1} = s20{!2} /\ bp{1} = bp0{!2} /\
     s1hatp{1} = s1hatp0{2} /\ counter{1} = counter0{!2} /\
     reject{1} = reject{2} /\ retry{1} = retry0{!2} /\
     fuel{1} = fuel0{!2} + 1 /\ steps{1} = steps{2} /\
     0 <= fuel0{!2}).
  + wp.
    call (_ : ={arg} ==> ={res}).
    * by proc; sim.
    * auto => />; smt().
  + auto => />; smt().
+ sp 0 2.
  unroll {1} 1.
  if.
  + auto => />; smt().
  + rcondf{1} 14.
    * move=> &m.
      wp.
      call (_ : true).
      + auto.
      + skip.
        auto => />; smt().
    wp.
    call (_ : ={arg} ==> ={res}).
    * by proc; sim.
    * auto => />.
      rewrite /checked_mode2_retry_one_more_result.
  + rcondf{1} 1.
    * move=> &m; skip; auto.
    auto => />.
qed.

end Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze.
