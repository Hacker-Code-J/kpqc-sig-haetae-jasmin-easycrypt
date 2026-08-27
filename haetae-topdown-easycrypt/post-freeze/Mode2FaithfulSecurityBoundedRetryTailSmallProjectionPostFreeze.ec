require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray128 BArray8192 BArray32768.
require import Mode2FaithfulSecurityRetryTailInvariantPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailPostFreeze
               Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze.

theory Mode2FaithfulSecurityBoundedRetryTailSmallProjectionPostFreeze.

import RealOrder.
import Mode2FaithfulSecurityRetryTailInvariantPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze.

module BoundedTail =
  Mode2FaithfulSecurityBoundedRetryTailPostFreeze
    .CheckedMode2BoundedRetryTail.

module OneMore =
  Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze
    .CheckedMode2RetryOneMoreObserver.

module ThenOneMore =
  Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze
    .CheckedMode2BoundedRetryTailThenOneMore.

(* This file identifies the first projection of the one-more composition with
   the actual [fuel]-bounded retry result.  The additional progress window is
   used only to make the observer suffix lossless.  No retry independence,
   contraction factor, unbounded termination, packing, full key generation,
   or equality with [HAETAE.kg] is claimed. *)

module CheckedMode2BoundedRetryTailOnly = {
  proc run
      (seedbuf : BArray128.t, mat : BArray32768.t,
       avec : BArray8192.t, s1 : BArray8192.t, s2 : BArray8192.t,
       bp : BArray8192.t, s1hatp : BArray8192.t,
       counter : W64.t, retry fuel : int)
      : checked_mode2_bounded_retry_tail_result = {
    var tail : checked_mode2_bounded_retry_tail_result;

    tail <@ BoundedTail.run
      (seedbuf, mat, avec, s1, s2, bp, s1hatp,
       counter, retry, fuel);
    return tail;
  }
}.

lemma checked_mode2_retry_one_more_observer_first
    (small0 : checked_mode2_bounded_retry_tail_result) :
  hoare [OneMore.run :
    small = small0 ==> res.`1 = small0].
proof.
proc.
if.
+ wp.
  call (_ : true).
  + auto.
  + auto => />.
+ wp.
  skip.
  auto => />.
qed.

lemma checked_mode2_retry_one_more_observer_first_ll
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 : BArray8192.t)
    retry0 fuel0 eta_limits
    (small0 : checked_mode2_bounded_retry_tail_result) :
  phoare [OneMore.run :
    small = small0 /\ 0 <= fuel0 /\
    checked_mode2_bounded_retry_tail_post
      seedbuf0 mat0 avec0 retry0 fuel0 small0 /\
    checked_mode2_retry_window_progress
      seedbuf0 retry0 (fuel0 + 1) eta_limits
    ==>
    checked_mode2_bounded_retry_tail_post
      seedbuf0 mat0 avec0 retry0 fuel0 res.`1 /\
    checked_mode2_bounded_retry_tail_post
      seedbuf0 mat0 avec0 retry0 (fuel0 + 1) res.`2 /\
    (checked_mode2_bounded_retry_tail_rejected_exhaustion
       (fuel0 + 1) res.`2 =>
     checked_mode2_bounded_retry_tail_rejected_exhaustion
       fuel0 res.`1) /\
    res.`1 = small0] = 1%r.
proof.
conseq
  (checked_mode2_retry_one_more_observer_ll
    seedbuf0 mat0 avec0 retry0 fuel0 eta_limits small0)
  (checked_mode2_retry_one_more_observer_first small0) => //=.
qed.

lemma checked_mode2_bounded_retry_tail_correct
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (counter0 : W64.t) retry0 fuel0 eta_limits :
  hoare [BoundedTail.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
    s1 = s10 /\ s2 = s20 /\ bp = bp0 /\ s1hatp = s1hat0 /\
    counter = counter0 /\ retry = retry0 /\ fuel = fuel0 /\
    0 <= fuel0 /\
    checked_mode2_retry_tail_state
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0
      retry0 counter0 W64.one /\
    checked_mode2_retry_window_progress
      seedbuf0 retry0 fuel0 eta_limits
    ==>
    checked_mode2_bounded_retry_tail_post
      seedbuf0 mat0 avec0 retry0 fuel0 res].
proof.
conseq
  (checked_mode2_bounded_retry_tail_ll
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
    retry0 fuel0 eta_limits) => //=.
qed.

lemma checked_mode2_bounded_retry_tail_post_complement0
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (counter0 : W64.t) retry0 fuel0 eta_limits :
  phoare [BoundedTail.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
    s1 = s10 /\ s2 = s20 /\ bp = bp0 /\ s1hatp = s1hat0 /\
    counter = counter0 /\ retry = retry0 /\ fuel = fuel0 /\
    0 <= fuel0 /\
    checked_mode2_retry_tail_state
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0
      retry0 counter0 W64.one /\
    checked_mode2_retry_window_progress
      seedbuf0 retry0 fuel0 eta_limits
    ==>
    ! checked_mode2_bounded_retry_tail_post
        seedbuf0 mat0 avec0 retry0 fuel0 res] = 0%r.
proof.
bypr=> &m hpre.
have hgood :
  Pr[BoundedTail.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m :
     checked_mode2_bounded_retry_tail_post
       seedbuf0 mat0 avec0 retry0 fuel0 res] = 1%r.
+ by byphoare
    (checked_mode2_bounded_retry_tail_ll
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
      retry0 fuel0 eta_limits) => //.
have hpartition :
  Pr[BoundedTail.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m :
     checked_mode2_bounded_retry_tail_post
       seedbuf0 mat0 avec0 retry0 fuel0 res] +
  Pr[BoundedTail.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m :
     ! checked_mode2_bounded_retry_tail_post
         seedbuf0 mat0 avec0 retry0 fuel0 res] =
  Pr[BoundedTail.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m : true].
+ rewrite Pr[mu_not].
  ring.
have htotal_bound :
  0%r <=
    Pr[BoundedTail.run(
         seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
         bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m : true]
  <= 1%r.
+ split.
  + by rewrite Pr[mu_ge0].
  + by rewrite Pr[mu_le1].
have hsum := hpartition.
rewrite hgood in hsum.
move: htotal_bound => [_ htotal_le].
have hsum_le :
  1%r +
    Pr[BoundedTail.run(
         seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
         bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m :
       ! checked_mode2_bounded_retry_tail_post
           seedbuf0 mat0 avec0 retry0 fuel0 res]
  <= 1%r.
+ rewrite hsum.
  exact htotal_le.
have hbad_le0 :
  Pr[BoundedTail.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m :
     ! checked_mode2_bounded_retry_tail_post
         seedbuf0 mat0 avec0 retry0 fuel0 res]
  <= 0%r.
+ move: hsum_le.
  have hone : 1%r = 1%r + 0%r by ring.
  rewrite hone ler_add2l.
  done.
apply ler_anti.
split; first exact hbad_le0.
by rewrite Pr[mu_ge0].
qed.

lemma checked_mode2_bounded_retry_tail_self_post
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (counter0 : W64.t) retry0 fuel0 eta_limits :
  equiv [BoundedTail.run ~ BoundedTail.run :
    ={seedbuf, mat, avec, s1, s2, bp, s1hatp, counter, retry, fuel} /\
    seedbuf{2} = seedbuf0 /\ mat{2} = mat0 /\ avec{2} = avec0 /\
    s1{2} = s10 /\ s2{2} = s20 /\ bp{2} = bp0 /\
    s1hatp{2} = s1hat0 /\ counter{2} = counter0 /\
    retry{2} = retry0 /\ fuel{2} = fuel0 /\ 0 <= fuel0 /\
    checked_mode2_retry_tail_state
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0
      retry0 counter0 W64.one /\
    checked_mode2_retry_window_progress
      seedbuf0 retry0 fuel0 eta_limits
    ==>
    res{1} = res{2} /\
    checked_mode2_bounded_retry_tail_post
      seedbuf0 mat0 avec0 retry0 fuel0 res{2}].
proof.
conseq
  (: ={seedbuf, mat, avec, s1, s2, bp, s1hatp,
       counter, retry, fuel} ==> ={res})
  _
  (checked_mode2_bounded_retry_tail_correct
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
    retry0 fuel0 eta_limits) => //=.
by proc; sim.
qed.

lemma checked_mode2_bounded_retry_tail_only_equiv :
  equiv [BoundedTail.run ~ CheckedMode2BoundedRetryTailOnly.run :
    ={seedbuf, mat, avec, s1, s2, bp, s1hatp,
      counter, retry, fuel}
    ==>
    ={res}].
proof.
proc.
inline BoundedTail.run.
sp 3 13.
seq 1 1 :
  (seedbuf{1} = seedbuf0{2} /\ mat{1} = mat0{2} /\
   avec{1} = avec0{2} /\ s1{1} = s10{2} /\
   s2{1} = s20{2} /\ bp{1} = bp0{2} /\
   s1hatp{1} = s1hatp0{2} /\ counter{1} = counter0{2} /\
   reject{1} = reject{2} /\ retry{1} = retry0{2} /\
   fuel{1} = fuel0{2} /\ steps{1} = steps{2} /\
   ! (0 < fuel{1} /\ reject{1} = W64.one) /\
   ! (0 < fuel0{2} /\ reject{2} = W64.one)).
+ while
    (seedbuf{1} = seedbuf0{2} /\ mat{1} = mat0{2} /\
     avec{1} = avec0{2} /\ s1{1} = s10{2} /\
     s2{1} = s20{2} /\ bp{1} = bp0{2} /\
     s1hatp{1} = s1hatp0{2} /\ counter{1} = counter0{2} /\
     reject{1} = reject{2} /\ retry{1} = retry0{2} /\
     fuel{1} = fuel0{2} /\ steps{1} = steps{2}).
  + wp.
    call (_ : ={arg} ==> ={res}).
    * by proc; sim.
    * auto => />.
  + auto => />.
+ auto => />.
qed.

lemma checked_mode2_bounded_retry_tail_only_small_projection
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (counter0 : W64.t) retry0 fuel0 eta_limits :
  equiv [CheckedMode2BoundedRetryTailOnly.run ~ ThenOneMore.run :
    ={seedbuf, mat, avec, s1, s2, bp, s1hatp, counter, retry, fuel} /\
    seedbuf{2} = seedbuf0 /\ mat{2} = mat0 /\ avec{2} = avec0 /\
    s1{2} = s10 /\ s2{2} = s20 /\ bp{2} = bp0 /\
    s1hatp{2} = s1hat0 /\ counter{2} = counter0 /\
    retry{2} = retry0 /\ fuel{2} = fuel0 /\ 0 <= fuel0 /\
    checked_mode2_retry_tail_state
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0
      retry0 counter0 W64.one /\
    checked_mode2_retry_window_progress
      seedbuf0 retry0 (fuel0 + 1) eta_limits
    ==>
    res{1} = res{2}.`1].
proof.
proc.
seq 1 1 :
  (tail{1} = small{2} /\
   checked_mode2_bounded_retry_tail_post
     seedbuf0 mat0 avec0 retry0 fuel0 small{2} /\
   0 <= fuel0 /\
   checked_mode2_retry_window_progress
     seedbuf0 retry0 (fuel0 + 1) eta_limits).
+ call
    (checked_mode2_bounded_retry_tail_self_post
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
      retry0 fuel0 eta_limits).
  auto => />.
  move=> hfuel _ _ _ _ _ hprogress hnowrap.
  split.
  + move=> offset hoff0 hofflt.
    apply hprogress.
    smt().
  + move=> offset hoff0 hoffle.
    apply hnowrap.
    smt().
+ ecall{2}
    (checked_mode2_retry_one_more_observer_first_ll
      seedbuf0 mat0 avec0 retry0 fuel0 eta_limits tail{1}).
  auto => />.
qed.

lemma checked_mode2_bounded_retry_tail_small_projection
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (counter0 : W64.t) retry0 fuel0 eta_limits :
  equiv [BoundedTail.run ~ ThenOneMore.run :
    ={seedbuf, mat, avec, s1, s2, bp, s1hatp, counter, retry, fuel} /\
    seedbuf{2} = seedbuf0 /\ mat{2} = mat0 /\ avec{2} = avec0 /\
    s1{2} = s10 /\ s2{2} = s20 /\ bp{2} = bp0 /\
    s1hatp{2} = s1hat0 /\ counter{2} = counter0 /\
    retry{2} = retry0 /\ fuel{2} = fuel0 /\ 0 <= fuel0 /\
    checked_mode2_retry_tail_state
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0
      retry0 counter0 W64.one /\
    checked_mode2_retry_window_progress
      seedbuf0 retry0 (fuel0 + 1) eta_limits
    ==>
    res{1} = res{2}.`1].
proof.
transitivity CheckedMode2BoundedRetryTailOnly.run
  (={seedbuf, mat, avec, s1, s2, bp, s1hatp,
     counter, retry, fuel} ==> ={res})
  (={seedbuf, mat, avec, s1, s2, bp, s1hatp, counter, retry, fuel} /\
   seedbuf{2} = seedbuf0 /\ mat{2} = mat0 /\ avec{2} = avec0 /\
   s1{2} = s10 /\ s2{2} = s20 /\ bp{2} = bp0 /\
   s1hatp{2} = s1hat0 /\ counter{2} = counter0 /\
   retry{2} = retry0 /\ fuel{2} = fuel0 /\ 0 <= fuel0 /\
   checked_mode2_retry_tail_state
     seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0
     retry0 counter0 W64.one /\
   checked_mode2_retry_window_progress
     seedbuf0 retry0 (fuel0 + 1) eta_limits
   ==>
   res{1} = res{2}.`1).
+ move=> &1 &2 *.
  exists
    (seedbuf{1}, mat{1}, avec{1}, s1{1}, s2{1},
     bp{1}, s1hatp{1}, counter{1}, retry{1}, fuel{1}).
  smt().
+ auto => />.
+ exact checked_mode2_bounded_retry_tail_only_equiv.
+ exact
    (checked_mode2_bounded_retry_tail_only_small_projection
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
      retry0 fuel0 eta_limits).
qed.

lemma checked_mode2_bounded_retry_tail_small_marginal_eq
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (counter0 : W64.t) retry0 fuel0 eta_limits &m P :
  0 <= fuel0 =>
  checked_mode2_retry_tail_state
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0
    retry0 counter0 W64.one =>
  checked_mode2_retry_window_progress
    seedbuf0 retry0 (fuel0 + 1) eta_limits =>
  Pr[BoundedTail.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       counter0, retry0, fuel0) @ &m : P res] =
  Pr[ThenOneMore.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       counter0, retry0, fuel0) @ &m : P res.`1].
proof.
move=> hfuel htail hwindow.
byequiv
  (checked_mode2_bounded_retry_tail_small_projection
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
    retry0 fuel0 eta_limits) => //=.
qed.

lemma checked_mode2_bounded_retry_tail_large_marginal_eq
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (counter0 : W64.t) retry0 fuel0 &m P :
  0 <= fuel0 =>
  Pr[BoundedTail.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       counter0, retry0, fuel0 + 1) @ &m : P res] =
  Pr[ThenOneMore.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       counter0, retry0, fuel0) @ &m : P res.`2].
proof.
move=> hfuel.
byequiv
  checked_mode2_bounded_retry_tail_succ_decomposition => //=.
qed.

lemma checked_mode2_bounded_retry_tail_then_one_more_ll
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (counter0 : W64.t) retry0 fuel0 eta_limits :
  phoare [ThenOneMore.run :
    seedbuf = seedbuf0 /\ mat = mat0 /\ avec = avec0 /\
    s1 = s10 /\ s2 = s20 /\ bp = bp0 /\ s1hatp = s1hat0 /\
    counter = counter0 /\ retry = retry0 /\ fuel = fuel0 /\
    0 <= fuel0 /\
    checked_mode2_retry_tail_state
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0
      retry0 counter0 W64.one /\
    checked_mode2_retry_window_progress
      seedbuf0 retry0 (fuel0 + 1) eta_limits
    ==>
    checked_mode2_bounded_retry_tail_post
      seedbuf0 mat0 avec0 retry0 fuel0 res.`1 /\
    checked_mode2_bounded_retry_tail_post
      seedbuf0 mat0 avec0 retry0 (fuel0 + 1) res.`2 /\
    (checked_mode2_bounded_retry_tail_rejected_exhaustion
       (fuel0 + 1) res.`2 =>
     checked_mode2_bounded_retry_tail_rejected_exhaustion
       fuel0 res.`1)] = 1%r.
proof.
proc.
seq 1 :
  (0 <= fuel0 /\
   checked_mode2_retry_window_progress
     seedbuf0 retry0 (fuel0 + 1) eta_limits /\
   checked_mode2_bounded_retry_tail_post
     seedbuf0 mat0 avec0 retry0 fuel0 small)
  1%r 1%r 0%r _ => //=.
+ call
    (checked_mode2_bounded_retry_tail_ll
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
      retry0 fuel0 eta_limits).
  auto => />.
  move=> hfuel _ _ _ _ _ hprogress hnowrap.
  split.
  + move=> offset hoff0 hofflt.
    apply hprogress.
    smt().
  + move=> offset hoff0 hoffle.
    apply hnowrap.
    smt().
+ exlim small => small0.
  call
    (checked_mode2_retry_one_more_observer_first_ll
      seedbuf0 mat0 avec0 retry0 fuel0 eta_limits small0).
  auto => />.
+ call
    (checked_mode2_bounded_retry_tail_post_complement0
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
      retry0 fuel0 eta_limits).
  auto => />.
  move=> hfuel _ _ _ _ _ hprogress hnowrap.
  split.
  + move=> offset hoff0 hofflt.
    apply hprogress.
    smt().
  + move=> offset hoff0 hoffle.
    apply hnowrap.
    smt().
qed.

end Mode2FaithfulSecurityBoundedRetryTailSmallProjectionPostFreeze.
