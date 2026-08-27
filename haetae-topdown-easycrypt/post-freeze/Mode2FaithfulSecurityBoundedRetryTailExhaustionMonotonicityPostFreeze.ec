require import AllCore Distr Real StdOrder.

from Jasmin require import JModel_x86.

require import BArray128 BArray8192 BArray32768.
require import Mode2FaithfulSecurityRetryTailInvariantPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailPostFreeze
               Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze
               Mode2FaithfulSecurityBoundedRetryTailSmallProjectionPostFreeze.

theory Mode2FaithfulSecurityBoundedRetryTailExhaustionMonotonicityPostFreeze.

import RealOrder.
import Mode2FaithfulSecurityRetryTailInvariantPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailPostFreeze.
import Mode2FaithfulSecurityBoundedKeygenFuelPrefixPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze.
import Mode2FaithfulSecurityBoundedRetryTailSmallProjectionPostFreeze.

module BoundedTail =
  Mode2FaithfulSecurityBoundedRetryTailPostFreeze
    .CheckedMode2BoundedRetryTail.

module ThenOneMore =
  Mode2FaithfulSecurityBoundedRetryTailSuccDecompositionPostFreeze
    .CheckedMode2BoundedRetryTailThenOneMore.

(* This layer combines the two certified marginals with the one-more event
   implication.  It proves monotonicity of the actual bounded-tail exhaustion
   mass only.  It does not claim a strict contraction factor, retry
   independence, unbounded termination, packing, full key generation, or
   equality with [HAETAE.kg]. *)

op checked_mode2_bounded_retry_tail_then_one_more_good
    seedbuf0 mat0 avec0 retry0 fuel0
    (pair : checked_mode2_retry_one_more_pair) : bool =
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 fuel0 pair.`1 /\
  checked_mode2_bounded_retry_tail_post
    seedbuf0 mat0 avec0 retry0 (fuel0 + 1) pair.`2 /\
  (checked_mode2_bounded_retry_tail_rejected_exhaustion
     (fuel0 + 1) pair.`2 =>
   checked_mode2_bounded_retry_tail_rejected_exhaustion
     fuel0 pair.`1).

lemma mu_or_zero_le (x y z : real) :
  y = 0%r => 0%r <= z => x + y - z <= x.
proof.
move=> -> hz.
smt().
qed.

lemma checked_mode2_bounded_retry_tail_then_one_more_good_ll
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
    checked_mode2_bounded_retry_tail_then_one_more_good
      seedbuf0 mat0 avec0 retry0 fuel0 res] = 1%r.
proof.
conseq
  (checked_mode2_bounded_retry_tail_then_one_more_ll
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
    retry0 fuel0 eta_limits) => //=.
qed.

lemma checked_mode2_bounded_retry_tail_then_one_more_good_complement0
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
    ! checked_mode2_bounded_retry_tail_then_one_more_good
        seedbuf0 mat0 avec0 retry0 fuel0 res] = 0%r.
proof.
bypr=> &m hpre.
have hgood :
  Pr[ThenOneMore.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m :
     checked_mode2_bounded_retry_tail_then_one_more_good
       seedbuf0 mat0 avec0 retry0 fuel0 res] = 1%r.
+ by byphoare
    (checked_mode2_bounded_retry_tail_then_one_more_good_ll
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
      retry0 fuel0 eta_limits) => //.
have hpartition :
  Pr[ThenOneMore.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m :
     checked_mode2_bounded_retry_tail_then_one_more_good
       seedbuf0 mat0 avec0 retry0 fuel0 res] +
  Pr[ThenOneMore.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m :
     ! checked_mode2_bounded_retry_tail_then_one_more_good
         seedbuf0 mat0 avec0 retry0 fuel0 res] =
  Pr[ThenOneMore.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m : true].
+ rewrite Pr[mu_not].
  ring.
have htotal_bound :
  0%r <=
    Pr[ThenOneMore.run(
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
    Pr[ThenOneMore.run(
         seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
         bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m :
       ! checked_mode2_bounded_retry_tail_then_one_more_good
           seedbuf0 mat0 avec0 retry0 fuel0 res]
  <= 1%r.
+ rewrite hsum.
  exact htotal_le.
have hbad_le0 :
  Pr[ThenOneMore.run(
       seedbuf{m}, mat{m}, avec{m}, s1{m}, s2{m},
       bp{m}, s1hatp{m}, counter{m}, retry{m}, fuel{m}) @ &m :
     ! checked_mode2_bounded_retry_tail_then_one_more_good
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

lemma checked_mode2_bounded_retry_tail_then_one_more_exhaustion_le
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (counter0 : W64.t) retry0 fuel0 eta_limits &m :
  0 <= fuel0 =>
  checked_mode2_retry_tail_state
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0
    retry0 counter0 W64.one =>
  checked_mode2_retry_window_progress
    seedbuf0 retry0 (fuel0 + 1) eta_limits =>
  Pr[ThenOneMore.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       counter0, retry0, fuel0) @ &m :
     checked_mode2_bounded_retry_tail_rejected_exhaustion
       (fuel0 + 1) res.`2] <=
  Pr[ThenOneMore.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       counter0, retry0, fuel0) @ &m :
     checked_mode2_bounded_retry_tail_rejected_exhaustion
       fuel0 res.`1].
proof.
move=> hfuel htail hwindow.
have hbad0 :
  Pr[ThenOneMore.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       counter0, retry0, fuel0) @ &m :
     ! checked_mode2_bounded_retry_tail_then_one_more_good
         seedbuf0 mat0 avec0 retry0 fuel0 res] = 0%r.
+ by byphoare
    (checked_mode2_bounded_retry_tail_then_one_more_good_complement0
      seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
      retry0 fuel0 eta_limits) => //.
apply
  (ler_trans
    (Pr[ThenOneMore.run(
          seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
          counter0, retry0, fuel0) @ &m :
        checked_mode2_bounded_retry_tail_rejected_exhaustion
          fuel0 res.`1 \/
        ! checked_mode2_bounded_retry_tail_then_one_more_good
            seedbuf0 mat0 avec0 retry0 fuel0 res])).
+ rewrite Pr[mu_sub]
          /checked_mode2_bounded_retry_tail_then_one_more_good.
  smt().
trivial.
rewrite Pr[mu_or].
apply (mu_or_zero_le _ _ _ hbad0).
by rewrite Pr[mu_ge0].
qed.

lemma checked_mode2_bounded_retry_tail_exhaustion_mass_prefix
    (seedbuf0 : BArray128.t)
    (mat0 : BArray32768.t)
    (avec0 s10 s20 bp0 s1hat0 : BArray8192.t)
    (counter0 : W64.t) retry0 fuel0 eta_limits &m :
  0 <= fuel0 =>
  checked_mode2_retry_tail_state
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0
    retry0 counter0 W64.one =>
  checked_mode2_retry_window_progress
    seedbuf0 retry0 (fuel0 + 1) eta_limits =>
  Pr[BoundedTail.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       counter0, retry0, fuel0 + 1) @ &m :
     checked_mode2_bounded_retry_tail_rejected_exhaustion
       (fuel0 + 1) res] <=
  Pr[BoundedTail.run(
       seedbuf0, mat0, avec0, s10, s20, bp0, s1hat0,
       counter0, retry0, fuel0) @ &m :
     checked_mode2_bounded_retry_tail_rejected_exhaustion
       fuel0 res].
proof.
move=> hfuel htail hwindow.
have hlarge :=
  checked_mode2_bounded_retry_tail_large_marginal_eq
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
    retry0 fuel0 &m
    (fun result =>
      checked_mode2_bounded_retry_tail_rejected_exhaustion
        (fuel0 + 1) result) hfuel.
have hsmall :=
  checked_mode2_bounded_retry_tail_small_marginal_eq
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
    retry0 fuel0 eta_limits &m
    (fun result =>
      checked_mode2_bounded_retry_tail_rejected_exhaustion
        fuel0 result) hfuel htail hwindow.
have hpair :=
  checked_mode2_bounded_retry_tail_then_one_more_exhaustion_le
    seedbuf0 mat0 avec0 s10 s20 bp0 s1hat0 counter0
    retry0 fuel0 eta_limits &m hfuel htail hwindow.
rewrite hlarge hsmall.
exact hpair.
qed.

end Mode2FaithfulSecurityBoundedRetryTailExhaustionMonotonicityPostFreeze.
