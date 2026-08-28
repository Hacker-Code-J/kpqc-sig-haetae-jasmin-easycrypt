require import AllCore Distr FSet IntDiv List Mu_mem Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTAccumulatorProbability
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotTailPostFreeze.

import RealOrder Bigreal Bigreal.BRM RField.
import
  KeygenM23SingularFFTAccumulatorProbability
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTFourthMomentPostFreeze
  Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotTailPostFreeze.

theory Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotUnionPostFreeze.

(* This file restricts the accumulator coordinate headroom union bound to the
   finalized-[s2] rows only.  It keeps the fixed-context real/imaginary
   Markov4 right-hand sides exact and symbolic, but does not certify [s1]
   slots, random contexts, all-five-slot joint events, actual FFT behavior,
   eighth moments, or any numeric security level. *)

op ideal_mode2_s2_coordinate_site_set : (int * int) fset =
  product
    (rangeset 0 KeygenM23SingularFFTSpec.mode2_s2_count_i)
    (rangeset 0 KeygenM23SingularSpec.singular_words_i).

op ideal_mode2_accumulator_s2_slot_real_bad_at
    (sample : mode2_accumulator_sample) (row k : int) : bool =
  mode2_accumulator_coordinate_real_bad_at sample
    (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k.

op ideal_mode2_accumulator_s2_slot_imag_bad_at
    (sample : mode2_accumulator_sample) (row k : int) : bool =
  mode2_accumulator_coordinate_imag_bad_at sample
    (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k.

op ideal_mode2_accumulator_s2_slot_headroom_bad_at
    (sample : mode2_accumulator_sample) (row k : int) : bool =
  ideal_mode2_accumulator_s2_slot_real_bad_at sample row k \/
  ideal_mode2_accumulator_s2_slot_imag_bad_at sample row k.

op ideal_mode2_accumulator_s2_slot_real_bad
    (sample : mode2_accumulator_sample) : bool =
  exists rk,
    rk \in ideal_mode2_s2_coordinate_site_set /\
    ideal_mode2_accumulator_s2_slot_real_bad_at sample rk.`1 rk.`2.

op ideal_mode2_accumulator_s2_slot_imag_bad
    (sample : mode2_accumulator_sample) : bool =
  exists rk,
    rk \in ideal_mode2_s2_coordinate_site_set /\
    ideal_mode2_accumulator_s2_slot_imag_bad_at sample rk.`1 rk.`2.

op ideal_mode2_accumulator_s2_slot_headroom_bad
    (sample : mode2_accumulator_sample) : bool =
  exists rk,
    rk \in ideal_mode2_s2_coordinate_site_set /\
    ideal_mode2_accumulator_s2_slot_headroom_bad_at sample rk.`1 rk.`2.

op ideal_mode2_accumulator_s2_slot_real_markov4_rhs
    (pre_bp avec : BArray8192.t) (row k : int) : real =
  ideal_final_s2_row_residual_re_profile4 pre_bp avec row k 256 /
  (ideal_final_s2_full_row_residual_real_headroom pre_bp avec row k ^ 4).

op ideal_mode2_accumulator_s2_slot_imag_markov4_rhs
    (pre_bp avec : BArray8192.t) (row k : int) : real =
  ideal_final_s2_row_residual_im_profile4 pre_bp avec row k 256 /
  (ideal_final_s2_full_row_residual_imag_headroom pre_bp avec row k ^ 4).

op ideal_mode2_accumulator_s2_slot_headroom_markov4_rhs
    (pre_bp avec : BArray8192.t) (row k : int) : real =
  ideal_mode2_accumulator_s2_slot_real_markov4_rhs pre_bp avec row k +
  ideal_mode2_accumulator_s2_slot_imag_markov4_rhs pre_bp avec row k.

op ideal_mode2_accumulator_s2_slot_headroom_markov4_row_sum
    (pre_bp avec : BArray8192.t) (row : int) : real =
  BRA.bigi predT
    (fun k =>
      ideal_mode2_accumulator_s2_slot_headroom_markov4_rhs
        pre_bp avec row k)
    0 KeygenM23SingularSpec.singular_words_i.

op ideal_mode2_accumulator_s2_slot_headroom_markov4_sum
    (pre_bp avec : BArray8192.t) : real =
  BRA.bigi predT
    (fun row =>
      ideal_mode2_accumulator_s2_slot_headroom_markov4_row_sum
        pre_bp avec row)
    0 KeygenM23SingularFFTSpec.mode2_s2_count_i.

op ideal_mode2_accumulator_rowk_range_sum
    (bd : int -> int -> real) (n row : int) : real =
  BRA.bigi predT (fun k => bd row k) 0 n.

lemma ideal_mode2_s2_coordinate_site_set_mem row k :
  (row, k) \in ideal_mode2_s2_coordinate_site_set <=>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i /\
  0 <= k < KeygenM23SingularSpec.singular_words_i.
proof.
rewrite /ideal_mode2_s2_coordinate_site_set productP !mem_rangeset /=.
smt().
qed.

lemma ideal_mode2_s2_coordinate_site_set_card :
  card ideal_mode2_s2_coordinate_site_set = 512.
proof.
rewrite /ideal_mode2_s2_coordinate_site_set
        (card_product
          (rangeset 0 KeygenM23SingularFFTSpec.mode2_s2_count_i)
          (rangeset 0 KeygenM23SingularSpec.singular_words_i))
        !card_rangeset.
rewrite /KeygenM23SingularFFTSpec.mode2_s2_count_i
        /KeygenM23SingularSpec.singular_words_i.
smt().
qed.

lemma ideal_mode2_accumulator_k_range_bad_mu_le
    (d : mode2_accumulator_sample distr)
    (p : int -> mode2_accumulator_sample -> bool)
    (bd : int -> real) n :
  0 <= n =>
  (forall k,
    0 <= k < n =>
    mu d (fun sample => p k sample) <= bd k) =>
  mu d (fun sample => exists k, 0 <= k < n /\ p k sample) <=
    BRA.bigi predT bd 0 n.
proof.
move=> hn.
elim/natind: n hn => [n hnle0|n hnge0 ih].
+ move=> hn0 hbd.
   have hmu0 :
       mu d (fun sample => exists k, 0 <= k < n /\ p k sample) = 0%r.
   + apply mu0_false => sample _.
     smt().
   have hsum0 : BRA.bigi predT bd 0 n = 0%r.
   + rewrite BRA.big_geq 1:/#.
     trivial.
   rewrite hmu0 hsum0.
   trivial.
move=> hnnext hbd.
have -> :
    mu d (fun sample => exists k, 0 <= k < n + 1 /\ p k sample) =
    mu d
      (predU
        (fun sample => p n sample)
        (fun sample => exists k, 0 <= k < n /\ p k sample)).
+ apply mu_eq => sample /=.
   smt().
have hor :
    mu d
      (predU
        (fun sample => p n sample)
        (fun sample => exists k, 0 <= k < n /\ p k sample)) <=
    mu d (fun sample => p n sample) +
    mu d (fun sample => exists k, 0 <= k < n /\ p k sample).
+ exact (mu_or_le d _ _).
rewrite (rangeSr 0 n) 1:/# BRA.big_rcons /= /predT.
have hlast :
    mu d (fun sample => p n sample) <= bd n.
+ have hnk : 0 <= n < n + 1 by smt().
  exact (hbd n hnk).
have hprev :
    mu d (fun sample => exists k, 0 <= k < n /\ p k sample) <=
    BRA.bigi predT bd 0 n.
+ apply (ih hnge0) => k hk.
   have hkn1 : 0 <= k < n + 1 by smt().
   exact (hbd k hkn1).
smt().
qed.

lemma ideal_mode2_accumulator_rowk_range_bad_mu_le
    (d : mode2_accumulator_sample distr)
    (p : int -> int -> mode2_accumulator_sample -> bool)
    (bd : int -> int -> real) m n :
  0 <= m =>
  0 <= n =>
  (forall row k,
    0 <= row < m =>
    0 <= k < n =>
    mu d (fun sample => p row k sample) <= bd row k) =>
  mu d (fun sample =>
    exists row,
      0 <= row < m /\
      exists k, 0 <= k < n /\ p row k sample) <=
    BRA.bigi predT
      (fun row => ideal_mode2_accumulator_rowk_range_sum bd n row)
      0 m.
proof.
move=> hm hn.
elim/natind: m hm => [m hmle0|m hmge0 ih].
+ move=> hm0 hbd.
   have hmu0 :
       mu d (fun sample =>
         exists row,
           0 <= row < m /\
           exists k, 0 <= k < n /\ p row k sample) = 0%r.
   + apply mu0_false => sample _.
     smt().
   have hsum0 :
       BRA.bigi predT
         (fun row => ideal_mode2_accumulator_rowk_range_sum bd n row)
         0 m = 0%r.
   + rewrite BRA.big_geq 1:/#.
     trivial.
   rewrite hmu0 hsum0.
   trivial.
move=> hmnext hbd.
have -> :
    mu d (fun sample =>
      exists row,
        0 <= row < m + 1 /\
        exists k, 0 <= k < n /\ p row k sample) =
    mu d
      (predU
        (fun sample => exists k, 0 <= k < n /\ p m k sample)
        (fun sample =>
          exists row,
            0 <= row < m /\
            exists k, 0 <= k < n /\ p row k sample)).
+ apply mu_eq => sample /=.
   smt().
have hor :
    mu d
      (predU
        (fun sample => exists k, 0 <= k < n /\ p m k sample)
        (fun sample =>
          exists row,
            0 <= row < m /\
            exists k, 0 <= k < n /\ p row k sample)) <=
    mu d (fun sample => exists k, 0 <= k < n /\ p m k sample) +
    mu d (fun sample =>
      exists row,
        0 <= row < m /\
        exists k, 0 <= k < n /\ p row k sample).
+ exact (mu_or_le d _ _).
rewrite (rangeSr 0 m) 1:/# BRA.big_rcons /= /predT.
have hrowm :
    mu d (fun sample => exists k, 0 <= k < n /\ p m k sample) <=
    ideal_mode2_accumulator_rowk_range_sum bd n m.
+ apply
    (ideal_mode2_accumulator_k_range_bad_mu_le
      d (p m) (fun k => bd m k) n hn).
   move=> k hk.
   have hmrow : 0 <= m < m + 1 by smt().
   exact (hbd m k hmrow hk).
have hprev :
    mu d (fun sample =>
      exists row,
        0 <= row < m /\
        exists k, 0 <= k < n /\ p row k sample) <=
    BRA.bigi predT
      (fun row => ideal_mode2_accumulator_rowk_range_sum bd n row)
      0 m.
+ apply (ih hmge0) => row k hrow hk.
   have hrownext : 0 <= row < m + 1 by smt().
   exact (hbd row k hrownext hk).
smt().
qed.

lemma ideal_mode2_accumulator_s2_slot_headroom_badE sample :
  ideal_mode2_accumulator_s2_slot_headroom_bad sample =
  (exists row,
    0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i /\
    exists k,
      0 <= k < KeygenM23SingularSpec.singular_words_i /\
      ideal_mode2_accumulator_s2_slot_headroom_bad_at sample row k).
proof.
apply eq_iff; split.
+ move=> [rk [hrk hbad]].
   case: rk hrk hbad => row k /=.
   rewrite ideal_mode2_s2_coordinate_site_set_mem.
   smt().
move=> [row [hrow [k [hk hbad]]]].
exists (row, k).
rewrite ideal_mode2_s2_coordinate_site_set_mem.
smt().
qed.

lemma ideal_mode2_accumulator_s2_slot_headroom_bad_mu_le_exact
    pre_bp avec :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  mu
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    ideal_mode2_accumulator_s2_slot_headroom_bad <=
  ideal_mode2_accumulator_s2_slot_headroom_markov4_sum pre_bp avec.
proof.
move=> hctx.
have -> :
    ideal_mode2_accumulator_s2_slot_headroom_bad =
    (fun sample =>
      exists row,
        0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i /\
        exists k,
          0 <= k < KeygenM23SingularSpec.singular_words_i /\
          ideal_mode2_accumulator_s2_slot_headroom_bad_at sample row k).
+ apply fun_ext => sample.
  exact (ideal_mode2_accumulator_s2_slot_headroom_badE sample).
rewrite /ideal_mode2_accumulator_s2_slot_headroom_markov4_sum.
apply
  (ideal_mode2_accumulator_rowk_range_bad_mu_le
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (fun row k sample =>
      ideal_mode2_accumulator_s2_slot_headroom_bad_at sample row k)
    (ideal_mode2_accumulator_s2_slot_headroom_markov4_rhs pre_bp avec)
    KeygenM23SingularFFTSpec.mode2_s2_count_i
    KeygenM23SingularSpec.singular_words_i).
+ rewrite /KeygenM23SingularFFTSpec.mode2_s2_count_i.
   trivial.
+ rewrite /KeygenM23SingularSpec.singular_words_i.
   trivial.
move=> row k hrow hk.
rewrite /ideal_mode2_accumulator_s2_slot_headroom_bad_at.
apply
  (mode2_accumulator_coordinate_headroom_bad_at_mu_le_split
    (Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
      .ideal_mode2_accumulator_distribution pre_bp avec)
    (KeygenM23SingularFFTSpec.mode2_s1_count_i + row) k
    (ideal_mode2_accumulator_s2_slot_real_markov4_rhs pre_bp avec row k)
    (ideal_mode2_accumulator_s2_slot_imag_markov4_rhs pre_bp avec row k)).
+ exact
     (ideal_mode2_accumulator_s2_slot_real_bad_mu_le_markov4
       pre_bp avec row k hctx hrow hk).
exact
  (ideal_mode2_accumulator_s2_slot_imag_bad_mu_le_markov4
    pre_bp avec row k hctx hrow hk).
qed.

end Mode2FaithfulSecurityIdealFinalS2AccumulatorSlotUnionPostFreeze.
