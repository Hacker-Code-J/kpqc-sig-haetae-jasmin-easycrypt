require import AllCore IntDiv List FSet Distr Mu_mem Ring StdOrder Real.

from Jasmin require import JModel_x86.

require import BArray8192.
require import
  KeygenM23ComplexReal
  KeygenM23SingularSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety.

import RealOrder RField.
import
  KeygenM23ComplexReal
  KeygenM23SingularFFTAccumulatorBridge
  KeygenM23SingularFFTAccumulatorSafety.

theory KeygenM23SingularFFTAccumulatorProbability.

(* This theory is deliberately distribution-parametric.  It decomposes the
   deterministic headroom event and applies finite union bounds, but it does
   not postulate a law for the key-generation samples or numeric tail bounds. *)
type mode2_accumulator_sample = BArray8192.t * BArray8192.t.

op mode2_prefix_site_set : (int * int) fset =
  product
    (rangeset 0 (KeygenM23SingularFFTSpec.mode2_slice_count_i + 1))
    (rangeset 0 KeygenM23SingularSpec.singular_words_i).

op mode2_coordinate_site_set : (int * int) fset =
  product
    (rangeset 0 KeygenM23SingularFFTSpec.mode2_slice_count_i)
    (rangeset 0 KeygenM23SingularSpec.singular_words_i).

op mode2_accumulator_trace_headroom_bad
    (sample : mode2_accumulator_sample) : bool =
  mode2_accumulator_headroom_bad_event
    sample.`1 sample.`2
    KeygenM23SingularFFTSpec.mode2_slice_count_i.

op mode2_accumulator_prefix_lower_bad_at
    (sample : mode2_accumulator_sample) (processed j : int) : bool =
  mode2_ideal_energy_prefix sample.`1 sample.`2 processed j <
    mode2_energy_error_prefix sample.`1 sample.`2 processed j.

op mode2_accumulator_prefix_upper_bad_at
    (sample : mode2_accumulator_sample) (processed j : int) : bool =
  accumulator_q16_signed_limit <=
    mode2_ideal_energy_prefix sample.`1 sample.`2 processed j +
    mode2_energy_error_prefix sample.`1 sample.`2 processed j.

op mode2_accumulator_prefix_headroom_bad_at
    (sample : mode2_accumulator_sample) (processed j : int) : bool =
  mode2_accumulator_prefix_lower_bad_at sample processed j \/
  mode2_accumulator_prefix_upper_bad_at sample processed j.

op mode2_accumulator_coordinate_real_bad_at
    (sample : mode2_accumulator_sample) (slot j : int) : bool =
  accumulator_q16_coordinate_cap <
    `|creal (mode2_ideal_fft_at sample.`1 sample.`2 slot j)| +
      mode2_fft_endpoint_eps.

op mode2_accumulator_coordinate_imag_bad_at
    (sample : mode2_accumulator_sample) (slot j : int) : bool =
  accumulator_q16_coordinate_cap <
    `|cimag (mode2_ideal_fft_at sample.`1 sample.`2 slot j)| +
      mode2_fft_endpoint_eps.

op mode2_accumulator_coordinate_headroom_bad_at
    (sample : mode2_accumulator_sample) (slot j : int) : bool =
  mode2_accumulator_coordinate_real_bad_at sample slot j \/
  mode2_accumulator_coordinate_imag_bad_at sample slot j.

op mode2_accumulator_prefix_headroom_bad
    (sample : mode2_accumulator_sample) : bool =
  exists ij,
    ij \in mode2_prefix_site_set /\
    mode2_accumulator_prefix_headroom_bad_at sample ij.`1 ij.`2.

op mode2_accumulator_coordinate_headroom_bad
    (sample : mode2_accumulator_sample) : bool =
  exists ij,
    ij \in mode2_coordinate_site_set /\
    mode2_accumulator_coordinate_headroom_bad_at sample ij.`1 ij.`2.

lemma mu_or_le (d : mode2_accumulator_sample distr)
    (p q : mode2_accumulator_sample -> bool) :
  mu d (predU p q) <= mu d p + mu d q.
proof.
rewrite mu_or.
smt(ge0_mu).
qed.

lemma mode2_prefix_site_set_mem (processed j : int) :
  (processed, j) \in mode2_prefix_site_set <=>
  0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i /\
  0 <= j < KeygenM23SingularSpec.singular_words_i.
proof.
rewrite /mode2_prefix_site_set productP !mem_rangeset /=.
smt().
qed.

lemma mode2_coordinate_site_set_mem (slot j : int) :
  (slot, j) \in mode2_coordinate_site_set <=>
  0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i /\
  0 <= j < KeygenM23SingularSpec.singular_words_i.
proof.
rewrite /mode2_coordinate_site_set productP !mem_rangeset /=.
smt().
qed.

lemma mode2_prefix_site_set_card :
  card mode2_prefix_site_set = 1536.
proof.
rewrite /mode2_prefix_site_set
        (card_product
          (rangeset 0
            (KeygenM23SingularFFTSpec.mode2_slice_count_i + 1))
          (rangeset 0 KeygenM23SingularSpec.singular_words_i))
        !card_rangeset.
rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i
        /KeygenM23SingularSpec.singular_words_i.
smt().
qed.

lemma mode2_coordinate_site_set_card :
  card mode2_coordinate_site_set = 1280.
proof.
rewrite /mode2_coordinate_site_set
        (card_product
          (rangeset 0 KeygenM23SingularFFTSpec.mode2_slice_count_i)
          (rangeset 0 KeygenM23SingularSpec.singular_words_i))
        !card_rangeset.
rewrite /KeygenM23SingularFFTSpec.mode2_slice_count_i
        /KeygenM23SingularSpec.singular_words_i.
smt().
qed.

lemma mode2_accumulator_headroom_bad_event_cover
    (sample : mode2_accumulator_sample) :
  mode2_accumulator_trace_headroom_bad sample =>
  mode2_accumulator_prefix_headroom_bad sample \/
  mode2_accumulator_coordinate_headroom_bad sample.
proof.
rewrite /mode2_accumulator_trace_headroom_bad
        /mode2_accumulator_headroom_bad_event.
move=> [slot j [hslot [hj hbad]]].
have hslot0 : 0 <= slot by smt().
have hslot5 : slot < KeygenM23SingularFFTSpec.mode2_slice_count_i by
  smt().
have hj0 : 0 <= j by smt().
have hj256 : j < KeygenM23SingularSpec.singular_words_i by
  smt().
rewrite /mode2_accumulator_headroom_step in hbad.
rewrite /mode2_accumulator_prefix_headroom_bad
        /mode2_accumulator_coordinate_headroom_bad.
rewrite /mode2_accumulator_prefix_headroom_bad_at
        /mode2_accumulator_prefix_lower_bad_at
        /mode2_accumulator_prefix_upper_bad_at
        /mode2_accumulator_coordinate_headroom_bad_at
        /mode2_accumulator_coordinate_real_bad_at
        /mode2_accumulator_coordinate_imag_bad_at in hbad.
rewrite /mode2_accumulator_prefix_headroom
        /mode2_accumulator_coordinate_headroom in hbad.
have hprefix0 : (slot, j) \in mode2_prefix_site_set.
+ rewrite mode2_prefix_site_set_mem.
  smt().
have hprefix1 : (slot + 1, j) \in mode2_prefix_site_set.
+ rewrite mode2_prefix_site_set_mem.
  smt().
have hcoord : (slot, j) \in mode2_coordinate_site_set.
+ rewrite mode2_coordinate_site_set_mem.
  smt().
smt().
qed.

lemma mode2_accumulator_prefix_headroom_bad_mu_le
    (d : mode2_accumulator_sample distr) (delta_prefix : real) :
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu d (fun sample =>
      mode2_accumulator_prefix_headroom_bad_at sample processed j) <=
      delta_prefix) =>
  mu d mode2_accumulator_prefix_headroom_bad <=
    1536%r * delta_prefix.
proof.
move=> hprefix.
rewrite /mode2_accumulator_prefix_headroom_bad.
rewrite -mode2_prefix_site_set_card.
apply
  (mu_mem_le_gen
    mode2_prefix_site_set d
    (fun (ij : int * int) sample =>
      mode2_accumulator_prefix_headroom_bad_at sample ij.`1 ij.`2)
    delta_prefix).
move=> ij hij.
case: ij hij => processed j hij /=.
move: hij.
rewrite mode2_prefix_site_set_mem.
move=> [hprocessed hj].
exact (hprefix processed j hprocessed hj).
qed.

lemma mode2_accumulator_coordinate_headroom_bad_mu_le
    (d : mode2_accumulator_sample distr) (delta_coord : real) :
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu d (fun sample =>
      mode2_accumulator_coordinate_headroom_bad_at sample slot j) <=
      delta_coord) =>
  mu d mode2_accumulator_coordinate_headroom_bad <=
    1280%r * delta_coord.
proof.
move=> hcoord.
rewrite /mode2_accumulator_coordinate_headroom_bad.
rewrite -mode2_coordinate_site_set_card.
apply
  (mu_mem_le_gen
    mode2_coordinate_site_set d
    (fun (ij : int * int) sample =>
      mode2_accumulator_coordinate_headroom_bad_at sample ij.`1 ij.`2)
    delta_coord).
move=> ij hij.
case: ij hij => slot j hij /=.
move: hij.
rewrite mode2_coordinate_site_set_mem.
move=> [hslot hj].
exact (hcoord slot j hslot hj).
qed.

lemma mode2_accumulator_headroom_bad_event_mu_le
    (d : mode2_accumulator_sample distr)
    (delta_prefix delta_coord : real) :
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu d (fun sample =>
      mode2_accumulator_prefix_headroom_bad_at sample processed j) <=
      delta_prefix) =>
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu d (fun sample =>
      mode2_accumulator_coordinate_headroom_bad_at sample slot j) <=
      delta_coord) =>
  mu d mode2_accumulator_trace_headroom_bad <=
    1536%r * delta_prefix + 1280%r * delta_coord.
proof.
move=> hprefix hcoord.
apply (ler_trans
         (mu d mode2_accumulator_prefix_headroom_bad +
          mu d mode2_accumulator_coordinate_headroom_bad)).
+ apply
    (ler_trans
      (mu d
        (predU
          mode2_accumulator_prefix_headroom_bad
          mode2_accumulator_coordinate_headroom_bad))).
  + apply mu_sub => sample.
    exact (mode2_accumulator_headroom_bad_event_cover sample).
  exact (mu_or_le d _ _).
have hprefix_bound :=
  mode2_accumulator_prefix_headroom_bad_mu_le d delta_prefix hprefix.
have hcoord_bound :=
  mode2_accumulator_coordinate_headroom_bad_mu_le d delta_coord hcoord.
smt().
qed.

lemma mode2_accumulator_prefix_headroom_bad_at_mu_le_split
    (d : mode2_accumulator_sample distr)
    (processed j : int) (delta_lower delta_upper : real) :
  mu d (fun sample =>
    mode2_accumulator_prefix_lower_bad_at sample processed j) <=
    delta_lower =>
  mu d (fun sample =>
    mode2_accumulator_prefix_upper_bad_at sample processed j) <=
    delta_upper =>
  mu d (fun sample =>
    mode2_accumulator_prefix_headroom_bad_at sample processed j) <=
    delta_lower + delta_upper.
proof.
move=> hlower hupper.
rewrite /mode2_accumulator_prefix_headroom_bad_at.
apply (ler_trans
         (mu d (fun sample =>
            mode2_accumulator_prefix_lower_bad_at sample processed j) +
          mu d (fun sample =>
            mode2_accumulator_prefix_upper_bad_at sample processed j))).
+ exact (mu_or_le d _ _).
smt().
qed.

lemma mode2_accumulator_coordinate_headroom_bad_at_mu_le_split
    (d : mode2_accumulator_sample distr)
    (slot j : int) (delta_real delta_imag : real) :
  mu d (fun sample =>
    mode2_accumulator_coordinate_real_bad_at sample slot j) <=
    delta_real =>
  mu d (fun sample =>
    mode2_accumulator_coordinate_imag_bad_at sample slot j) <=
    delta_imag =>
  mu d (fun sample =>
    mode2_accumulator_coordinate_headroom_bad_at sample slot j) <=
    delta_real + delta_imag.
proof.
move=> hreal himag.
rewrite /mode2_accumulator_coordinate_headroom_bad_at.
apply (ler_trans
         (mu d (fun sample =>
            mode2_accumulator_coordinate_real_bad_at sample slot j) +
          mu d (fun sample =>
            mode2_accumulator_coordinate_imag_bad_at sample slot j))).
+ exact (mu_or_le d _ _).
smt().
qed.

lemma mode2_accumulator_headroom_bad_event_mu_le_split
    (d : mode2_accumulator_sample distr)
    (delta_lower delta_upper delta_real delta_imag : real) :
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu d (fun sample =>
      mode2_accumulator_prefix_lower_bad_at sample processed j) <=
      delta_lower) =>
  (forall processed j,
    0 <= processed <= KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu d (fun sample =>
      mode2_accumulator_prefix_upper_bad_at sample processed j) <=
      delta_upper) =>
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu d (fun sample =>
      mode2_accumulator_coordinate_real_bad_at sample slot j) <=
      delta_real) =>
  (forall slot j,
    0 <= slot < KeygenM23SingularFFTSpec.mode2_slice_count_i =>
    0 <= j < KeygenM23SingularSpec.singular_words_i =>
    mu d (fun sample =>
      mode2_accumulator_coordinate_imag_bad_at sample slot j) <=
      delta_imag) =>
  mu d mode2_accumulator_trace_headroom_bad <=
    1536%r * (delta_lower + delta_upper) +
    1280%r * (delta_real + delta_imag).
proof.
move=> hlower hupper hreal himag.
apply (mode2_accumulator_headroom_bad_event_mu_le
         d (delta_lower + delta_upper) (delta_real + delta_imag)).
+ move=> processed j hprocessed hj.
  apply (mode2_accumulator_prefix_headroom_bad_at_mu_le_split
           d processed j delta_lower delta_upper).
  + exact (hlower processed j hprocessed hj).
  exact (hupper processed j hprocessed hj).
+ move=> slot j hslot hj.
  apply (mode2_accumulator_coordinate_headroom_bad_at_mu_le_split
           d slot j delta_real delta_imag).
  + exact (hreal slot j hslot hj).
  exact (himag slot j hslot hj).
qed.

end KeygenM23SingularFFTAccumulatorProbability.
