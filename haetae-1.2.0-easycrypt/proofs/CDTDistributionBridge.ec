require import AllCore IntDiv List Distr DInterval.
from Jasmin require import JModel_x86.
require import SamplerTarget CDTCorrectness CDTTermination SamplerConstants
  ReferenceConstants CDTDistributionSpec.

op cdt83_modulus : int = 2 ^ 83.

(* The literal words come from the pinned C generator. These operations
   only assemble their high and low limbs into mathematical thresholds. *)
op cdt83_reference_high (i : int) : int =
  if i < 76 then W32.to_uint (nth W32.zero reference_cdt83_hi_words i)
  else reference_cdt83_tail_hi.

op [opaque] cdt83_thresholds : int list =
  mapi (fun i low => cdt83_reference_high i * W64.modulus + W64.to_uint low)
    reference_cdt83_lo_words.

lemma cdt83_modulus_positive : 0 < cdt83_modulus.
proof. by rewrite /cdt83_modulus. qed.

lemma cdt83_thresholds_length : size cdt83_thresholds = 166.
proof. by rewrite /cdt83_thresholds size_mapi reference_cdt83_lo_length. qed.

lemma cdt83_high_reference i : 0 <= i < 166 =>
  cdt_high i = cdt83_reference_high i.
proof.
  move=> hi; rewrite /cdt_high /cdt83_reference_high.
  case (i < 76) => hhead; last by rewrite /reference_cdt83_tail_hi.
  rewrite cdt83_hi_matches_reference /reference_cdt83_hi
    BArray304.get32_of_list32 1:reference_cdt83_hi_length 1:/#.
  trivial.
qed.

lemma cdt83_low_reference i : 0 <= i < 166 =>
  cdt_low i = W64.to_uint (nth W64.zero reference_cdt83_lo_words i).
proof.
  move=> hi; rewrite /cdt_low cdt83_lo_matches_reference /reference_cdt83_lo
    BArray1328.get64_of_list64 1:reference_cdt83_lo_length 1://.
  trivial.
qed.

lemma cdt83_thresholds_nth i : 0 <= i < 166 =>
  nth 0 cdt83_thresholds i = cdt_threshold i.
proof.
  move=> hi; rewrite /cdt83_thresholds (nth_mapi W64.zero _ 0 _ i).
  + by rewrite reference_cdt83_lo_length.
  by rewrite /= /cdt_threshold (cdt83_high_reference i hi)
    (cdt83_low_reference i hi).
qed.

lemma cdt83_thresholds_actual :
  cdt83_thresholds = map cdt_threshold (iota_ 0 166).
proof.
  apply (eq_from_nth 0).
  + by rewrite cdt83_thresholds_length size_map size_iota.
  move=> i; rewrite cdt83_thresholds_length => hi.
  rewrite (cdt83_thresholds_nth i hi) (nth_map 0 0 _ i _).
  + by rewrite size_iota.
  by rewrite nth_iota 1:hi /=.
qed.

lemma cdt83_count_bridge low high :
  cdt_count low high 166 = cdt_rank cdt83_thresholds (cdt_input low high).
proof.
  by rewrite /cdt_rank cdt83_thresholds_actual count_map /preim /cdt_count.
qed.

lemma cdt83_thresholds_sorted : sorted (<=) cdt83_thresholds.
proof.
  by rewrite /cdt83_thresholds /cdt83_reference_high
    /reference_cdt83_hi_words /reference_cdt83_lo_words
    /reference_cdt83_tail_hi /mapi /=.
qed.

lemma cdt83_thresholds_strict : sorted (<) cdt83_thresholds.
proof.
  by rewrite /cdt83_thresholds /cdt83_reference_high
    /reference_cdt83_hi_words /reference_cdt83_lo_words
    /reference_cdt83_tail_hi /mapi /=.
qed.

lemma cdt83_thresholds_range :
  all (fun t => 0 <= t < cdt83_modulus) cdt83_thresholds.
proof.
  by rewrite /cdt83_thresholds /cdt83_reference_high /cdt83_modulus
    /reference_cdt83_hi_words /reference_cdt83_lo_words
    /reference_cdt83_tail_hi /mapi /=.
qed.

lemma cdt83_table_valid : cdt_valid cdt83_modulus cdt83_thresholds.
proof.
  by rewrite /cdt_valid cdt83_modulus_positive cdt83_thresholds_sorted
    cdt83_thresholds_range.
qed.

lemma cdt83_last_threshold :
  nth 0 cdt83_thresholds 165 = cdt83_modulus - 2.
proof.
  by rewrite cdt83_thresholds_nth 1:// /cdt_threshold /cdt_high /cdt_low /=
    cdt83_lo_last_word W64.of_uintK /cdt83_modulus /=.
qed.

lemma cdt83_endpoint_mass :
  cdt_bin_mass cdt83_modulus cdt83_thresholds 166 = 1%r / cdt83_modulus%r.
proof.
  by rewrite /cdt_bin_mass /cdt_bin_lower /cdt_bin_upper
    cdt83_thresholds_length /= cdt83_last_threshold /cdt83_modulus /=.
qed.

lemma cdt83_split_high_range u : 0 <= u < cdt83_modulus =>
  0 <= u %/ 18446744073709551616 < 524288.
proof.
  rewrite /cdt83_modulus /= => hu.
  have he := divz_eq u 18446744073709551616.
  have hm := modz_cmp u 18446744073709551616.
  smt().
qed.

lemma cdt83_split_input u : 0 <= u < cdt83_modulus =>
  cdt_input (W64.of_int (u %% 18446744073709551616)) (W32.of_int (u %/ 18446744073709551616)) = u.
proof.
  move=> hu; have hhigh := cdt83_split_high_range u hu.
  have hhigh32 : 0 <= u %/ 18446744073709551616 < 4294967296 by smt().
  rewrite /cdt_input W32.of_uintK W64.of_uintK /= modz_mod.
  rewrite (modz_small (u %/ 18446744073709551616) 4294967296 hhigh32).
  apply/eq_sym; exact (divz_eq u 18446744073709551616).
qed.

lemma cdt83_split_count u : 0 <= u < cdt83_modulus =>
  cdt_count (W64.of_int (u %% 18446744073709551616)) (W32.of_int (u %/ 18446744073709551616)) 166 =
    cdt_rank cdt83_thresholds u.
proof.
  by move=> hu; rewrite cdt83_count_bridge (cdt83_split_input u hu).
qed.

(* Uniformity is an explicit premise of this experiment, rather than a
   property asserted about any concrete SHAKE seed or byte stream. *)
module Uniform83Jasmin = {
  proc sample() : int = {
    var u : int;
    var output : W64.t;
    u <$ dinter 0 (cdt83_modulus - 1);
    output <@ SamplerTarget.M.sample_gauss83_jazz
      (W64.of_int (u %% 18446744073709551616), W32.of_int (u %/ 18446744073709551616));
    return W64.to_uint output;
  }
}.

lemma uniform83_jasmin_equiv :
  equiv [Uniform83Jasmin.sample ~ UniformCDT.sample :
    modulus{2} = cdt83_modulus /\ thresholds{2} = cdt83_thresholds ==> ={res}].
proof.
  proc; wp.
  ecall{1} (sample_gauss83_jazz_total
    (W64.of_int (u{1} %% 18446744073709551616)) (W32.of_int (u{1} %/ 18446744073709551616))).
  rnd; skip.
  move=> &1 &2 /= [hm ht]; rewrite hm ht /=.
  move=> u hu.
  have hurange : 0 <= u < cdt83_modulus by
    move: hu; rewrite supp_dinter; smt().
  rewrite hu /=.
  move=> result [hresult _].
  by move: hresult; rewrite (cdt83_split_count u hurange).
qed.

lemma uniform83_jasmin_probability (event : int -> bool) &m :
  Pr[Uniform83Jasmin.sample() @ &m : event res] =
  Pr[UniformCDT.sample(cdt83_modulus, cdt83_thresholds) @ &m : event res].
proof. by byequiv uniform83_jasmin_equiv. qed.

lemma uniform83_jasmin_ll : islossless Uniform83Jasmin.sample.
proof.
  proc; wp; call sample_gauss83_jazz_ll; rnd; skip; auto => />.
  apply dinter_ll; have := cdt83_modulus_positive; smt().
qed.

lemma uniform83_jasmin_supported :
  hoare [Uniform83Jasmin.sample : true ==> 0 <= res <= 166].
proof.
  proc; wp; ecall (sample_gauss83_jazz_correct
    (W64.of_int (u %% 18446744073709551616)) (W32.of_int (u %/ 18446744073709551616))).
  rnd; skip; auto => />.
qed.

lemma uniform83_jasmin_total :
  phoare [Uniform83Jasmin.sample : true ==> 0 <= res <= 166] = 1%r.
proof. by conseq uniform83_jasmin_ll uniform83_jasmin_supported. qed.

require import CDTDistribution.

lemma uniform83_jasmin_law (event : int -> bool) &m :
  Pr[Uniform83Jasmin.sample() @ &m : event res] =
    mu (cdt_distribution cdt83_modulus cdt83_thresholds) event.
proof.
  by rewrite uniform83_jasmin_probability uniform_cdt_law.
qed.

lemma uniform83_jasmin_mass k &m :
  Pr[Uniform83Jasmin.sample() @ &m : res = k] =
    cdt_bin_mass cdt83_modulus cdt83_thresholds k.
proof.
  rewrite (uniform83_jasmin_probability (fun x => x = k) &m).
  exact (uniform_cdt_probability cdt83_modulus cdt83_thresholds k &m cdt83_table_valid).
qed.

lemma cdt83_distribution_support k :
  (k \in cdt_distribution cdt83_modulus cdt83_thresholds) = (0 <= k <= 166).
proof.
  have hlast : 0 < size cdt83_thresholds =>
    nth 0 cdt83_thresholds (size cdt83_thresholds - 1) < cdt83_modulus - 1 by
    rewrite cdt83_thresholds_length /= cdt83_last_threshold; smt().
  by rewrite (cdt_distribution_full_support cdt83_modulus cdt83_thresholds k
    cdt83_table_valid cdt83_thresholds_strict hlast) cdt83_thresholds_length.
qed.

lemma uniform83_jasmin_support k &m :
  (0%r < Pr[Uniform83Jasmin.sample() @ &m : res = k]) = (0 <= k <= 166).
proof.
  rewrite uniform83_jasmin_mass
    -(cdt_distribution_mass cdt83_modulus cdt83_thresholds k cdt83_table_valid).
  exact (cdt83_distribution_support k).
qed.

lemma uniform83_jasmin_endpoint &m :
  Pr[Uniform83Jasmin.sample() @ &m : res = 166] = 1%r / (2 ^ 83)%r.
proof. by rewrite uniform83_jasmin_mass cdt83_endpoint_mass /cdt83_modulus. qed.
