require import
  AllCore DList Distr IntDiv List Mu_mem Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenEtaSamplerSpec
  KeygenSamplerCallersSpec
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze.

import RealOrder.

theory Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze.

(* This theory lifts the ideal eta polynomial law to the mode-2 3+2 secret
   shape.  Its second component is sampled_s2 before avec/finalize, not the
   accumulator's final_s2.  The product law is an ideal-randomness statement;
   the deterministic SHAKE nonce streams remain outside this iid boundary. *)

type ideal_eta_secret_pair = int list list * int list list.
type ideal_eta_packed_secret_pair = BArray8192.t * BArray8192.t.

op ideal_eta_s1_distribution : int list list distr =
  dlist
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_polynomial_distribution
    KeygenSamplerCallersSpec.mode2_m_i.

op ideal_eta_s2_distribution : int list list distr =
  dlist
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_polynomial_distribution
    KeygenSamplerCallersSpec.mode2_k_i.

op ideal_eta_secret_pair_distribution : ideal_eta_secret_pair distr =
  ideal_eta_s1_distribution `*` ideal_eta_s2_distribution.

op ideal_eta_decoded_s1_distribution : int list list distr =
  dlist
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_decoded_polynomial_distribution
    KeygenSamplerCallersSpec.mode2_m_i.

op ideal_eta_decoded_s2_distribution : int list list distr =
  dlist
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_decoded_polynomial_distribution
    KeygenSamplerCallersSpec.mode2_k_i.

op ideal_eta_decoded_secret_pair_distribution :
    ideal_eta_secret_pair distr =
  ideal_eta_decoded_s1_distribution `*`
    ideal_eta_decoded_s2_distribution.

op eta_vector_word_capacity_i : int = BArray8192.size %/ 4.

op eta_padded_word_list (coefficients : int list) : W32.t list =
  map W32.of_int coefficients ++
    nseq (eta_vector_word_capacity_i - size coefficients) W32.zero.

op pack_eta_coefficients8192 (coefficients : int list) : BArray8192.t =
  BArray8192.of_list32 (eta_padded_word_list coefficients).

op pack_eta_vector8192 (polynomials : int list list) : BArray8192.t =
  pack_eta_coefficients8192 (flatten polynomials).

op pack_eta_secret_pair
    (pair : ideal_eta_secret_pair) : ideal_eta_packed_secret_pair =
  (pack_eta_vector8192 pair.`1, pack_eta_vector8192 pair.`2).

op ideal_eta_packed_secret_pair_distribution :
    ideal_eta_packed_secret_pair distr =
  dmap ideal_eta_secret_pair_distribution pack_eta_secret_pair.

op ideal_eta_decoded_packed_secret_pair_distribution :
    ideal_eta_packed_secret_pair distr =
  dmap ideal_eta_decoded_secret_pair_distribution pack_eta_secret_pair.

op ideal_eta_packed_secret_pair_valid
    (sample : ideal_eta_packed_secret_pair) : bool =
  exists pair,
    pair \in ideal_eta_secret_pair_distribution /\
    sample = pack_eta_secret_pair pair.

lemma mode2_first_attempt_retry_counter_zero :
  KeygenSamplerCallersSpec.mode2_retry_counter_i 0 = 0.
proof.
by rewrite
  /KeygenSamplerCallersSpec.mode2_retry_counter_i
  /KeygenSamplerCallersSpec.mode2_retry_span_i.
qed.

lemma mode2_first_attempt_eta_nonce slot :
  0 <= slot <
    KeygenSamplerCallersSpec.mode2_m_i +
      KeygenSamplerCallersSpec.mode2_k_i =>
  KeygenSamplerCallersSpec.mode2_eta_nonce_i 0 slot = slot.
proof.
move=> hslot.
rewrite
  /KeygenSamplerCallersSpec.mode2_eta_nonce_i
  /KeygenSamplerCallersSpec.mode2_retry_counter_i.
ring.
qed.

lemma mode2_first_attempt_s1_nonce slot :
  0 <= slot < KeygenSamplerCallersSpec.mode2_m_i =>
  KeygenSamplerCallersSpec.mode2_eta_nonce_i 0 slot = slot.
proof.
move=> hslot.
apply mode2_first_attempt_eta_nonce.
rewrite
  /KeygenSamplerCallersSpec.mode2_m_i
  /KeygenSamplerCallersSpec.mode2_k_i in hslot.
rewrite
  /KeygenSamplerCallersSpec.mode2_m_i
  /KeygenSamplerCallersSpec.mode2_k_i.
smt().
qed.

lemma mode2_first_attempt_s2_nonce slot :
  0 <= slot < KeygenSamplerCallersSpec.mode2_k_i =>
  KeygenSamplerCallersSpec.mode2_eta_nonce_i
    0 (KeygenSamplerCallersSpec.mode2_m_i + slot) =
  KeygenSamplerCallersSpec.mode2_m_i + slot.
proof.
move=> hslot.
apply mode2_first_attempt_eta_nonce.
rewrite
  /KeygenSamplerCallersSpec.mode2_m_i
  /KeygenSamplerCallersSpec.mode2_k_i in hslot.
rewrite
  /KeygenSamplerCallersSpec.mode2_m_i
  /KeygenSamplerCallersSpec.mode2_k_i.
smt().
qed.

lemma mode2_first_attempt_eta_nonce_segments_disjoint s1_slot s2_slot :
  0 <= s1_slot < KeygenSamplerCallersSpec.mode2_m_i =>
  0 <= s2_slot < KeygenSamplerCallersSpec.mode2_k_i =>
  KeygenSamplerCallersSpec.mode2_eta_nonce_i 0 s1_slot <
  KeygenSamplerCallersSpec.mode2_eta_nonce_i
    0 (KeygenSamplerCallersSpec.mode2_m_i + s2_slot).
proof.
move=> hs1 hs2.
rewrite
  (mode2_first_attempt_s1_nonce s1_slot hs1)
  (mode2_first_attempt_s2_nonce s2_slot hs2).
rewrite /KeygenSamplerCallersSpec.mode2_m_i in hs1.
rewrite /KeygenSamplerCallersSpec.mode2_m_i.
smt().
qed.

lemma ideal_eta_s1_lossless : is_lossless ideal_eta_s1_distribution.
proof.
rewrite /ideal_eta_s1_distribution.
apply dlist_ll.
exact
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_polynomial_lossless.
qed.

lemma ideal_eta_s2_lossless : is_lossless ideal_eta_s2_distribution.
proof.
rewrite /ideal_eta_s2_distribution.
apply dlist_ll.
exact
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_polynomial_lossless.
qed.

lemma ideal_eta_secret_pair_lossless :
  is_lossless ideal_eta_secret_pair_distribution.
proof.
rewrite /ideal_eta_secret_pair_distribution dprod_ll.
split.
+ exact ideal_eta_s1_lossless.
exact ideal_eta_s2_lossless.
qed.

lemma ideal_eta_s1_uniform : is_uniform ideal_eta_s1_distribution.
proof.
rewrite /ideal_eta_s1_distribution.
apply dlist_uni.
exact
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_polynomial_uniform.
qed.

lemma ideal_eta_s2_uniform : is_uniform ideal_eta_s2_distribution.
proof.
rewrite /ideal_eta_s2_distribution.
apply dlist_uni.
exact
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_polynomial_uniform.
qed.

lemma ideal_eta_secret_pair_uniform :
  is_uniform ideal_eta_secret_pair_distribution.
proof.
rewrite /ideal_eta_secret_pair_distribution.
apply dprod_uni.
+ exact ideal_eta_s1_uniform.
exact ideal_eta_s2_uniform.
qed.

lemma ideal_eta_s1_support s1 :
  s1 \in ideal_eta_s1_distribution <=>
  size s1 = KeygenSamplerCallersSpec.mode2_m_i /\
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    s1.
proof.
rewrite /ideal_eta_s1_distribution supp_dlist.
+ by rewrite /KeygenSamplerCallersSpec.mode2_m_i.
trivial.
qed.

lemma ideal_eta_s2_support s2 :
  s2 \in ideal_eta_s2_distribution <=>
  size s2 = KeygenSamplerCallersSpec.mode2_k_i /\
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    s2.
proof.
rewrite /ideal_eta_s2_distribution supp_dlist.
+ by rewrite /KeygenSamplerCallersSpec.mode2_k_i.
trivial.
qed.

lemma ideal_eta_secret_pair_support pair :
  pair \in ideal_eta_secret_pair_distribution <=>
  size pair.`1 = KeygenSamplerCallersSpec.mode2_m_i /\
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    pair.`1 /\
  size pair.`2 = KeygenSamplerCallersSpec.mode2_k_i /\
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    pair.`2.
proof.
rewrite
  /ideal_eta_secret_pair_distribution supp_dprod
  ideal_eta_s1_support ideal_eta_s2_support.
smt().
qed.

lemma ideal_eta_vector_point polynomials count :
  0 <= count =>
  size polynomials = count =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    polynomials =>
  mu1
    (dlist
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution
      count)
    polynomials =
  (1%r / 3%r) ^
    (KeygenEtaSamplerSpec.eta_poly_words_i * count).
proof.
move=> hcount hsize hall.
have hpoint : forall polynomial, polynomial \in polynomials =>
  mu1
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_polynomial_distribution
    polynomial =
  (1%r / 3%r) ^ KeygenEtaSamplerSpec.eta_poly_words_i.
+ move=> polynomial hpolynomial.
  have hsupport : polynomial \in
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_polynomial_distribution.
  + move: hall; rewrite allP => hall.
    exact (hall polynomial hpolynomial).
  rewrite
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_polynomial_support in hsupport.
  move: hsupport => [hpoly_size hpoly_all].
  exact
    (Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_polynomial_point
      polynomial hpoly_size hpoly_all).
have h :=
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze.dlist_exact_point
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_polynomial_distribution
    ((1%r / 3%r) ^ KeygenEtaSamplerSpec.eta_poly_words_i)
    polynomials hpoint.
rewrite hsize in h.
rewrite -RField.exprM in h.
exact h.
qed.

lemma ideal_eta_s1_point s1 :
  size s1 = KeygenSamplerCallersSpec.mode2_m_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    s1 =>
  mu1 ideal_eta_s1_distribution s1 =
  (1%r / 3%r) ^
    (KeygenEtaSamplerSpec.eta_poly_words_i *
      KeygenSamplerCallersSpec.mode2_m_i).
proof.
move=> hsize hall.
rewrite /ideal_eta_s1_distribution.
apply ideal_eta_vector_point.
+ by rewrite /KeygenSamplerCallersSpec.mode2_m_i.
+ exact hsize.
exact hall.
qed.

lemma ideal_eta_s2_point s2 :
  size s2 = KeygenSamplerCallersSpec.mode2_k_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    s2 =>
  mu1 ideal_eta_s2_distribution s2 =
  (1%r / 3%r) ^
    (KeygenEtaSamplerSpec.eta_poly_words_i *
      KeygenSamplerCallersSpec.mode2_k_i).
proof.
move=> hsize hall.
rewrite /ideal_eta_s2_distribution.
apply ideal_eta_vector_point.
+ by rewrite /KeygenSamplerCallersSpec.mode2_k_i.
+ exact hsize.
exact hall.
qed.

lemma ideal_eta_secret_pair_point (pair : ideal_eta_secret_pair) :
  size pair.`1 = KeygenSamplerCallersSpec.mode2_m_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    pair.`1 =>
  size pair.`2 = KeygenSamplerCallersSpec.mode2_k_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    pair.`2 =>
  mu1 ideal_eta_secret_pair_distribution pair =
  (1%r / 3%r) ^
    (KeygenEtaSamplerSpec.eta_poly_words_i *
      (KeygenSamplerCallersSpec.mode2_m_i +
        KeygenSamplerCallersSpec.mode2_k_i)).
proof.
case: pair => s1 s2 /=.
move=> hs1size hs1all hs2size hs2all.
rewrite /ideal_eta_secret_pair_distribution dprod1E.
rewrite
  (ideal_eta_s1_point s1 hs1size hs1all)
  (ideal_eta_s2_point s2 hs2size hs2all).
rewrite
  /KeygenEtaSamplerSpec.eta_poly_words_i
  /KeygenSamplerCallersSpec.mode2_m_i
  /KeygenSamplerCallersSpec.mode2_k_i.
rewrite -RField.exprD_nneg 1:/# 1:/#.
congr; ring.
qed.

lemma ideal_eta_secret_pair_point_mode2 (pair : ideal_eta_secret_pair) :
  size pair.`1 = KeygenSamplerCallersSpec.mode2_m_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    pair.`1 =>
  size pair.`2 = KeygenSamplerCallersSpec.mode2_k_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    pair.`2 =>
  mu1 ideal_eta_secret_pair_distribution pair =
    (1%r / 3%r) ^ 1280.
proof.
move=> hs1size hs1all hs2size hs2all.
rewrite
  (ideal_eta_secret_pair_point
    pair hs1size hs1all hs2size hs2all).
rewrite
  /KeygenEtaSamplerSpec.eta_poly_words_i
  /KeygenSamplerCallersSpec.mode2_m_i
  /KeygenSamplerCallersSpec.mode2_k_i.
trivial.
qed.

lemma ideal_eta_decoded_s1_eq_iid :
  ideal_eta_decoded_s1_distribution = ideal_eta_s1_distribution.
proof.
rewrite
  /ideal_eta_decoded_s1_distribution
  /ideal_eta_s1_distribution
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_decoded_polynomial_eq_iid.
trivial.
qed.

lemma ideal_eta_decoded_s2_eq_iid :
  ideal_eta_decoded_s2_distribution = ideal_eta_s2_distribution.
proof.
rewrite
  /ideal_eta_decoded_s2_distribution
  /ideal_eta_s2_distribution
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_decoded_polynomial_eq_iid.
trivial.
qed.

lemma ideal_eta_decoded_secret_pair_eq_iid :
  ideal_eta_decoded_secret_pair_distribution =
  ideal_eta_secret_pair_distribution.
proof.
rewrite
  /ideal_eta_decoded_secret_pair_distribution
  /ideal_eta_secret_pair_distribution
  ideal_eta_decoded_s1_eq_iid
  ideal_eta_decoded_s2_eq_iid.
trivial.
qed.

lemma ideal_eta_decoded_secret_pair_lossless :
  is_lossless ideal_eta_decoded_secret_pair_distribution.
proof.
rewrite ideal_eta_decoded_secret_pair_eq_iid.
exact ideal_eta_secret_pair_lossless.
qed.

lemma ideal_eta_decoded_secret_pair_point_mode2
    (pair : ideal_eta_secret_pair) :
  size pair.`1 = KeygenSamplerCallersSpec.mode2_m_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    pair.`1 =>
  size pair.`2 = KeygenSamplerCallersSpec.mode2_k_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    pair.`2 =>
  mu1 ideal_eta_decoded_secret_pair_distribution pair =
    (1%r / 3%r) ^ 1280.
proof.
move=> hs1size hs1all hs2size hs2all.
rewrite ideal_eta_decoded_secret_pair_eq_iid.
exact
  (ideal_eta_secret_pair_point_mode2
    pair hs1size hs1all hs2size hs2all).
qed.

lemma eta_padded_word_list_size coefficients :
  size coefficients <= eta_vector_word_capacity_i =>
  size (eta_padded_word_list coefficients) * 4 = BArray8192.size.
proof.
move=> hsize.
rewrite
  /eta_padded_word_list size_cat size_map size_nseq
  /eta_vector_word_capacity_i.
rewrite
  (_ : max 0 (BArray8192.size %/ 4 - size coefficients) =
       BArray8192.size %/ 4 - size coefficients) 1:/#.
rewrite /BArray8192.size.
ring.
qed.

lemma pack_eta_coefficients8192_get32 coefficients i :
  size coefficients <= eta_vector_word_capacity_i =>
  0 <= i < size coefficients =>
  BArray8192.get32 (pack_eta_coefficients8192 coefficients) i =
  W32.of_int (nth 0 coefficients i).
proof.
move=> hsize hi.
rewrite /pack_eta_coefficients8192.
rewrite BArray8192.get32_of_list32.
+ exact (eta_padded_word_list_size coefficients hsize).
rewrite /eta_padded_word_list nth_cat size_map.
rewrite iftrue 1:/#.
exact (nth_map 0 W32.zero W32.of_int i coefficients hi).
qed.

lemma ideal_eta_vector_flatten_size polynomials count :
  size polynomials = count =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    polynomials =>
  size (flatten polynomials) =
    KeygenEtaSamplerSpec.eta_poly_words_i * count.
proof.
move=> hsize hall.
rewrite
  (size_flatten_ctt
    KeygenEtaSamplerSpec.eta_poly_words_i polynomials).
+ move=> polynomial hpolynomial.
  have hsupport : polynomial \in
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_polynomial_distribution.
  + move: hall; rewrite allP => hall.
    exact (hall polynomial hpolynomial).
  rewrite
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_polynomial_support in hsupport.
  move: hsupport => [hpoly_size _].
  exact hpoly_size.
rewrite hsize.
trivial.
qed.

lemma ideal_eta_vector_flatten_support polynomials :
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    polynomials =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    (flatten polynomials).
proof.
move=> hall.
apply/List.allP => coefficient hcoefficient.
rewrite -flattenP in hcoefficient.
move: hcoefficient => [polynomial [hpolynomial hcoefficient]].
have hpoly_support : polynomial \in
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_polynomial_distribution.
+ move: hall; rewrite allP => hall.
  exact (hall polynomial hpolynomial).
rewrite
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_polynomial_support in hpoly_support.
move: hpoly_support => [_ hpoly_all].
move: hpoly_all; rewrite allP => hpoly_all.
exact (hpoly_all coefficient hcoefficient).
qed.

lemma ideal_eta_centered_trit_to_sint value :
  value \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution =>
  W32.to_sint (W32.of_int value) = value.
proof.
move=> hvalue.
rewrite
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_support in hvalue.
rewrite W32.of_sintK /W32.smod /=.
smt().
qed.

lemma pack_eta_vector8192_centered polynomials count :
  0 <= count =>
  KeygenEtaSamplerSpec.eta_poly_words_i * count <=
    eta_vector_word_capacity_i =>
  size polynomials = count =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
        .ideal_eta_polynomial_distribution)
    polynomials =>
  KeygenSamplerCallersSpec.eta_vector_centered8192
    (pack_eta_vector8192 polynomials) count.
proof.
move=> hcount hcapacity hsize hall.
have hflat_size :=
  ideal_eta_vector_flatten_size polynomials count hsize hall.
have hflat_support := ideal_eta_vector_flatten_support polynomials hall.
have hflat_capacity :
  size (flatten polynomials) <= eta_vector_word_capacity_i by
  rewrite hflat_size.
rewrite
  /KeygenSamplerCallersSpec.eta_vector_centered8192
  /KeygenEtaSamplerSpec.centered_interval8192
  /KeygenSamplerCallersSpec.eta_vector_words_i /=.
move=> i hi.
have hi_flat : 0 <= i < size (flatten polynomials).
+ rewrite hflat_size.
  rewrite /KeygenEtaSamplerSpec.eta_poly_words_i in hi.
  rewrite /KeygenEtaSamplerSpec.eta_poly_words_i.
  smt().
have hnth_support : nth 0 (flatten polynomials) i \in
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution.
+ move: hflat_support; rewrite allP => hflat_support.
  apply hflat_support.
  exact (mem_nth 0 (flatten polynomials) i hi_flat).
rewrite /pack_eta_vector8192.
rewrite
  (pack_eta_coefficients8192_get32
    (flatten polynomials) i hflat_capacity hi_flat).
rewrite (ideal_eta_centered_trit_to_sint
  (nth 0 (flatten polynomials) i) hnth_support).
rewrite
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_support in hnth_support.
move: hnth_support => [-> | [-> | ->]]; trivial.
qed.

lemma ideal_eta_packed_secret_pair_lossless :
  is_lossless ideal_eta_packed_secret_pair_distribution.
proof.
rewrite /ideal_eta_packed_secret_pair_distribution.
apply dmap_ll.
exact ideal_eta_secret_pair_lossless.
qed.

lemma ideal_eta_packed_secret_pair_support sample :
  sample \in ideal_eta_packed_secret_pair_distribution <=>
  ideal_eta_packed_secret_pair_valid sample.
proof.
rewrite
  /ideal_eta_packed_secret_pair_distribution
  /ideal_eta_packed_secret_pair_valid supp_dmap.
trivial.
qed.

lemma ideal_eta_packed_secret_pair_centered sample :
  sample \in ideal_eta_packed_secret_pair_distribution =>
  KeygenSamplerCallersSpec.eta_vector_centered8192
    sample.`1 KeygenSamplerCallersSpec.mode2_m_i /\
  KeygenSamplerCallersSpec.eta_vector_centered8192
    sample.`2 KeygenSamplerCallersSpec.mode2_k_i.
proof.
rewrite
  /ideal_eta_packed_secret_pair_distribution supp_dmap.
move=> [pair [hpair ->]].
rewrite ideal_eta_secret_pair_support in hpair.
move: hpair => [hs1size [hs1all [hs2size hs2all]]].
rewrite /pack_eta_secret_pair /=.
split.
+ apply pack_eta_vector8192_centered.
  + by rewrite /KeygenSamplerCallersSpec.mode2_m_i.
  + rewrite
      /KeygenEtaSamplerSpec.eta_poly_words_i
      /KeygenSamplerCallersSpec.mode2_m_i
      /eta_vector_word_capacity_i
      /BArray8192.size.
    trivial.
  + exact hs1size.
  exact hs1all.
apply pack_eta_vector8192_centered.
+ by rewrite /KeygenSamplerCallersSpec.mode2_k_i.
+ rewrite
    /KeygenEtaSamplerSpec.eta_poly_words_i
    /KeygenSamplerCallersSpec.mode2_k_i
    /eta_vector_word_capacity_i
    /BArray8192.size.
  trivial.
+ exact hs2size.
exact hs2all.
qed.

lemma ideal_eta_decoded_packed_secret_pair_eq_iid :
  ideal_eta_decoded_packed_secret_pair_distribution =
  ideal_eta_packed_secret_pair_distribution.
proof.
rewrite
  /ideal_eta_decoded_packed_secret_pair_distribution
  /ideal_eta_packed_secret_pair_distribution
  ideal_eta_decoded_secret_pair_eq_iid.
trivial.
qed.

lemma ideal_eta_decoded_packed_secret_pair_lossless :
  is_lossless ideal_eta_decoded_packed_secret_pair_distribution.
proof.
rewrite ideal_eta_decoded_packed_secret_pair_eq_iid.
exact ideal_eta_packed_secret_pair_lossless.
qed.

end Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze.
