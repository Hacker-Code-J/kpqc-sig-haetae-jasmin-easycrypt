require import
  AllCore DInterval DList Distr IntDiv List Mu_mem Real StdBigop StdOrder.

require import
  KeygenEtaSamplerSpec
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.

import RealOrder.

theory Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze.

(* One accepted byte contributes five balanced ternary coefficients, so
   52 accepted bytes suffice for a 256-coefficient polynomial.  This remains
   an ideal-randomness construction; it does not assign an iid law to the
   deterministic SHAKE stream used by the concrete sampler. *)

op ideal_eta_poly_blocks_i : int = 52.

op eta_uncenter_trit (value : int) : int =
  if value = -1 then 2 else value.

op eta_uncentered_digit (values : int list) (digit : int) : int =
  eta_uncenter_trit (nth 0 values digit).

op eta_encode_digit_block (values : int list) : int =
    eta_uncentered_digit values 0
  + 3 * eta_uncentered_digit values 1
  + 9 * eta_uncentered_digit values 2
  + 27 * eta_uncentered_digit values 3
  + 81 * eta_uncentered_digit values 4.

op ideal_eta_polynomial_distribution : int list distr =
  dlist
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    KeygenEtaSamplerSpec.eta_poly_words_i.

op ideal_eta_decoded_polynomial_distribution : int list distr =
  dmap
    (dlist
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_accepted_byte
      ideal_eta_poly_blocks_i)
    (fun bytes =>
      take KeygenEtaSamplerSpec.eta_poly_words_i
        (KeygenEtaSamplerSpec.eta_decode_bytes bytes)).

op ideal_eta_decoded_coefficients_distribution : int list distr =
  dmap
    (dlist
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_accepted_byte
      ideal_eta_poly_blocks_i)
    KeygenEtaSamplerSpec.eta_decode_bytes.

lemma ideal_eta_centered_trit_support value :
  value \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution <=>
  value = -1 \/ value = 0 \/ value = 1.
proof.
rewrite
  /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  supp_dmap.
split.
+ move=> [residue [hresidue ->]].
  rewrite supp_dinter in hresidue.
  rewrite
    /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_center_residue.
  smt().
move=> [-> | [-> | ->]].
+ exists 2.
  split; first by rewrite supp_dinter; smt().
  by rewrite
    /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_center_residue.
+ exists 0.
  split; first by rewrite supp_dinter; smt().
  by rewrite
    /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_center_residue.
exists 1.
split; first by rewrite supp_dinter; smt().
by rewrite
  /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_center_residue.
qed.

lemma ideal_eta_centered_trit_lossless :
  is_lossless
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution.
proof.
rewrite
  /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution.
apply dmap_ll.
by apply dinter_ll.
qed.

lemma ideal_eta_centered_trit_uniform :
  is_uniform
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution.
proof.
rewrite
  /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution.
apply dmap_uni_in_inj.
+ move=> residue1 residue2 hresidue1 hresidue2 heq.
  rewrite supp_dinter in hresidue1.
  rewrite supp_dinter in hresidue2.
  have hrange1 : 0 <= residue1 < 3 by smt().
  have hrange2 : 0 <= residue2 < 3 by smt().
  exact
    (Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .eta_center_residue_injective
      residue1 residue2 hrange1 hrange2 heq).
apply dinter_uni.
qed.

lemma ideal_eta_digit_block_uniform :
  is_uniform
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_digit_block_distribution.
proof.
rewrite
  /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_digit_block_distribution.
apply dmap_uni_in_inj.
+ move=> byte1 byte2 hbyte1 hbyte2 hdecode.
  rewrite
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_accepted_byte_support in hbyte1.
  rewrite
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_accepted_byte_support in hbyte2.
  exact
    (Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .eta_decode_byte_injective
      byte1 byte2 hbyte1 hbyte2 hdecode).
exact
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_accepted_byte_uniform.
qed.

lemma eta_uncenter_trit_range value :
  value = -1 \/ value = 0 \/ value = 1 =>
  0 <= eta_uncenter_trit value < 3.
proof. by rewrite /eta_uncenter_trit; smt(). qed.

lemma eta_center_uncenter_trit value :
  value = -1 \/ value = 0 \/ value = 1 =>
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_center_residue
    (eta_uncenter_trit value) = value.
proof.
rewrite
  /eta_uncenter_trit
  /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_center_residue.
smt().
qed.

lemma eta_digit_block_supported_nth values digit :
  size values = KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    values =>
  0 <= digit < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  nth 0 values digit \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution.
proof.
move=> hsize hall hdigit.
move: hall.
rewrite -(
  all_nthP
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    values 0).
move=> hall.
apply hall.
by rewrite hsize.
qed.

lemma eta_encode_digit_block_range values :
  size values = KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    values =>
  0 <= eta_encode_digit_block values <
    KeygenEtaSamplerSpec.eta_accept_bound_i.
proof.
move=> hsize hall.
have h0 := eta_digit_block_supported_nth values 0 hsize hall _.
+ by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
have h1 := eta_digit_block_supported_nth values 1 hsize hall _.
+ by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
have h2 := eta_digit_block_supported_nth values 2 hsize hall _.
+ by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
have h3 := eta_digit_block_supported_nth values 3 hsize hall _.
+ by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
have h4 := eta_digit_block_supported_nth values 4 hsize hall _.
+ by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
rewrite ideal_eta_centered_trit_support in h0.
rewrite ideal_eta_centered_trit_support in h1.
rewrite ideal_eta_centered_trit_support in h2.
rewrite ideal_eta_centered_trit_support in h3.
rewrite ideal_eta_centered_trit_support in h4.
have hr0 := eta_uncenter_trit_range (nth 0 values 0) h0.
have hr1 := eta_uncenter_trit_range (nth 0 values 1) h1.
have hr2 := eta_uncenter_trit_range (nth 0 values 2) h2.
have hr3 := eta_uncenter_trit_range (nth 0 values 3) h3.
have hr4 := eta_uncenter_trit_range (nth 0 values 4) h4.
rewrite
  /eta_encode_digit_block
  /eta_uncentered_digit
  /KeygenEtaSamplerSpec.eta_accept_bound_i.
smt().
qed.

lemma base3_step quotient residue :
  0 <= residue < 3 =>
  (quotient * 3 + residue) %% 3 = residue /\
  (quotient * 3 + residue) %/ 3 = quotient.
proof.
move=> hresidue.
split.
+ by rewrite modzMDl modz_small 1:/#.
by rewrite divzMDl 1:/# divz_small 1:/#.
qed.

lemma ideal_eta_polynomial_lossless :
  is_lossless ideal_eta_polynomial_distribution.
proof.
rewrite /ideal_eta_polynomial_distribution.
apply dlist_ll.
exact ideal_eta_centered_trit_lossless.
qed.

lemma ideal_eta_polynomial_uniform :
  is_uniform ideal_eta_polynomial_distribution.
proof.
rewrite /ideal_eta_polynomial_distribution.
apply dlist_uni.
exact ideal_eta_centered_trit_uniform.
qed.

lemma ideal_eta_polynomial_support values :
  values \in ideal_eta_polynomial_distribution <=>
  size values = KeygenEtaSamplerSpec.eta_poly_words_i /\
  all
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    values.
proof.
rewrite /ideal_eta_polynomial_distribution supp_dlist.
+ by rewrite /KeygenEtaSamplerSpec.eta_poly_words_i.
trivial.
qed.

lemma ideal_eta_centered_trit_point value :
  value = -1 \/ value = 0 \/ value = 1 =>
  mu1
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    value = 1%r / 3%r.
proof.
move=> [-> | [-> | ->]].
+ exact
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_point_neg1.
+ exact
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_point_zero.
exact
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_point_one.
qed.

lemma dlist_exact_point ['a] (d : 'a distr) (point : real) values :
  (forall value, value \in values => mu1 d value = point) =>
  mu1 (dlist d (size values)) values = point ^ (size values).
proof.
move=> hpoint.
rewrite dlist1E 1:size_ge0 /=.
elim values hpoint => [|value values ih] hpoint.
+ by rewrite StdBigop.Bigreal.BRM.big_nil RField.expr0.
rewrite StdBigop.Bigreal.BRM.big_cons /predT /=.
have hhead : mu1 d value = point by apply hpoint; trivial.
have htail : forall x, x \in values => mu1 d x = point.
+ move=> x hx.
  apply hpoint.
  by rewrite /= hx.
rewrite hhead (ih htail).
rewrite (_ : 1 + size values = size values + 1) 1:/#.
rewrite RField.exprS 1:size_ge0.
ring.
qed.

lemma ideal_eta_polynomial_point values :
  size values = KeygenEtaSamplerSpec.eta_poly_words_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    values =>
  mu1 ideal_eta_polynomial_distribution values =
    (1%r / 3%r) ^ KeygenEtaSamplerSpec.eta_poly_words_i.
proof.
move=> hsize hall.
rewrite /ideal_eta_polynomial_distribution -hsize.
have hpoint : forall value, value \in values =>
  mu1
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    value = 1%r / 3%r.
+ move=> value hvalue.
  have hsupport : value \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution.
  + move: hall; rewrite allP => hall.
    exact (hall value hvalue).
  rewrite ideal_eta_centered_trit_support in hsupport.
  exact (ideal_eta_centered_trit_point value hsupport).
have h := dlist_exact_point
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution
  (1%r / 3%r) values hpoint.
exact h.
qed.

lemma eta_encode_digit_block_digit values digit :
  size values = KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    values =>
  0 <= digit < KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_residue_digit
    (eta_encode_digit_block values) digit =
  eta_uncenter_trit (nth 0 values digit).
proof.
move=> hsize hall hdigit.
have h0 := eta_digit_block_supported_nth values 0 hsize hall _.
+ by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
have h1 := eta_digit_block_supported_nth values 1 hsize hall _.
+ by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
have h2 := eta_digit_block_supported_nth values 2 hsize hall _.
+ by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
have h3 := eta_digit_block_supported_nth values 3 hsize hall _.
+ by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
have h4 := eta_digit_block_supported_nth values 4 hsize hall _.
+ by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
rewrite ideal_eta_centered_trit_support in h0.
rewrite ideal_eta_centered_trit_support in h1.
rewrite ideal_eta_centered_trit_support in h2.
rewrite ideal_eta_centered_trit_support in h3.
rewrite ideal_eta_centered_trit_support in h4.
have hr0 := eta_uncenter_trit_range (nth 0 values 0) h0.
have hr1 := eta_uncenter_trit_range (nth 0 values 1) h1.
have hr2 := eta_uncenter_trit_range (nth 0 values 2) h2.
have hr3 := eta_uncenter_trit_range (nth 0 values 3) h3.
have hr4 := eta_uncenter_trit_range (nth 0 values 4) h4.
have hd0 : 0 <= eta_uncentered_digit values 0 < 3 by
  rewrite /eta_uncentered_digit; exact hr0.
have hd1 : 0 <= eta_uncentered_digit values 1 < 3 by
  rewrite /eta_uncentered_digit; exact hr1.
have hd2 : 0 <= eta_uncentered_digit values 2 < 3 by
  rewrite /eta_uncentered_digit; exact hr2.
have hd3 : 0 <= eta_uncentered_digit values 3 < 3 by
  rewrite /eta_uncentered_digit; exact hr3.
have hd4 : 0 <= eta_uncentered_digit values 4 < 3 by
  rewrite /eta_uncentered_digit; exact hr4.
pose q4 := eta_uncentered_digit values 4.
pose q3 := eta_uncentered_digit values 3 + q4 * 3.
pose q2 := eta_uncentered_digit values 2 + q3 * 3.
pose q1 := eta_uncentered_digit values 1 + q2 * 3.
have hencode :
  eta_encode_digit_block values =
  q1 * 3 + eta_uncentered_digit values 0.
+ rewrite /eta_encode_digit_block /q1 /q2 /q3 /q4.
  ring.
have hq1 : q1 = q2 * 3 + eta_uncentered_digit values 1 by
  rewrite /q1; ring.
have hq2 : q2 = q3 * 3 + eta_uncentered_digit values 2 by
  rewrite /q2; ring.
have hq3 : q3 = q4 * 3 + eta_uncentered_digit values 3 by
  rewrite /q3; ring.
have [hmod0' hdiv0'] :=
  base3_step q1 (eta_uncentered_digit values 0) hd0.
have [hmod1' hdiv1'] :=
  base3_step q2 (eta_uncentered_digit values 1) hd1.
have [hmod2' hdiv2'] :=
  base3_step q3 (eta_uncentered_digit values 2) hd2.
have [hmod3' hdiv3'] :=
  base3_step q4 (eta_uncentered_digit values 3) hd3.
have hmod0 :
  eta_encode_digit_block values %% 3 =
  eta_uncentered_digit values 0 by
  rewrite hencode hmod0'.
have hdiv0 : eta_encode_digit_block values %/ 3 = q1 by
  rewrite hencode hdiv0'.
have hmod1 : q1 %% 3 = eta_uncentered_digit values 1 by
  rewrite hq1 hmod1'.
have hdiv1 : q1 %/ 3 = q2 by rewrite hq1 hdiv1'.
have hmod2 : q2 %% 3 = eta_uncentered_digit values 2 by
  rewrite hq2 hmod2'.
have hdiv2 : q2 %/ 3 = q3 by rewrite hq2 hdiv2'.
have hmod3 : q3 %% 3 = eta_uncentered_digit values 3 by
  rewrite hq3 hmod3'.
have hdiv3 : q3 %/ 3 = q4 by rewrite hq3 hdiv3'.
have hmod4 : q4 %% 3 = eta_uncentered_digit values 4.
+ by rewrite /q4 modz_small 1:/#.
have hres0 :
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_residue_digit
    (eta_encode_digit_block values) 0 =
  eta_uncenter_trit (nth 0 values 0) by
  rewrite
    /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_residue_digit
    expr0 divz1 hmod0 /eta_uncentered_digit.
have hres1 :
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_residue_digit
    (eta_encode_digit_block values) 1 =
  eta_uncenter_trit (nth 0 values 1) by
  rewrite
    /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_residue_digit;
  change
    ((eta_encode_digit_block values %/ 3) %% 3 =
      eta_uncentered_digit values 1);
  rewrite hdiv0 hmod1.
have hres2 :
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_residue_digit
    (eta_encode_digit_block values) 2 =
  eta_uncenter_trit (nth 0 values 2) by
  rewrite
    /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_residue_digit
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_div_pow2;
  change
    (((eta_encode_digit_block values %/ 3) %/ 3) %% 3 =
      eta_uncentered_digit values 2);
  rewrite hdiv0 hdiv1 hmod2.
have hres3 :
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_residue_digit
    (eta_encode_digit_block values) 3 =
  eta_uncenter_trit (nth 0 values 3) by
  rewrite
    /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_residue_digit
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_div_pow3;
  change
    ((((eta_encode_digit_block values %/ 3) %/ 3) %/ 3) %% 3 =
      eta_uncentered_digit values 3);
  rewrite hdiv0 hdiv1 hdiv2 hmod3.
have hres4 :
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_residue_digit
    (eta_encode_digit_block values) 4 =
  eta_uncenter_trit (nth 0 values 4) by
  rewrite
    /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_residue_digit
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze.eta_div_pow4;
  change
    (((((eta_encode_digit_block values %/ 3) %/ 3) %/ 3) %/ 3) %% 3 =
      eta_uncentered_digit values 4);
  rewrite hdiv0 hdiv1 hdiv2 hdiv3 hmod4.
rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i in hdigit.
have hdigit_cases :
  digit = 0 \/ digit = 1 \/ digit = 2 \/ digit = 3 \/ digit = 4 by
  smt().
move: hdigit_cases => [-> | [-> | [-> | [-> | ->]]]].
+ exact hres0.
+ exact hres1.
+ exact hres2.
+ exact hres3.
exact hres4.
qed.

lemma eta_decode_encode_digit_block values :
  size values = KeygenEtaSamplerSpec.eta_digits_per_byte_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    values =>
  KeygenEtaSamplerSpec.eta_decode_byte
    (eta_encode_digit_block values) = values.
proof.
move=> hsize hall.
have hencode := eta_encode_digit_block_range values hsize hall.
apply/(eq_from_nth 0).
+ rewrite KeygenEtaSamplerSpec.eta_decode_byte_size hencode hsize.
  trivial.
move=> digit.
rewrite KeygenEtaSamplerSpec.eta_decode_byte_size hencode => hdigit.
rewrite
  (KeygenEtaSamplerSpec.eta_decode_byte_nth
    (eta_encode_digit_block values) digit hencode hdigit).
rewrite
  (Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .eta_centered_digit_as_centered_residue
    (eta_encode_digit_block values) digit hencode hdigit).
rewrite (eta_encode_digit_block_digit values digit hsize hall hdigit).
apply eta_center_uncenter_trit.
rewrite -ideal_eta_centered_trit_support.
exact (eta_digit_block_supported_nth values digit hsize hall hdigit).
qed.

lemma ideal_eta_digit_block_support values :
  values \in
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_digit_block_distribution <=>
  size values = KeygenEtaSamplerSpec.eta_digits_per_byte_i /\
  all
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    values.
proof.
rewrite
  /Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_digit_block_distribution
  supp_dmap.
split.
+ move=> [byte [hbyte ->]].
  rewrite
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_accepted_byte_support in hbyte.
  split.
  + by rewrite KeygenEtaSamplerSpec.eta_decode_byte_size hbyte.
  apply/(
    all_nthP
      (support
        Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
          .ideal_eta_centered_trit_distribution)
      (KeygenEtaSamplerSpec.eta_decode_byte byte) 0).
  move=> digit.
  rewrite KeygenEtaSamplerSpec.eta_decode_byte_size hbyte => hdigit.
  rewrite
    (KeygenEtaSamplerSpec.eta_decode_byte_nth
      byte digit hbyte hdigit).
  rewrite ideal_eta_centered_trit_support.
  have hrange := KeygenEtaSamplerSpec.eta_centered_digit_range byte digit.
  smt().
move=> [hsize hall].
exists (eta_encode_digit_block values).
split.
+ rewrite
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_accepted_byte_support.
  exact (eta_encode_digit_block_range values hsize hall).
rewrite (eta_decode_encode_digit_block values hsize hall).
trivial.
qed.

lemma ideal_eta_digit_block_eq_iid :
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_digit_block_distribution =
  dlist
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    KeygenEtaSamplerSpec.eta_digits_per_byte_i.
proof.
have hll1 :=
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_digit_block_lossless.
have hll2 :
  is_lossless
    (dlist
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution
      KeygenEtaSamplerSpec.eta_digits_per_byte_i).
+ apply dlist_ll.
  exact ideal_eta_centered_trit_lossless.
have huni1 := ideal_eta_digit_block_uniform.
have huni2 :
  is_uniform
    (dlist
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution
      KeygenEtaSamplerSpec.eta_digits_per_byte_i).
+ apply dlist_uni.
  exact ideal_eta_centered_trit_uniform.
have hsupp :
  support
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_digit_block_distribution =
  support
    (dlist
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution
      KeygenEtaSamplerSpec.eta_digits_per_byte_i).
+ apply fun_ext => values.
  rewrite ideal_eta_digit_block_support supp_dlist.
  + by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
  trivial.
apply/eq_distr => values.
rewrite
  (mu1_uni
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_digit_block_distribution values huni1)
  (mu1_uni
    (dlist
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution
      KeygenEtaSamplerSpec.eta_digits_per_byte_i)
    values huni2).
rewrite hll1 hll2 hsupp.
trivial.
qed.

lemma dmap_dlist_take_prefix ['a] (d : 'a distr) n m :
  0 <= n =>
  0 <= m =>
  is_lossless d =>
  dmap (dlist d (n + m)) (take n) = dlist d n.
proof.
move=> hn hm hll.
rewrite dlist_add 1:hn 1:hm dmap_comp.
have -> :
  dmap
    (dlist d n `*` dlist d m)
    (take n \o (fun (parts : 'a list * 'a list) => parts.`1 ++ parts.`2)) =
  dmap
    (dlist d n `*` dlist d m)
    (fun (parts : 'a list * 'a list) => parts.`1).
+ apply eq_dmap_in => parts hparts.
  rewrite supp_dprod in hparts.
  move: hparts => [hleft _].
  have hsize := supp_dlist_size d n parts.`1 hn hleft.
  rewrite /(\o) /=.
  exact (take_size_cat n parts.`1 parts.`2 hsize).
rewrite (dprod_marginalL (dlist d n) (dlist d m) idfun).
have htail : is_lossless (dlist d m) by
  apply dlist_ll; exact hll.
rewrite /is_lossless in htail.
rewrite htail dmap_id dscalar1.
trivial.
qed.

lemma ideal_eta_decoded_coefficients_eq_iid :
  ideal_eta_decoded_coefficients_distribution =
  dlist
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (KeygenEtaSamplerSpec.eta_digits_per_byte_i * ideal_eta_poly_blocks_i).
proof.
rewrite
  /ideal_eta_decoded_coefficients_distribution
  /KeygenEtaSamplerSpec.eta_decode_bytes.
have hfun :
  (fun bytes : int list =>
    flatten (map KeygenEtaSamplerSpec.eta_decode_byte bytes)) =
  (flatten \o (map KeygenEtaSamplerSpec.eta_decode_byte)).
+ apply fun_ext => bytes.
  by rewrite /(\o).
rewrite hfun -dmap_comp -dlist_dmap.
rewrite
  -/Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_digit_block_distribution.
rewrite ideal_eta_digit_block_eq_iid.
rewrite dlist_dlist.
+ by rewrite /KeygenEtaSamplerSpec.eta_digits_per_byte_i.
+ by rewrite /ideal_eta_poly_blocks_i.
trivial.
qed.

lemma ideal_eta_decoded_polynomial_eq_iid :
  ideal_eta_decoded_polynomial_distribution =
  ideal_eta_polynomial_distribution.
proof.
rewrite
  /ideal_eta_decoded_polynomial_distribution
  /ideal_eta_polynomial_distribution.
have hfun :
  (fun bytes : int list =>
    take KeygenEtaSamplerSpec.eta_poly_words_i
      (KeygenEtaSamplerSpec.eta_decode_bytes bytes)) =
  (take KeygenEtaSamplerSpec.eta_poly_words_i \o
    KeygenEtaSamplerSpec.eta_decode_bytes).
+ apply fun_ext => bytes.
  by rewrite /(\o).
rewrite hfun -dmap_comp.
rewrite -/ideal_eta_decoded_coefficients_distribution.
rewrite ideal_eta_decoded_coefficients_eq_iid.
rewrite
  /KeygenEtaSamplerSpec.eta_digits_per_byte_i
  /ideal_eta_poly_blocks_i
  /KeygenEtaSamplerSpec.eta_poly_words_i /=.
apply
  (dmap_dlist_take_prefix
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    256 4).
+ trivial.
+ trivial.
exact ideal_eta_centered_trit_lossless.
qed.

lemma ideal_eta_decoded_polynomial_lossless :
  is_lossless ideal_eta_decoded_polynomial_distribution.
proof.
rewrite ideal_eta_decoded_polynomial_eq_iid.
exact ideal_eta_polynomial_lossless.
qed.

lemma ideal_eta_decoded_polynomial_point values :
  size values = KeygenEtaSamplerSpec.eta_poly_words_i =>
  all
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    values =>
  mu1 ideal_eta_decoded_polynomial_distribution values =
    (1%r / 3%r) ^ KeygenEtaSamplerSpec.eta_poly_words_i.
proof.
move=> hsize hall.
rewrite ideal_eta_decoded_polynomial_eq_iid.
exact (ideal_eta_polynomial_point values hsize hall).
qed.

end Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze.
