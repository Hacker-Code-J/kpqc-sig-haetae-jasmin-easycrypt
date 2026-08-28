require import AllCore DList Distr List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import BArray8192 KeygenEtaSamplerSpec KeygenSamplerCallersSpec
               KeygenM23MatrixSpec Mode2KeygenCoreEquation
               Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
               Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
               Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
               Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
               Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
               Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze.

import RealOrder.
import Bigreal Bigreal.BRM.

theory Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze.

(* This layer is a fixed-context heterogeneous product law over the active
   512 finalized [s2] coordinates.  The contexts [pre_bp] and [avec] are
   parameters, so the coordinates are independent only conditionally on those
   fixed arrays.  This file does not claim random-context or unconditional
   independence, homogeneous iid finalized outputs, FFT concentration, or any
   SHAKE/actual-sampler statement. *)

op ideal_final_s2_flat_source_distribution : int list distr =
  dmap
    Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze
      .ideal_eta_s2_distribution
    flatten.

op ideal_final_s2_output_coord
    (pre_bp avec : BArray8192.t) (i x : int) : int =
  Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.math_output
    (BArray8192.get32 pre_bp i)
    (BArray8192.get32 avec i)
    x.

op ideal_final_s2_output_distribution
    (pre_bp avec : BArray8192.t) : int list distr =
  dmap
    ideal_final_s2_flat_source_distribution
    (mapi (ideal_final_s2_output_coord pre_bp avec)).

op ideal_final_s2_residual_coord
    (pre_bp avec : BArray8192.t) (i : int) (x : int) : real =
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_centered_residual_at pre_bp avec i x.

op ideal_final_s2_residual_distribution
    (pre_bp avec : BArray8192.t) : real list distr =
  dmap
    ideal_final_s2_flat_source_distribution
    (mapi (ideal_final_s2_residual_coord pre_bp avec)).

op ideal_final_s2_residual_distribution_at
    (pre_bp avec : BArray8192.t) (i : int) : real distr =
  dmap
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_residual_coord pre_bp avec i).

op ideal_final_s2_residual_moment2_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  (((ideal_final_s2_residual_coord pre_bp avec i (-1)) ^ 2) +
   ((ideal_final_s2_residual_coord pre_bp avec i 0) ^ 2) +
   ((ideal_final_s2_residual_coord pre_bp avec i 1) ^ 2)) / 3%r.

op ideal_final_s2_residual_moment4_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  (((ideal_final_s2_residual_coord pre_bp avec i (-1)) ^ 4) +
   ((ideal_final_s2_residual_coord pre_bp avec i 0) ^ 4) +
   ((ideal_final_s2_residual_coord pre_bp avec i 1) ^ 4)) / 3%r.

op ideal_final_s2_residual_moment8_at
    (pre_bp avec : BArray8192.t) (i : int) : real =
  (((ideal_final_s2_residual_coord pre_bp avec i (-1)) ^ 8) +
   ((ideal_final_s2_residual_coord pre_bp avec i 0) ^ 8) +
   ((ideal_final_s2_residual_coord pre_bp avec i 1) ^ 8)) / 3%r.

lemma conditional_dmap_dlist_nth ['a]
    (d : 'a distr) (x0 : 'a) n i :
  is_lossless d =>
  0 <= i < n =>
  dmap (dlist d n) (fun xs => nth x0 xs i) = d.
proof.
move=> hll hi.
have hn : 0 <= n - 1 by smt().
have hi' : 0 <= i <= n - 1 by smt().
rewrite (_ : n = (n - 1) + 1) 1:/#.
rewrite (dlist_insert x0 i (n - 1) d hn hi') dmap_comp.
have -> :
    dmap (d `*` dlist d (n - 1))
      ((fun xs => nth x0 xs i) \o
       (fun x_xs : 'a * 'a list => insert x_xs.`1 x_xs.`2 i)) =
    dmap (d `*` dlist d (n - 1))
      (fun (x_xs : 'a * 'a list) => x_xs.`1).
+ apply eq_dmap_in => x_xs hx_x_xs.
  rewrite supp_dprod in hx_x_xs.
  move: hx_x_xs => [_ hxs].
  have hsize := supp_dlist_size d (n - 1) x_xs.`2 hn hxs.
  rewrite /(\o) /=.
  apply nth_insert.
  rewrite hsize.
  exact hi'.
rewrite (dprod_marginalL d (dlist d (n - 1)) idfun).
have htail : is_lossless (dlist d (n - 1)) by
  apply dlist_ll; exact hll.
rewrite /is_lossless in htail.
rewrite htail dmap_id dscalar1.
trivial.
qed.

lemma conditional_dmap_dlist_mapi_nth ['a 'b]
    (d : 'a distr) (x0 : 'a) (y0 : 'b) n i
    (f : int -> 'a -> 'b) :
  is_lossless d =>
  0 <= i < n =>
  dmap (dmap (dlist d n) (mapi f)) (fun ys => nth y0 ys i) =
  dmap d (f i).
proof.
move=> hll hi.
have hn : 0 <= n by smt().
rewrite dmap_comp.
have -> :
    dmap (dlist d n)
      ((fun ys => nth y0 ys i) \o mapi f) =
    dmap (dlist d n)
      (fun xs => f i (nth x0 xs i)).
+ apply eq_dmap_in => xs hxs.
  have hsize := supp_dlist_size d n xs hn hxs.
  rewrite /(\o).
  by rewrite (nth_mapi x0 xs y0 f i) 1:/#.
change
  (dmap (dlist d n) ((f i) \o (fun xs => nth x0 xs i)) =
   dmap d (f i)).
rewrite -dmap_comp.
rewrite (conditional_dmap_dlist_nth d x0 n i hll hi).
trivial.
qed.

lemma conditional_dmap_dlist_mapi_event_product ['a 'b]
    (d : 'a distr) (x0 : 'a) (y0 : 'b) n
    (f : int -> 'a -> 'b) (P : int -> 'b -> bool) :
  0 <= n =>
  mu (dmap (dlist d n) (mapi f))
     (fun ys => forall i, 0 <= i && i < n => P i (nth y0 ys i)) =
  bigi predT (fun i => mu d (fun x => P i (f i x))) 0 n.
proof.
move=> hn.
rewrite dmapE.
have -> :
    mu (dlist d n)
      ((fun ys => forall i, 0 <= i && i < n => P i (nth y0 ys i)) \o
       mapi f) =
    mu (dlist d n)
      (fun xs => forall i, 0 <= i && i < n =>
        P i (f i (nth x0 xs i))).
+ apply mu_eq_support => xs hxs.
  have hsize := supp_dlist_size d n xs hn hxs.
  rewrite /(\o).
  apply eq_iff; split.
  + move=> h i hi.
    have := h i hi.
    by rewrite (nth_mapi x0 xs y0 f i) 1:/#.
  move=> h i hi.
  have := h i hi.
  by rewrite (nth_mapi x0 xs y0 f i) 1:/#.
exact (dlistE x0 d (fun i x => P i (f i x)) n).
qed.

lemma ideal_final_s2_flat_source_eq_iid :
  ideal_final_s2_flat_source_distribution =
  dlist
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    KeygenM23MatrixSpec.mode2_b_words_i.
proof.
rewrite /ideal_final_s2_flat_source_distribution.
rewrite
  /Mode2FaithfulSecurityIdealEtaVectorLawPostFreeze.ideal_eta_s2_distribution
  /Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_polynomial_distribution.
rewrite dlist_dlist.
+ by rewrite /KeygenEtaSamplerSpec.eta_poly_words_i.
+ by rewrite /KeygenSamplerCallersSpec.mode2_k_i.
have -> :
    KeygenEtaSamplerSpec.eta_poly_words_i *
      KeygenSamplerCallersSpec.mode2_k_i =
    KeygenM23MatrixSpec.mode2_b_words_i.
+ rewrite /KeygenEtaSamplerSpec.eta_poly_words_i
           /KeygenSamplerCallersSpec.mode2_k_i
           /KeygenM23MatrixSpec.mode2_b_words_i
           /KeygenM23MatrixSpec.mode2_rows_i
           /KeygenM23MatrixSpec.poly_words_i.
   ring.
trivial.
qed.

lemma ideal_final_s2_flat_source_lossless :
  is_lossless ideal_final_s2_flat_source_distribution.
proof.
rewrite ideal_final_s2_flat_source_eq_iid.
apply dlist_ll.
exact
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_lossless.
qed.

lemma ideal_final_s2_flat_source_support xs :
  xs \in ideal_final_s2_flat_source_distribution <=>
  size xs = KeygenM23MatrixSpec.mode2_b_words_i /\
  all
    (support
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution)
    xs.
proof.
rewrite ideal_final_s2_flat_source_eq_iid.
rewrite supp_dlist.
+ by rewrite /KeygenM23MatrixSpec.mode2_b_words_i.
trivial.
qed.

lemma ideal_final_s2_flat_source_marginal i :
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  dmap ideal_final_s2_flat_source_distribution
    (fun xs => nth 0 xs i) =
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
    .ideal_eta_centered_trit_distribution.
proof.
move=> hi.
rewrite ideal_final_s2_flat_source_eq_iid.
exact
  (conditional_dmap_dlist_nth
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    0
    KeygenM23MatrixSpec.mode2_b_words_i
    i
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_centered_trit_lossless
    hi).
qed.

lemma ideal_final_s2_output_distribution_lossless pre_bp avec :
  is_lossless (ideal_final_s2_output_distribution pre_bp avec).
proof.
rewrite /ideal_final_s2_output_distribution.
apply dmap_ll.
exact ideal_final_s2_flat_source_lossless.
qed.

lemma ideal_final_s2_output_distribution_support pre_bp avec ys :
  ys \in ideal_final_s2_output_distribution pre_bp avec <=>
  exists xs,
    xs \in ideal_final_s2_flat_source_distribution /\
    ys = mapi (ideal_final_s2_output_coord pre_bp avec) xs.
proof.
rewrite /ideal_final_s2_output_distribution supp_dmap.
trivial.
qed.

lemma ideal_final_s2_residual_distribution_lossless pre_bp avec :
  is_lossless (ideal_final_s2_residual_distribution pre_bp avec).
proof.
rewrite /ideal_final_s2_residual_distribution.
apply dmap_ll.
exact ideal_final_s2_flat_source_lossless.
qed.

lemma ideal_final_s2_residual_distribution_support pre_bp avec ys :
  ys \in ideal_final_s2_residual_distribution pre_bp avec <=>
  exists xs,
    xs \in ideal_final_s2_flat_source_distribution /\
    ys = mapi (ideal_final_s2_residual_coord pre_bp avec) xs.
proof.
rewrite /ideal_final_s2_residual_distribution supp_dmap.
trivial.
qed.

lemma ideal_final_s2_residual_distribution_at_lossless pre_bp avec i :
  is_lossless (ideal_final_s2_residual_distribution_at pre_bp avec i).
proof.
rewrite /ideal_final_s2_residual_distribution_at.
apply dmap_ll.
exact
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .ideal_eta_centered_trit_lossless.
qed.

lemma ideal_final_s2_residual_distribution_at_support
    pre_bp avec i y :
  y \in ideal_final_s2_residual_distribution_at pre_bp avec i <=>
  exists x,
    x \in
      Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
        .ideal_eta_centered_trit_distribution /\
    y = ideal_final_s2_residual_coord pre_bp avec i x.
proof.
rewrite /ideal_final_s2_residual_distribution_at supp_dmap.
trivial.
qed.

lemma ideal_final_s2_output_coordinate_marginal
    pre_bp avec i :
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  dmap (ideal_final_s2_output_distribution pre_bp avec)
    (fun ys => nth 0 ys i) =
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_distribution_at pre_bp avec i.
proof.
move=> hi.
rewrite /ideal_final_s2_output_distribution.
rewrite ideal_final_s2_flat_source_eq_iid.
rewrite /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_distribution_at
        /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
          .ideal_final_s2_distribution
        /ideal_final_s2_output_coord.
exact
  (conditional_dmap_dlist_mapi_nth
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    0 0
    KeygenM23MatrixSpec.mode2_b_words_i
    i
    (ideal_final_s2_output_coord pre_bp avec)
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_centered_trit_lossless
    hi).
qed.

lemma ideal_final_s2_residual_coordinate_marginal
    pre_bp avec i :
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  dmap (ideal_final_s2_residual_distribution pre_bp avec)
    (fun ys => nth 0%r ys i) =
  ideal_final_s2_residual_distribution_at pre_bp avec i.
proof.
move=> hi.
rewrite /ideal_final_s2_residual_distribution.
rewrite ideal_final_s2_flat_source_eq_iid.
rewrite /ideal_final_s2_residual_distribution_at.
exact
  (conditional_dmap_dlist_mapi_nth
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    0 0%r
    KeygenM23MatrixSpec.mode2_b_words_i
    i
    (ideal_final_s2_residual_coord pre_bp avec)
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_centered_trit_lossless
    hi).
qed.

lemma ideal_final_s2_output_event_marginalE
    pre_bp avec (P : int -> int -> bool) i :
  mu
    (Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution)
    (fun x => P i (ideal_final_s2_output_coord pre_bp avec i x)) =
  mu
    (Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
      .ideal_final_s2_distribution_at pre_bp avec i)
    (P i).
proof.
rewrite /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_distribution_at
        /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
          .ideal_final_s2_distribution
        /ideal_final_s2_output_coord.
have hd :=
  dmapE
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze.math_output
      (BArray8192.get32 pre_bp i)
      (BArray8192.get32 avec i))
    (P i).
rewrite /(\o) in hd.
apply eq_sym.
exact hd.
qed.

lemma ideal_final_s2_residual_event_marginalE
    pre_bp avec (P : int -> real -> bool) i :
  mu
    (Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution)
    (fun x => P i (ideal_final_s2_residual_coord pre_bp avec i x)) =
  mu (ideal_final_s2_residual_distribution_at pre_bp avec i) (P i).
proof.
rewrite /ideal_final_s2_residual_distribution_at /ideal_final_s2_residual_coord.
have hd :=
  dmapE
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
      .ideal_final_s2_centered_residual_at pre_bp avec i)
    (P i).
rewrite /(\o) in hd.
apply eq_sym.
exact hd.
qed.

lemma ideal_final_s2_output_rectangular_event_product
    pre_bp avec (P : int -> int -> bool) :
  mu (ideal_final_s2_output_distribution pre_bp avec)
     (fun ys =>
       forall i,
         0 <= i && i < KeygenM23MatrixSpec.mode2_b_words_i =>
         P i (nth 0 ys i)) =
  bigi predT
    (fun i =>
      mu
        (Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_distribution_at pre_bp avec i)
        (P i))
    0 KeygenM23MatrixSpec.mode2_b_words_i.
proof.
rewrite /ideal_final_s2_output_distribution.
rewrite ideal_final_s2_flat_source_eq_iid.
rewrite
  (conditional_dmap_dlist_mapi_event_product
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    0 0
    KeygenM23MatrixSpec.mode2_b_words_i
    (ideal_final_s2_output_coord pre_bp avec)
    P).
+ by rewrite /KeygenM23MatrixSpec.mode2_b_words_i.
apply eq_bigr => i _.
exact (ideal_final_s2_output_event_marginalE pre_bp avec P i).
qed.

lemma ideal_final_s2_residual_rectangular_event_product
    pre_bp avec (P : int -> real -> bool) :
  mu (ideal_final_s2_residual_distribution pre_bp avec)
     (fun ys =>
       forall i,
         0 <= i && i < KeygenM23MatrixSpec.mode2_b_words_i =>
         P i (nth 0%r ys i)) =
  bigi predT
    (fun i => mu (ideal_final_s2_residual_distribution_at pre_bp avec i) (P i))
    0 KeygenM23MatrixSpec.mode2_b_words_i.
proof.
rewrite /ideal_final_s2_residual_distribution.
rewrite ideal_final_s2_flat_source_eq_iid.
rewrite
  (conditional_dmap_dlist_mapi_event_product
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    0 0%r
    KeygenM23MatrixSpec.mode2_b_words_i
    (ideal_final_s2_residual_coord pre_bp avec)
    P).
+ by rewrite /KeygenM23MatrixSpec.mode2_b_words_i.
apply eq_bigr => i _.
exact (ideal_final_s2_residual_event_marginalE pre_bp avec P i).
qed.

lemma ideal_final_s2_residual_three_point_mean_zero_at
    pre_bp avec i :
  ((ideal_final_s2_residual_coord pre_bp avec i (-1)) +
   (ideal_final_s2_residual_coord pre_bp avec i 0) +
   (ideal_final_s2_residual_coord pre_bp avec i 1)) / 3%r = 0%r.
proof.
exact
  (Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_residual_three_point_average_zero pre_bp avec i).
qed.

lemma ideal_final_s2_residual_moment2_bridge pre_bp avec i :
  ideal_final_s2_residual_moment2_at pre_bp avec i =
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_centered_moment2_at pre_bp avec i.
proof.
rewrite /ideal_final_s2_residual_moment2_at
        /ideal_final_s2_residual_coord.
rewrite /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_moment2_at
        /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
          .ideal_final_s2_centered_moment2
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_residual_at.
trivial.
qed.

lemma ideal_final_s2_residual_moment4_bridge pre_bp avec i :
  ideal_final_s2_residual_moment4_at pre_bp avec i =
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_centered_moment4_at pre_bp avec i.
proof.
rewrite /ideal_final_s2_residual_moment4_at
        /ideal_final_s2_residual_coord.
rewrite /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_moment4_at
        /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
          .ideal_final_s2_centered_moment4
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_residual_at.
trivial.
qed.

lemma ideal_final_s2_residual_moment8_bridge pre_bp avec i :
  ideal_final_s2_residual_moment8_at pre_bp avec i =
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_centered_moment8_at pre_bp avec i.
proof.
rewrite /ideal_final_s2_residual_moment8_at
        /ideal_final_s2_residual_coord.
rewrite /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_moment8_at
        /Mode2FaithfulSecurityIdealFinalS2MomentLawPostFreeze
          .ideal_final_s2_centered_moment8
        /Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
          .ideal_final_s2_centered_residual_at.
trivial.
qed.

lemma ideal_final_s2_residual_moment_bounds_at
    pre_bp avec i :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= i < KeygenM23MatrixSpec.mode2_b_words_i =>
  ideal_final_s2_residual_moment2_at pre_bp avec i <= 8%r / 3%r /\
  ideal_final_s2_residual_moment4_at pre_bp avec i <= 32%r / 3%r /\
  ideal_final_s2_residual_moment8_at pre_bp avec i <= 512%r / 3%r.
proof.
move=> hctx hi.
have hbounds :=
  Mode2FaithfulSecurityIdealFinalS2ArrayBiasDecompositionPostFreeze
    .ideal_final_s2_moment_bounds_at pre_bp avec i hctx hi.
move: hbounds => [_ [h2 [_ [h4 [_ h8]]]]].
rewrite ideal_final_s2_residual_moment2_bridge
        ideal_final_s2_residual_moment4_bridge
        ideal_final_s2_residual_moment8_bridge.
smt().
qed.

end Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze.
