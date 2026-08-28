require import AllCore DList Distr Finite IntDiv List Real Ring StdBigop StdOrder.

from Jasmin require import JModel_x86.

require import
  BArray8192
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23MatrixSpec
  KeygenM23SingularFFTSpec
  KeygenM23SingularSpec
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
  Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
  Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze.

import RealOrder Bigreal Bigreal.BRM.
import KeygenM23ComplexReal KeygenM23IdealRootDFT.

theory Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze.

(* This file is a fixed-context projection bridge from the full 512-coordinate
   ideal [s2] source/residual carrier down to one 256-word row.  It only moves
   the existing iid/full-distribution laws into the row-local odd-DFT carrier
   already analyzed in the residual FFT moment file.  It does not claim random
   contexts, actual/fixed-point FFT behavior, SHAKE coupling, numerical tails,
   or anything beyond this deterministic pushforward boundary. *)

op ideal_final_s2_row_offset (row : int) : int =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_index row 0.

op ideal_final_s2_row_suffix (row : int) : int =
  KeygenM23MatrixSpec.mode2_b_words_i -
  (ideal_final_s2_row_offset row + KeygenM23SingularSpec.singular_words_i).

op ideal_final_s2_full_row_source_projection
    (row : int) (xs : int list) : int list =
  take KeygenM23SingularSpec.singular_words_i
    (drop (ideal_final_s2_row_offset row) xs).

op ideal_final_s2_full_row_source_distribution
    (row : int) : int list distr =
  dmap
    Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_flat_source_distribution
    (ideal_final_s2_full_row_source_projection row).

op ideal_final_s2_full_row_residual_projection
    (row : int) (ys : real list) : real list =
  take KeygenM23SingularSpec.singular_words_i
    (drop (ideal_final_s2_row_offset row) ys).

op ideal_final_s2_row_residual_list_distribution
    (pre_bp avec : BArray8192.t) (row : int) : real list distr =
  dmap
    (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_source_distribution 256)
    (mapi
      (fun j =>
        Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_value pre_bp avec row j)).

op ideal_final_s2_full_row_residual_distribution
    (pre_bp avec : BArray8192.t) (row : int) : real list distr =
  dmap
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_distribution pre_bp avec)
    (ideal_final_s2_full_row_residual_projection row).

op ideal_final_s2_row_residual_fft_of_list (ys : real list) (k : int) : complex =
  odd_dft256 (fun j => cof_real (nth 0%r ys j)) k.

op ideal_final_s2_full_row_residual_odd_dft256_distribution
    (pre_bp avec : BArray8192.t) (row k : int) : complex distr =
  dmap
    (ideal_final_s2_full_row_residual_distribution pre_bp avec row)
    (fun ys => ideal_final_s2_row_residual_fft_of_list ys k).

lemma dmap_dlist_drop_right ['a] (d : 'a distr) n m :
  0 <= n =>
  0 <= m =>
  is_lossless d =>
  dmap (dlist d (n + m)) (drop n) = dlist d m.
proof.
move=> hn hm hll.
rewrite dlist_add 1:hn 1:hm dmap_comp.
have -> :
  dmap
    (dlist d n `*` dlist d m)
    (drop n \o (fun (parts : 'a list * 'a list) => parts.`1 ++ parts.`2)) =
  dmap
    (dlist d n `*` dlist d m)
    (fun (parts : 'a list * 'a list) => parts.`2).
+ apply eq_dmap_in => parts hparts.
   rewrite supp_dprod in hparts.
   move: hparts => [hleft _].
   have hsize := supp_dlist_size d n parts.`1 hn hleft.
   rewrite /(\o) /=.
   exact (drop_size_cat n parts.`1 parts.`2 hsize).
rewrite (dprod_marginalR (dlist d n) (dlist d m) idfun).
have hhead : is_lossless (dlist d n) by apply dlist_ll; exact hll.
rewrite /is_lossless in hhead.
rewrite hhead dmap_id dscalar1.
trivial.
qed.

lemma dmap_dlist_take_drop_middle ['a] (d : 'a distr) n m p :
  0 <= n =>
  0 <= m =>
  0 <= p =>
  is_lossless d =>
  dmap (dlist d (n + m + p)) (take m \o drop n) = dlist d m.
proof.
move=> hn hm hp hll.
have hmp : 0 <= m + p by smt().
have -> : n + m + p = n + (m + p) by ring.
rewrite -dmap_comp.
rewrite (dmap_dlist_drop_right d n (m + p) hn hmp hll).
exact
  (Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
    .dmap_dlist_take_prefix d m p hm hp hll).
qed.

lemma mapi_block_projection ['a 'b]
    (x0 : 'a) (y0 : 'b) (f : int -> 'a -> 'b)
    xs offset len :
  0 <= offset =>
  0 <= len =>
  offset + len <= size xs =>
  take len (drop offset (mapi f xs)) =
  mapi (fun j x => f (offset + j) x) (take len (drop offset xs)).
proof.
move=> hoff hlen hbound.
have hblock : size (take len (drop offset xs)) = len.
+ apply size_takel.
  split; first exact hlen.
  rewrite size_drop //.
  smt(size_ge0).
have hblock_mapi :
    size (take len (drop offset (mapi f xs))) = len.
+ apply size_takel.
  split; first exact hlen.
  rewrite size_drop // size_mapi.
  smt(size_ge0).
apply (eq_from_nth y0).
+ rewrite hblock_mapi size_mapi hblock.
  trivial.
move=> j hj.
have hj0 : 0 <= j by smt().
have hjoff : 0 <= offset + j < size xs by smt().
rewrite nth_take // 1:/#.
rewrite nth_drop //.
rewrite (nth_mapi x0 xs y0 f (offset + j)) 1:hjoff.
rewrite (nth_mapi x0 (take len (drop offset xs)) y0
  (fun jj x => f (offset + jj) x) j) 1:/#.
rewrite nth_take // 1:/#.
rewrite nth_drop //.
qed.

lemma ideal_final_s2_row_index_offsetE row j :
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_index row j =
  ideal_final_s2_row_offset row + j.
proof.
rewrite /ideal_final_s2_row_offset
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_index.
ring.
qed.

lemma ideal_final_s2_full_row_source_distributionE row :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  ideal_final_s2_full_row_source_distribution row =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_source_distribution 256.
proof.
move=> hrow.
rewrite /ideal_final_s2_full_row_source_distribution.
rewrite
  Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
    .ideal_final_s2_flat_source_eq_iid.
have hoff : 0 <= ideal_final_s2_row_offset row.
+ rewrite /ideal_final_s2_row_offset
          /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
            .ideal_final_s2_row_index.
   smt().
have hlen : 0 <= KeygenM23SingularSpec.singular_words_i.
+ rewrite /KeygenM23SingularSpec.singular_words_i.
   trivial.
have hsuf : 0 <= ideal_final_s2_row_suffix row.
+ rewrite /ideal_final_s2_row_suffix /ideal_final_s2_row_offset
          /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
            .ideal_final_s2_row_index
          /KeygenM23SingularFFTSpec.mode2_s2_count_i
          /KeygenM23SingularSpec.singular_words_i
          /KeygenM23MatrixSpec.mode2_b_words_i
          /KeygenM23MatrixSpec.mode2_rows_i
          /KeygenM23MatrixSpec.poly_words_i.
   smt().
have -> :
    KeygenM23MatrixSpec.mode2_b_words_i =
    ideal_final_s2_row_offset row +
    KeygenM23SingularSpec.singular_words_i +
    ideal_final_s2_row_suffix row.
+ rewrite /ideal_final_s2_row_suffix.
   ring.
exact
  (dmap_dlist_take_drop_middle
    Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
      .ideal_eta_centered_trit_distribution
    (ideal_final_s2_row_offset row)
    KeygenM23SingularSpec.singular_words_i
    (ideal_final_s2_row_suffix row)
    hoff hlen hsuf
    Mode2FaithfulSecurityIdealEtaPolynomialLawPostFreeze
      .ideal_eta_centered_trit_lossless).
qed.

lemma ideal_final_s2_full_row_residual_distributionE pre_bp avec row :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  ideal_final_s2_full_row_residual_distribution pre_bp avec row =
  ideal_final_s2_row_residual_list_distribution pre_bp avec row.
proof.
move=> hrow.
rewrite /ideal_final_s2_full_row_residual_distribution
        /Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
          .ideal_final_s2_residual_distribution
        /ideal_final_s2_row_residual_list_distribution.
rewrite dmap_comp.
have -> :
    dmap
      Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
        .ideal_final_s2_flat_source_distribution
      (ideal_final_s2_full_row_residual_projection row \o
       mapi
         (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
           .ideal_final_s2_residual_coord pre_bp avec)) =
    dmap
      Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
        .ideal_final_s2_flat_source_distribution
      (mapi
         (fun j =>
           Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
             .ideal_final_s2_row_residual_value pre_bp avec row j) \o
       ideal_final_s2_full_row_source_projection row).
+ apply eq_dmap_in => xs hxs.
have hsupport :
    size xs = KeygenM23MatrixSpec.mode2_b_words_i /\
    all
      (support
        Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
          .ideal_eta_centered_trit_distribution)
      xs.
+ rewrite
    -Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_flat_source_support.
  exact hxs.
have [hsize _] := hsupport.
have hoff : 0 <= ideal_final_s2_row_offset row.
+ rewrite /ideal_final_s2_row_offset
          /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
            .ideal_final_s2_row_index.
   smt().
have hlen : 0 <= KeygenM23SingularSpec.singular_words_i.
+ rewrite /KeygenM23SingularSpec.singular_words_i.
   trivial.
have hbound :
    ideal_final_s2_row_offset row + KeygenM23SingularSpec.singular_words_i <=
    size xs.
+ rewrite
    /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_index
    /KeygenM23SingularFFTSpec.mode2_s2_count_i in hrow.
  rewrite hsize /ideal_final_s2_row_offset
          /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
            .ideal_final_s2_row_index
          /KeygenM23SingularFFTSpec.mode2_s2_count_i
          /KeygenM23SingularSpec.singular_words_i
          /KeygenM23MatrixSpec.mode2_b_words_i
          /KeygenM23MatrixSpec.mode2_rows_i
          /KeygenM23MatrixSpec.poly_words_i.
   smt().
rewrite /(\o) /ideal_final_s2_full_row_residual_projection
        /ideal_final_s2_full_row_source_projection.
rewrite
  (mapi_block_projection 0 0%r
    (Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
      .ideal_final_s2_residual_coord pre_bp avec)
    xs
    (ideal_final_s2_row_offset row)
    KeygenM23SingularSpec.singular_words_i
    hoff hlen hbound).
have -> :
    (fun j x =>
      Mode2FaithfulSecurityIdealFinalS2ConditionalProductLawPostFreeze
        .ideal_final_s2_residual_coord pre_bp avec
        (ideal_final_s2_row_offset row + j) x) =
    (fun j x =>
      Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
        .ideal_final_s2_row_residual_value pre_bp avec row j x).
+ apply fun_ext => j.
   apply fun_ext => x.
   rewrite /ideal_final_s2_row_offset
           /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
             .ideal_final_s2_row_residual_value
           ideal_final_s2_row_index_offsetE.
   trivial.
trivial.
rewrite -dmap_comp.
have hsource := ideal_final_s2_full_row_source_distributionE row hrow.
rewrite /ideal_final_s2_full_row_source_distribution in hsource.
rewrite hsource.
trivial.
qed.

lemma ideal_final_s2_full_row_residual_odd_dft256_distributionE
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  ideal_final_s2_full_row_residual_odd_dft256_distribution pre_bp avec row k =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_odd_dft256_distribution pre_bp avec row k.
proof.
move=> hrow.
rewrite /ideal_final_s2_full_row_residual_odd_dft256_distribution.
rewrite (ideal_final_s2_full_row_residual_distributionE pre_bp avec row hrow).
rewrite /ideal_final_s2_row_residual_list_distribution
        /ideal_final_s2_row_residual_fft_of_list
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_odd_dft256_distribution.
rewrite dmap_comp.
apply eq_dmap_in => xs hxs.
have hsize :
    size xs = 256
  by rewrite
       /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
         .ideal_final_s2_row_source_distribution
       in hxs;
     exact
       (supp_dlist_size
         Mode2FaithfulSecurityIdealEtaByteLawPostFreeze
           .ideal_eta_centered_trit_distribution
         256 xs _ hxs).
rewrite /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_odd_dft256_sample
        /Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
          .ideal_final_s2_row_residual_slice
        /odd_dft256 /csum256.
rewrite /(\o) /=.
congr.
apply eq_in_map => j hj.
rewrite mem_iota in hj.
have hj256 : 0 <= j < 256 by smt().
simplify.
rewrite (nth_mapi 0 xs 0%r
  (fun jj =>
    Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
      .ideal_final_s2_row_residual_value pre_bp avec row jj) j) 1:hsize 1:hj256.
trivial.
qed.

lemma ideal_final_s2_full_row_residual_fft_real_mean_zero
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (ideal_final_s2_full_row_residual_odd_dft256_distribution pre_bp avec row k)
    creal = 0%r.
proof.
move=> hrow.
rewrite
  (ideal_final_s2_full_row_residual_odd_dft256_distributionE
    pre_bp avec row k hrow).
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_fft_real_mean_zero
      pre_bp avec row k hrow).
qed.

lemma ideal_final_s2_full_row_residual_fft_imag_mean_zero
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (ideal_final_s2_full_row_residual_odd_dft256_distribution pre_bp avec row k)
    cimag = 0%r.
proof.
move=> hrow.
rewrite
  (ideal_final_s2_full_row_residual_odd_dft256_distributionE
    pre_bp avec row k hrow).
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_fft_imag_mean_zero
      pre_bp avec row k hrow).
qed.

lemma ideal_final_s2_full_row_residual_fft_cnorm2E
    pre_bp avec row k :
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  E
    (ideal_final_s2_full_row_residual_odd_dft256_distribution pre_bp avec row k)
    cnorm2 =
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_re_profile pre_bp avec row k 256 +
  Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_im_profile pre_bp avec row k 256.
proof.
move=> hrow.
rewrite
  (ideal_final_s2_full_row_residual_odd_dft256_distributionE
    pre_bp avec row k hrow).
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_fft_cnorm2E
      pre_bp avec row k hrow).
qed.

lemma ideal_final_s2_full_row_residual_fft_cnorm2_le
    pre_bp avec row k :
  Mode2FaithfulSecurityIdealAccumulatorPushforwardPostFreeze
    .ideal_mode2_finalize_context_valid pre_bp avec =>
  0 <= row < KeygenM23SingularFFTSpec.mode2_s2_count_i =>
  0 <= k < 256 =>
  E
    (ideal_final_s2_full_row_residual_odd_dft256_distribution pre_bp avec row k)
    cnorm2 <=
  2048%r / 3%r.
proof.
move=> hctx hrow hk.
rewrite
  (ideal_final_s2_full_row_residual_odd_dft256_distributionE
    pre_bp avec row k hrow).
exact
  (Mode2FaithfulSecurityIdealFinalS2ResidualFFTMomentBoundPostFreeze
    .ideal_final_s2_row_residual_fft_cnorm2_le
      pre_bp avec row k hctx hrow hk).
qed.

end Mode2FaithfulSecurityIdealFinalS2ResidualRowProjectionPostFreeze.
