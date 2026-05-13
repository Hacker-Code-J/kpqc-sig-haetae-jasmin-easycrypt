require import AllCore IntDiv List.
require import HAETAE_Params HAETAE_FIPS202.

theory HAETAE_Algebra.

import HAETAE_Params.
import HAETAE_FIPS202.

type byte = int.
type seed = byte list.
type crh = byte list.
type random_coins = byte list.
type xof256_state = byte list.
type message = byte list.
type context = byte list.
type coeff = int.
type poly = coeff list.
type challenge = poly.
type polyveck = poly list.
type polyvecl = poly list.
type polyvecm = poly list.
type matrix = poly list list.
type hint_t = polyveck.
type sig_token = polyvecl * polyveck * hint_t.

type pkey = seed * polyveck.
type encoded_pkey = byte list.
type skey = seed * int.
type signature = polyveck * poly * crh * challenge * sig_token * int * int.

op secret_key_of_seed (_ : mode) (sd : seed) : skey = (sd, 0).
op poly_zero : poly = nseq n 0.
op polyveck_zero (md : mode) : polyveck = nseq (mode_k md) poly_zero.
op polyvecl_zero (md : mode) : polyvecl = nseq (mode_l md) poly_zero.
op polyvecm_zero (md : mode) : polyvecm = nseq (mode_m md) poly_zero.
op matrix_zero (md : mode) : matrix =
  nseq (mode_k md) (polyvecl_zero md).

lemma poly_zero_size :
  size poly_zero = n.
proof. by rewrite /poly_zero size_nseq /n. qed.

lemma polyveck_zero_size md :
  size (polyveck_zero md) = mode_k md.
proof. by rewrite /polyveck_zero size_nseq; case md. qed.

lemma polyvecl_zero_size md :
  size (polyvecl_zero md) = mode_l md.
proof. by rewrite /polyvecl_zero size_nseq; case md. qed.

lemma polyvecm_zero_size md :
  size (polyvecm_zero md) = mode_m md.
proof. by rewrite /polyvecm_zero /mode_m size_nseq; case md. qed.

op poly_wf (p : poly) : bool = size p = n.
op polyveck_wf (md : mode) (xs : polyveck) : bool =
  size xs = mode_k md /\ all poly_wf xs.
op polyvecl_wf (md : mode) (xs : polyvecl) : bool =
  size xs = mode_l md /\ all poly_wf xs.

lemma polyveck_wf_nth md b row :
  polyveck_wf md b =>
  0 <= row < mode_k md =>
  poly_wf (nth poly_zero b row).
proof.
rewrite /polyveck_wf.
move=> [b_sz b_all] row_rng.
rewrite /poly_wf.
by smt(allP mem_nth).
qed.

op crh_wf (mu : crh) : bool = size mu = crhbytes.
op challenge_coeff_ok (x : coeff) : bool = x = -1 \/ x = 0 \/ x = 1.
op challenge_wf (ch : challenge) : bool =
  poly_wf ch /\ all challenge_coeff_ok ch.
op unit_coeff_ok (x : coeff) : bool = x = -1 \/ x = 1.
op challenge_sparse_at (md : mode) (i : int) (x : coeff) : bool =
  if i < mode_tau md then unit_coeff_ok x else x = 0.
op challenge_sparse (md : mode) (ch : challenge) : bool =
  size ch = n /\
  forall (i : int), 0 <= i /\ i < n =>
    challenge_sparse_at md i (nth 0 ch i).
op poly_unit (p : poly) : bool = poly_wf p /\ all unit_coeff_ok p.
op polyveck_unit (md : mode) (xs : polyveck) : bool =
  polyveck_wf md xs /\ all poly_unit xs.
op polyvecl_unit (md : mode) (xs : polyvecl) : bool =
  polyvecl_wf md xs /\ all poly_unit xs.

lemma poly_zero_wf : poly_wf poly_zero.
proof. by rewrite /poly_wf poly_zero_size. qed.

lemma polyveck_zero_wf md : polyveck_wf md (polyveck_zero md).
proof.
rewrite /polyveck_wf polyveck_zero_size.
split=> //.
rewrite /polyveck_zero all_nseq.
by right; apply poly_zero_wf.
qed.

lemma polyvecl_zero_wf md : polyvecl_wf md (polyvecl_zero md).
proof.
rewrite /polyvecl_wf polyvecl_zero_size.
split=> //.
rewrite /polyvecl_zero all_nseq.
by right; apply poly_zero_wf.
qed.

op coeff_mod (x : coeff) : coeff = x %% q.
op coeff_add (x y : coeff) : coeff = coeff_mod (x + y).
op coeff_neg (x : coeff) : coeff = coeff_mod (-x).
op coeff_sub (x y : coeff) : coeff = coeff_add x (coeff_neg y).
op coeff_mul (x y : coeff) : coeff = coeff_mod (x * y).
op coeff_double (x : coeff) : coeff = coeff_add x x.

op poly_coeff (p : poly) (i : int) : coeff = nth 0 p i.
op poly_normalize (p : poly) : poly =
  mkseq (fun i => coeff_mod (poly_coeff p i)) n.
op poly_add (p r : poly) : poly =
  if p = poly_zero /\ r = poly_zero then poly_zero
  else mkseq
    (fun i => coeff_add (poly_coeff p i) (poly_coeff r i)) n.
op poly_neg (p : poly) : poly =
  if p = poly_zero then poly_zero
  else mkseq (fun i => coeff_neg (poly_coeff p i)) n.
op poly_sub (p r : poly) : poly = poly_add p (poly_neg r).
op poly_double (p : poly) : poly =
  if p = poly_zero then poly_zero
  else mkseq (fun i => coeff_double (poly_coeff p i)) n.

op poly_mul_term (p r : poly) (i j : int) : coeff =
  if j <= i then poly_coeff p j * poly_coeff r (i - j)
  else - (poly_coeff p j * poly_coeff r (n + i - j)).
op poly_mul (p r : poly) : poly =
  if p = poly_zero \/ r = poly_zero then poly_zero
  else mkseq
    (fun i =>
      coeff_mod
        (sumz (map (fun j => poly_mul_term p r i j) (range 0 n)))) n.

op poly_dot (row : poly list) (v : poly list) : poly =
  if row = [] \/ v = [] then poly_zero
  else foldl
    (fun acc (xy : poly * poly) => poly_add acc (poly_mul xy.`1 xy.`2))
    poly_zero
    (zip row v).

op matrix_vec_mul (md : mode) (a : matrix) (v : polyvecl) : polyveck =
  if a = [] \/ a = matrix_zero md then polyveck_zero md
  else mkseq (fun i => poly_dot (nth [] a i) v) (mode_k md).

op polyveck_add (md : mode) (xs ys : polyveck) : polyveck =
  if xs = polyveck_zero md /\ ys = polyveck_zero md then polyveck_zero md
  else mkseq
    (fun i => poly_add (nth poly_zero xs i) (nth poly_zero ys i))
    (mode_k md).
op polyveck_neg (md : mode) (xs : polyveck) : polyveck =
  if xs = polyveck_zero md then polyveck_zero md
  else mkseq (fun i => poly_neg (nth poly_zero xs i)) (mode_k md).
op polyveck_sub (md : mode) (xs ys : polyveck) : polyveck =
  polyveck_add md xs (polyveck_neg md ys).
op polyveck_double (md : mode) (xs : polyveck) : polyveck =
  if xs = polyveck_zero md then polyveck_zero md
  else mkseq (fun i => poly_double (nth poly_zero xs i)) (mode_k md).

op polyvecl_sub (md : mode) (xs ys : polyvecl) : polyvecl =
  mkseq
    (fun i => poly_sub (nth poly_zero xs i) (nth poly_zero ys i))
    (mode_l md).

lemma polyvecl_sub_size md xs ys :
  size (polyvecl_sub md xs ys) = mode_l md.
proof. by rewrite /polyvecl_sub size_mkseq; case md. qed.

lemma poly_add_wf p r : poly_wf (poly_add p r).
proof.
rewrite /poly_wf /poly_add.
case: (p = poly_zero /\ r = poly_zero) => _.
+ by apply poly_zero_size.
by rewrite size_mkseq /n.
qed.

lemma poly_normalize_wf p : poly_wf (poly_normalize p).
proof. by rewrite /poly_wf /poly_normalize size_mkseq /n. qed.

lemma poly_neg_wf p : poly_wf (poly_neg p).
proof.
rewrite /poly_wf /poly_neg.
case: (p = poly_zero) => _.
+ by apply poly_zero_size.
by rewrite size_mkseq /n.
qed.

lemma poly_sub_wf p r : poly_wf (poly_sub p r).
proof. by rewrite /poly_sub; apply poly_add_wf. qed.

lemma poly_double_wf p : poly_wf (poly_double p).
proof.
rewrite /poly_wf /poly_double.
case: (p = poly_zero) => _.
+ by apply poly_zero_size.
by rewrite size_mkseq /n.
qed.

lemma poly_mul_wf p r : poly_wf (poly_mul p r).
proof.
rewrite /poly_wf /poly_mul.
case: (p = poly_zero \/ r = poly_zero) => _.
+ by apply poly_zero_size.
by rewrite size_mkseq /n.
qed.

lemma poly_dot_wf row v : poly_wf (poly_dot row v).
proof.
rewrite /poly_dot.
case: (row = [] \/ v = []) => _.
+ by apply poly_zero_wf.
have h :
  forall zs acc,
    poly_wf acc =>
    poly_wf
      (foldl
        (fun (acc0 : poly) (xy : poly * poly) =>
          poly_add acc0 (poly_mul xy.`1 xy.`2))
        acc zs).
+ elim=> [|xy zs ih] acc acc_wf //=.
  apply ih.
  by apply poly_add_wf.
by apply h; apply poly_zero_wf.
qed.

lemma matrix_vec_mul_wf md a v : polyveck_wf md (matrix_vec_mul md a v).
proof.
rewrite /matrix_vec_mul.
case: (a = [] \/ a = matrix_zero md) => _.
+ by apply polyveck_zero_wf.
rewrite /polyveck_wf size_mkseq.
split.
+ by smt(mode_k_gt0).
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_dot_wf.
qed.

lemma polyveck_add_wf md xs ys : polyveck_wf md (polyveck_add md xs ys).
proof.
rewrite /polyveck_wf /polyveck_add.
case: (xs = polyveck_zero md /\ ys = polyveck_zero md) => _.
+ by apply polyveck_zero_wf.
rewrite size_mkseq.
split.
+ by smt(mode_k_gt0).
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_add_wf.
qed.

lemma polyveck_neg_wf md xs : polyveck_wf md (polyveck_neg md xs).
proof.
rewrite /polyveck_wf /polyveck_neg.
case: (xs = polyveck_zero md) => _.
+ by apply polyveck_zero_wf.
rewrite size_mkseq.
split.
+ by smt(mode_k_gt0).
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_neg_wf.
qed.

lemma polyveck_sub_wf md xs ys : polyveck_wf md (polyveck_sub md xs ys).
proof. by rewrite /polyveck_sub; apply polyveck_add_wf. qed.

lemma polyveck_double_wf md xs : polyveck_wf md (polyveck_double md xs).
proof.
rewrite /polyveck_wf /polyveck_double.
case: (xs = polyveck_zero md) => _.
+ by apply polyveck_zero_wf.
rewrite size_mkseq.
split.
+ by smt(mode_k_gt0).
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_double_wf.
qed.

lemma polyvecl_sub_wf md xs ys : polyvecl_wf md (polyvecl_sub md xs ys).
proof.
rewrite /polyvecl_wf /polyvecl_sub size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_sub_wf.
qed.

op coeff_q_bound (x : coeff) : bool = 0 <= x < q.
op poly_coeffs_q_bound (p : poly) : bool =
  forall i, 0 <= i < n => coeff_q_bound (poly_coeff p i).
op polyveck_coeffs_q_bound (md : mode) (xs : polyveck) : bool =
  forall row, 0 <= row < mode_k md =>
    poly_coeffs_q_bound (nth poly_zero xs row).

lemma coeff_mod_q_bound x : coeff_q_bound (coeff_mod x).
proof. by rewrite /coeff_q_bound /coeff_mod; smt(q_gt0). qed.

lemma poly_zero_coeffs_q_bound : poly_coeffs_q_bound poly_zero.
proof.
rewrite /poly_coeffs_q_bound /poly_coeff /poly_zero.
by smt(q_gt0 nth_nseq).
qed.

lemma poly_add_coeffs_q_bound p r :
  poly_coeffs_q_bound (poly_add p r).
proof.
rewrite /poly_coeffs_q_bound /poly_add => i i_rng.
case: (p = poly_zero /\ r = poly_zero) => _.
+ by apply poly_zero_coeffs_q_bound.
rewrite /poly_coeff nth_mkseq; first by smt().
by apply coeff_mod_q_bound.
qed.

lemma poly_neg_coeffs_q_bound p :
  poly_coeffs_q_bound (poly_neg p).
proof.
rewrite /poly_coeffs_q_bound /poly_neg => i i_rng.
case: (p = poly_zero) => _.
+ by apply poly_zero_coeffs_q_bound.
rewrite /poly_coeff nth_mkseq; first by smt().
by apply coeff_mod_q_bound.
qed.

lemma poly_sub_coeffs_q_bound p r :
  poly_coeffs_q_bound (poly_sub p r).
proof. by rewrite /poly_sub; apply poly_add_coeffs_q_bound. qed.

lemma poly_double_coeffs_q_bound p :
  poly_coeffs_q_bound (poly_double p).
proof.
rewrite /poly_coeffs_q_bound /poly_double => i i_rng.
case: (p = poly_zero) => _.
+ by apply poly_zero_coeffs_q_bound.
rewrite /poly_coeff nth_mkseq; first by smt().
by apply coeff_mod_q_bound.
qed.

lemma poly_mul_coeffs_q_bound p r :
  poly_coeffs_q_bound (poly_mul p r).
proof.
rewrite /poly_coeffs_q_bound /poly_mul => i i_rng.
case: (p = poly_zero \/ r = poly_zero) => _.
+ by apply poly_zero_coeffs_q_bound.
rewrite /poly_coeff nth_mkseq; first by smt().
by apply coeff_mod_q_bound.
qed.

lemma poly_dot_coeffs_q_bound row v :
  poly_coeffs_q_bound (poly_dot row v).
proof.
rewrite /poly_dot.
case: (row = [] \/ v = []) => _.
+ by apply poly_zero_coeffs_q_bound.
have h :
  forall zs acc,
    poly_coeffs_q_bound acc =>
    poly_coeffs_q_bound
      (foldl
        (fun (acc0 : poly) (xy : poly * poly) =>
          poly_add acc0 (poly_mul xy.`1 xy.`2))
        acc zs).
+ elim=> [|xy zs ih] acc acc_bd //=.
  apply ih.
  by apply poly_add_coeffs_q_bound.
by apply h; apply poly_zero_coeffs_q_bound.
qed.

lemma matrix_vec_mul_coeffs_q_bound md a v :
  polyveck_coeffs_q_bound md (matrix_vec_mul md a v).
proof.
rewrite /polyveck_coeffs_q_bound /matrix_vec_mul => row row_rng.
case: (a = [] \/ a = matrix_zero md) => _.
+ rewrite /polyveck_zero.
  have -> : nth poly_zero (nseq (mode_k md) poly_zero) row = poly_zero
    by smt(nth_nseq).
  by apply poly_zero_coeffs_q_bound.
rewrite nth_mkseq; first by smt().
by apply poly_dot_coeffs_q_bound.
qed.

lemma polyveck_zero_coeffs_q_bound md :
  polyveck_coeffs_q_bound md (polyveck_zero md).
proof.
rewrite /polyveck_coeffs_q_bound /polyveck_zero => row row_rng.
have -> : nth poly_zero (nseq (mode_k md) poly_zero) row = poly_zero
  by smt(nth_nseq).
by apply poly_zero_coeffs_q_bound.
qed.

lemma polyveck_add_coeffs_q_bound md xs ys :
  polyveck_coeffs_q_bound md (polyveck_add md xs ys).
proof.
rewrite /polyveck_coeffs_q_bound /polyveck_add => row row_rng.
case: (xs = polyveck_zero md /\ ys = polyveck_zero md) => _.
+ by apply polyveck_zero_coeffs_q_bound.
rewrite nth_mkseq; first by smt().
by apply poly_add_coeffs_q_bound.
qed.

lemma polyveck_neg_coeffs_q_bound md xs :
  polyveck_coeffs_q_bound md (polyveck_neg md xs).
proof.
rewrite /polyveck_coeffs_q_bound /polyveck_neg => row row_rng.
case: (xs = polyveck_zero md) => _.
+ by apply polyveck_zero_coeffs_q_bound.
rewrite nth_mkseq; first by smt().
by apply poly_neg_coeffs_q_bound.
qed.

lemma polyveck_sub_coeffs_q_bound md xs ys :
  polyveck_coeffs_q_bound md (polyveck_sub md xs ys).
proof. by rewrite /polyveck_sub; apply polyveck_add_coeffs_q_bound. qed.

lemma polyveck_double_coeffs_q_bound md xs :
  polyveck_coeffs_q_bound md (polyveck_double md xs).
proof.
rewrite /polyveck_coeffs_q_bound /polyveck_double => row row_rng.
case: (xs = polyveck_zero md) => _.
+ by apply polyveck_zero_coeffs_q_bound.
rewrite nth_mkseq; first by smt().
by apply poly_double_coeffs_q_bound.
qed.

op z1_alpha : int = 256.

op coeff_decompose_z1_low (x : coeff) : coeff =
  let lb = x %% z1_alpha in
  if z1_alpha %/ 2 <= lb then lb - z1_alpha else lb.
op coeff_decompose_z1_high (x : coeff) : coeff =
  (x + (z1_alpha %/ 2)) %/ z1_alpha.
op coeff_lsb (x : coeff) : coeff = x %% 2.
op coeff_decompose_vk_low (x : coeff) : coeff =
  if x %% 2 = 0 then 0
  else if (x %/ 2) %% 2 = 0 then 1
  else -1.
op coeff_decompose_vk_high (x : coeff) : coeff =
  (x - coeff_decompose_vk_low x) %/ 2.
op coeff_decompose_hint_high (md : mode) (x : coeff) : coeff =
  let alpha = mode_alpha_hint md in
  let hb = (x + (alpha %/ 2)) %/ alpha in
  let top = (dq - 2) %/ alpha in
  if top <= hb then hb - top else hb.
op coeff_compose_z1 (hi lo : coeff) : coeff = hi * z1_alpha + lo.

op poly_highbits (p : poly) : poly =
  mkseq (fun i => coeff_decompose_z1_high (poly_coeff p i)) n.
op poly_lowbits (p : poly) : poly =
  mkseq (fun i => coeff_decompose_z1_low (poly_coeff p i)) n.
op poly_lsb (p : poly) : poly =
  mkseq (fun i => coeff_lsb (poly_coeff p i)) n.
op poly_vk_lowbits (p : poly) : poly =
  mkseq (fun i => coeff_decompose_vk_low (poly_coeff p i)) n.
op poly_vk_highbits (p : poly) : poly =
  mkseq (fun i => coeff_decompose_vk_high (poly_coeff p i)) n.
op poly_compose_z1 (hi lo : poly) : poly =
  mkseq
    (fun i =>
      coeff_compose_z1 (poly_coeff hi i) (poly_coeff lo i)) n.
op poly_hint_highbits (md : mode) (p : poly) : poly =
  mkseq (fun i => coeff_decompose_hint_high md (poly_coeff p i)) n.

op polyvecl_highbits (md : mode) (xs : polyvecl) : polyvecl =
  mkseq (fun i => poly_highbits (nth poly_zero xs i)) (mode_l md).
op polyvecl_lowbits (md : mode) (xs : polyvecl) : polyvecl =
  mkseq (fun i => poly_lowbits (nth poly_zero xs i)) (mode_l md).
op polyveck_highbits_hint (md : mode) (xs : polyveck) : polyveck =
  mkseq (fun i => poly_hint_highbits md (nth poly_zero xs i)) (mode_k md).
op polyveck_vk_lowbits (md : mode) (xs : polyveck) : polyveck =
  mkseq (fun i => poly_vk_lowbits (nth poly_zero xs i)) (mode_k md).
op polyveck_vk_highbits (md : mode) (xs : polyveck) : polyveck =
  mkseq (fun i => poly_vk_highbits (nth poly_zero xs i)) (mode_k md).
op polyveck_mul_alpha (md : mode) (xs : polyveck) : polyveck =
  mkseq
    (fun i =>
      mkseq
        (fun j => mode_alpha_hint md * poly_coeff (nth poly_zero xs i) j)
        n)
    (mode_k md).

lemma poly_highbits_wf p : poly_wf (poly_highbits p).
proof. by rewrite /poly_wf /poly_highbits size_mkseq /n. qed.

lemma poly_lowbits_wf p : poly_wf (poly_lowbits p).
proof. by rewrite /poly_wf /poly_lowbits size_mkseq /n. qed.

lemma poly_lsb_wf p : poly_wf (poly_lsb p).
proof. by rewrite /poly_wf /poly_lsb size_mkseq /n. qed.

lemma poly_vk_lowbits_wf p : poly_wf (poly_vk_lowbits p).
proof. by rewrite /poly_wf /poly_vk_lowbits size_mkseq /n. qed.

lemma poly_vk_highbits_wf p : poly_wf (poly_vk_highbits p).
proof. by rewrite /poly_wf /poly_vk_highbits size_mkseq /n. qed.

lemma poly_compose_z1_wf hi lo : poly_wf (poly_compose_z1 hi lo).
proof. by rewrite /poly_wf /poly_compose_z1 size_mkseq /n. qed.

lemma poly_hint_highbits_wf md p : poly_wf (poly_hint_highbits md p).
proof. by rewrite /poly_wf /poly_hint_highbits size_mkseq /n. qed.

lemma polyvecl_highbits_wf md xs :
  polyvecl_wf md (polyvecl_highbits md xs).
proof.
rewrite /polyvecl_wf /polyvecl_highbits size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_highbits_wf.
qed.

lemma polyvecl_lowbits_wf md xs :
  polyvecl_wf md (polyvecl_lowbits md xs).
proof.
rewrite /polyvecl_wf /polyvecl_lowbits size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_lowbits_wf.
qed.

lemma polyveck_highbits_hint_wf md xs :
  polyveck_wf md (polyveck_highbits_hint md xs).
proof.
rewrite /polyveck_wf /polyveck_highbits_hint size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_hint_highbits_wf.
qed.

lemma polyveck_vk_lowbits_wf md xs :
  polyveck_wf md (polyveck_vk_lowbits md xs).
proof.
rewrite /polyveck_wf /polyveck_vk_lowbits size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_vk_lowbits_wf.
qed.

lemma polyveck_vk_highbits_wf md xs :
  polyveck_wf md (polyveck_vk_highbits md xs).
proof.
rewrite /polyveck_wf /polyveck_vk_highbits size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_vk_highbits_wf.
qed.

lemma polyveck_mul_alpha_wf md xs :
  polyveck_wf md (polyveck_mul_alpha md xs).
proof.
rewrite /polyveck_wf /polyveck_mul_alpha size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by rewrite /poly_wf size_mkseq /n.
qed.

op public_key_seed_poly (tag : int) (src : byte list) : poly =
  mkseq (fun i => coeff_mod (tag + i + nth 0 src i)) n.
op public_key_seed_polyvecl
   (md : mode) (tag : int) (src : byte list) : polyvecl =
  mkseq
    (fun i => public_key_seed_poly (tag + i) (i :: src))
    (mode_l md).
op public_key_seed_polyveck
   (md : mode) (tag : int) (src : byte list) : polyveck =
  mkseq
    (fun i => public_key_seed_poly (tag + i) (i :: src))
    (mode_k md).
op haetae_keygen_seedbuf_bytes : int = 2 * seedbytes + crhbytes.
op haetae_reference_keygen_seedbuf_bytes : int =
  2 * seedbytes + crhbytes.
op haetae_reference_keygen_xof_absorb_bytes : int = seedbytes.
op haetae_reference_keygen_xof_squeeze_bytes : int =
  haetae_reference_keygen_seedbuf_bytes.
op haetae_keygen_rhoprime_offset : int = 0.
op haetae_keygen_sigma_offset : int = seedbytes.
op haetae_keygen_key_offset : int = seedbytes + crhbytes.
op haetae_shake256_rate_bytes : int = shake256_rate_bytes.
op haetae_shake256_domain_separator : byte = shake256_domain_separator.
op haetae_shake256_bytes (input : byte list) (outlen : int) : byte list =
  shake256 input (size input) outlen.
op haetae_seed_slice (src : byte list) (offset len : int) : byte list =
  mkseq (fun i => nth 0 src (offset + i)) len.
op haetae_xof256_absorb_input
   (input : byte list) (inlen : int) : byte list =
  haetae_seed_slice input 0 inlen.
op haetae_xof256_absorb_once
   (input : byte list) (inlen : int) : xof256_state =
  shake256_absorb_once (haetae_xof256_absorb_input input inlen) inlen.
op haetae_xof256_squeeze
   (st : xof256_state) (outlen : int) : byte list =
  shake256_squeeze st outlen.
op haetae_xof256_absorb_once_squeeze
   (input : byte list) (inlen outlen : int) : byte list =
  haetae_xof256_squeeze
    (haetae_xof256_absorb_once input inlen)
    outlen.
op haetae_reference_keygen_seedbuf_after_memcpy (sd : seed) : byte list =
  mkseq
    (fun i => if i < seedbytes then nth 0 sd i else 0)
    haetae_reference_keygen_seedbuf_bytes.
op haetae_reference_keygen_xof_input (sd : seed) : byte list =
  haetae_seed_slice
    (haetae_reference_keygen_seedbuf_after_memcpy sd)
    0 haetae_reference_keygen_xof_absorb_bytes.
op haetae_keygen_xof_seedbuf (sd : seed) : byte list =
  haetae_xof256_absorb_once_squeeze
    (haetae_reference_keygen_seedbuf_after_memcpy sd)
    haetae_reference_keygen_xof_absorb_bytes
    haetae_reference_keygen_xof_squeeze_bytes.
op haetae_reference_keygen_xof256_seedbuf (sd : seed) : byte list =
  haetae_keygen_xof_seedbuf sd.
op haetae_keygen_seedbuf_rhoprime (seedbuf : byte list) : seed =
  haetae_seed_slice seedbuf haetae_keygen_rhoprime_offset seedbytes.
op haetae_keygen_seedbuf_sigma (seedbuf : byte list) : crh =
  haetae_seed_slice seedbuf haetae_keygen_sigma_offset crhbytes.
op haetae_keygen_seedbuf_key (seedbuf : byte list) : seed =
  haetae_seed_slice seedbuf haetae_keygen_key_offset seedbytes.
op haetae_keygen_seedbuf_layout_wf (seedbuf : byte list) : bool =
  size seedbuf = haetae_reference_keygen_seedbuf_bytes /\
  haetae_keygen_rhoprime_offset = 0 /\
  haetae_keygen_sigma_offset = seedbytes /\
  haetae_keygen_key_offset = seedbytes + crhbytes /\
  size (haetae_keygen_seedbuf_rhoprime seedbuf) = seedbytes /\
  size (haetae_keygen_seedbuf_sigma seedbuf) = crhbytes /\
  size (haetae_keygen_seedbuf_key seedbuf) = seedbytes.
op haetae_reference_keygen_xof_call_wf
   (sd : seed) (seedbuf : byte list) : bool =
  size sd = haetae_reference_keygen_xof_absorb_bytes /\
  size (haetae_reference_keygen_seedbuf_after_memcpy sd) =
    haetae_reference_keygen_seedbuf_bytes /\
  haetae_xof256_absorb_input
    (haetae_reference_keygen_seedbuf_after_memcpy sd)
    haetae_reference_keygen_xof_absorb_bytes =
    haetae_reference_keygen_xof_input sd /\
  shake256_absorb_once_short_domain
    (haetae_reference_keygen_xof_input sd)
    haetae_reference_keygen_xof_absorb_bytes /\
  haetae_reference_keygen_xof_squeeze_bytes < haetae_shake256_rate_bytes /\
  haetae_xof256_absorb_once
    (haetae_reference_keygen_seedbuf_after_memcpy sd)
    haetae_reference_keygen_xof_absorb_bytes =
    shake256_absorb_once
      (haetae_reference_keygen_xof_input sd)
      haetae_reference_keygen_xof_absorb_bytes /\
  seedbuf =
    shake256_squeeze
      (haetae_xof256_absorb_once
        (haetae_reference_keygen_seedbuf_after_memcpy sd)
        haetae_reference_keygen_xof_absorb_bytes)
      haetae_reference_keygen_xof_squeeze_bytes /\
  size seedbuf = haetae_reference_keygen_xof_squeeze_bytes /\
  haetae_reference_keygen_xof_absorb_bytes = seedbytes /\
  haetae_reference_keygen_xof_squeeze_bytes =
    haetae_reference_keygen_seedbuf_bytes.
op haetae_keygen_rhoprime (sd : seed) : seed =
  haetae_keygen_seedbuf_rhoprime
    (haetae_reference_keygen_xof256_seedbuf sd).
op haetae_keygen_sigma (sd : seed) : crh =
  haetae_keygen_seedbuf_sigma
    (haetae_reference_keygen_xof256_seedbuf sd).
op haetae_keygen_key (sd : seed) : seed =
  haetae_keygen_seedbuf_key
    (haetae_reference_keygen_xof256_seedbuf sd).
op haetae_keygen_counter_next (md : mode) (counter : int) : int =
  counter + mode_m md + mode_k md.
op haetae_keygen_first_accept_counter (_ : mode) (_ : seed) : int = 0.
op haetae_keygen_sampler_seed (sigma : crh) (counter : int) : seed =
  mkseq
    (fun i => nth 0 sigma (i %% crhbytes) + counter + i)
    seedbytes.

op public_matrix_seed (md : mode) (sd : seed) : matrix =
  mkseq
    (fun i => public_key_seed_polyvecl md (101 + i) (i :: sd))
    (mode_k md).
op public_secret_vector_seed (md : mode) (sd : seed) : polyvecl =
  public_key_seed_polyvecl md 211 sd.
op public_error_vector_seed (md : mode) (sd : seed) : polyveck =
  public_key_seed_polyveck md 307 sd.
op public_rounding_vector_seed (md : mode) (sd : seed) : polyveck =
  public_key_seed_polyveck md 401 sd.

op haetae_keygen_a0_matrix (md : mode) (sd : seed) : matrix =
  public_matrix_seed md sd.
op haetae_keygen_secret_vector (md : mode) (sd : seed) : polyvecl =
  public_secret_vector_seed md sd.
op haetae_keygen_error_vector (md : mode) (sd : seed) : polyveck =
  public_error_vector_seed md sd.
op haetae_keygen_raw_public_vector (md : mode) (sd : seed) : polyveck =
  polyveck_add md
    (matrix_vec_mul md
      (haetae_keygen_a0_matrix md sd)
      (haetae_keygen_secret_vector md sd))
    (haetae_keygen_error_vector md sd).
op haetae_keygen_mode23_predecompose_vector
   (md : mode) (sd : seed) : polyveck =
  polyveck_add md
    (public_rounding_vector_seed md sd)
    (haetae_keygen_raw_public_vector md sd).
op haetae_keygen_mode23_public_vector
   (md : mode) (sd : seed) : polyveck =
  polyveck_vk_highbits md (haetae_keygen_mode23_predecompose_vector md sd).
op haetae_keygen_mode23_rounding_lowbits
   (md : mode) (sd : seed) : polyveck =
  polyveck_vk_lowbits md (haetae_keygen_mode23_predecompose_vector md sd).
op haetae_keygen_mode23_adjusted_error_vector
   (md : mode) (sd : seed) : polyveck =
  polyveck_sub md
    (haetae_keygen_error_vector md sd)
    (haetae_keygen_mode23_rounding_lowbits md sd).
op haetae_keygen_mode5_public_vector
   (md : mode) (sd : seed) : polyveck =
  polyveck_neg md (polyveck_double md (haetae_keygen_raw_public_vector md sd)).
op haetae_public_key_vector_from_relation
   (md : mode) (sd : seed) (s : polyvecl) (e : polyveck) : polyveck =
  with md = Mode2 =>
    let raw =
      polyveck_add md
        (matrix_vec_mul md (public_matrix_seed md sd) s)
        e in
    polyveck_vk_highbits md
      (polyveck_add md (public_rounding_vector_seed md sd) raw)
  with md = Mode3 =>
    let raw =
      polyveck_add md
        (matrix_vec_mul md (public_matrix_seed md sd) s)
        e in
    polyveck_vk_highbits md
      (polyveck_add md (public_rounding_vector_seed md sd) raw)
  with md = Mode5 =>
    let raw =
      polyveck_add md
        (matrix_vec_mul md (public_matrix_seed md sd) s)
        e in
    polyveck_neg md (polyveck_double md raw).
op haetae_keygen_public_vector (md : mode) (sd : seed) : polyveck =
  haetae_public_key_vector_from_relation md sd
    (haetae_keygen_secret_vector md sd)
    (haetae_keygen_error_vector md sd).
op public_key_vector_seed (md : mode) (sd : seed) : polyveck =
  haetae_keygen_public_vector md sd.
op public_key_relation
   (md : mode) (pk : pkey) (s : polyvecl) (e : polyveck) : bool =
  pk.`2 = haetae_public_key_vector_from_relation md pk.`1 s e.
op public_key_equation_holds (md : mode) (pk : pkey) : bool =
  public_key_relation md pk
    (public_secret_vector_seed md pk.`1)
    (public_error_vector_seed md pk.`1).
op haetae_reference_polymatkm_expand_matA
   (md : mode) (rhoprime : seed) : matrix =
  public_matrix_seed md rhoprime.
op haetae_reference_polyveck_expand_vecA
   (md : mode) (rhoprime : seed) : polyveck =
  public_rounding_vector_seed md rhoprime.
op haetae_reference_polyvecmk_expand_S_s1
   (md : mode) (sigma : crh) (counter : int) : polyvecl =
  public_secret_vector_seed md (haetae_keygen_sampler_seed sigma counter).
op haetae_reference_polyvecmk_expand_S_s2
   (md : mode) (sigma : crh) (counter : int) : polyveck =
  public_error_vector_seed md (haetae_keygen_sampler_seed sigma counter).
op haetae_reference_keygen_secret_vector
   (md : mode) (sd : seed) : polyvecl =
  haetae_reference_polyvecmk_expand_S_s1 md
    (haetae_keygen_sigma sd)
    (haetae_keygen_first_accept_counter md sd).
op haetae_reference_keygen_error_vector
   (md : mode) (sd : seed) : polyveck =
  haetae_reference_polyvecmk_expand_S_s2 md
    (haetae_keygen_sigma sd)
    (haetae_keygen_first_accept_counter md sd).
op haetae_reference_keygen_a0_matrix
   (md : mode) (sd : seed) : matrix =
  haetae_reference_polymatkm_expand_matA md (haetae_keygen_rhoprime sd).
op haetae_reference_keygen_raw_public_vector
   (md : mode) (sd : seed) : polyveck =
  polyveck_add md
    (matrix_vec_mul md
      (haetae_reference_keygen_a0_matrix md sd)
      (haetae_reference_keygen_secret_vector md sd))
    (haetae_reference_keygen_error_vector md sd).
op haetae_reference_keygen_mode23_predecompose_vector
   (md : mode) (sd : seed) : polyveck =
  polyveck_add md
    (haetae_reference_polyveck_expand_vecA md (haetae_keygen_rhoprime sd))
    (haetae_reference_keygen_raw_public_vector md sd).
op haetae_reference_keygen_mode23_public_vector
   (md : mode) (sd : seed) : polyveck =
  polyveck_vk_highbits md
    (haetae_reference_keygen_mode23_predecompose_vector md sd).
op haetae_reference_keygen_mode23_rounding_lowbits
   (md : mode) (sd : seed) : polyveck =
  polyveck_vk_lowbits md
    (haetae_reference_keygen_mode23_predecompose_vector md sd).
op haetae_reference_keygen_mode23_adjusted_error_vector
   (md : mode) (sd : seed) : polyveck =
  polyveck_sub md
    (haetae_reference_keygen_error_vector md sd)
    (haetae_reference_keygen_mode23_rounding_lowbits md sd).
op haetae_reference_keygen_mode5_public_vector
   (md : mode) (sd : seed) : polyveck =
  polyveck_neg md
    (polyveck_double md (haetae_reference_keygen_raw_public_vector md sd)).
op haetae_reference_keygen_public_vector
   (md : mode) (sd : seed) : polyveck =
  haetae_public_key_vector_from_relation md
    (haetae_keygen_rhoprime sd)
    (haetae_reference_keygen_secret_vector md sd)
    (haetae_reference_keygen_error_vector md sd).
op packed_haetae_reference_public_key
   (md : mode) (sd : seed) : pkey =
  (haetae_keygen_rhoprime sd, haetae_reference_keygen_public_vector md sd).
op haetae_reference_keygen_seed_flow_wf (md : mode) (sd : seed) : bool =
  haetae_reference_keygen_a0_matrix md sd =
    haetae_reference_polymatkm_expand_matA md (haetae_keygen_rhoprime sd) /\
  haetae_reference_keygen_secret_vector md sd =
    haetae_reference_polyvecmk_expand_S_s1 md
      (haetae_keygen_sigma sd)
      (haetae_keygen_first_accept_counter md sd) /\
  haetae_reference_keygen_error_vector md sd =
    haetae_reference_polyvecmk_expand_S_s2 md
      (haetae_keygen_sigma sd)
      (haetae_keygen_first_accept_counter md sd) /\
  haetae_reference_keygen_public_vector md sd =
    haetae_public_key_vector_from_relation md
      (haetae_keygen_rhoprime sd)
      (haetae_reference_keygen_secret_vector md sd)
      (haetae_reference_keygen_error_vector md sd) /\
  (packed_haetae_reference_public_key md sd).`1 =
    haetae_keygen_rhoprime sd /\
  (packed_haetae_reference_public_key md sd).`2 =
    haetae_reference_keygen_public_vector md sd.

op haetae_mode23_qj_vector (md : mode) (sd : seed) : polyveck =
  public_rounding_vector_seed md sd.
op haetae_mode23_verification_column
   (md : mode) (b qj : polyveck) : polyveck =
  polyveck_double md (polyveck_sub md qj (polyveck_double md b)).
op haetae_mode5_verification_column
   (md : mode) (b : polyveck) : polyveck =
  mkseq (fun i => poly_normalize (nth poly_zero b i)) (mode_k md).
op public_key_mode23_column (md : mode) (pk : pkey) : polyveck =
  haetae_mode23_verification_column md pk.`2
    (haetae_mode23_qj_vector md pk.`1).
op public_key_mode5_column (md : mode) (pk : pkey) : polyveck =
  haetae_mode5_verification_column md pk.`2.
op public_key_verification_column (md : mode) (pk : pkey) : polyveck =
  with md = Mode2 => public_key_mode23_column md pk
  with md = Mode3 => public_key_mode23_column md pk
  with md = Mode5 => public_key_mode5_column md pk.
op haetae_verification_column_from_unpacked
   (md : mode) (sd : seed) (b : polyveck) : polyveck =
  with md = Mode2 =>
    haetae_mode23_verification_column md b
      (haetae_mode23_qj_vector md sd)
  with md = Mode3 =>
    haetae_mode23_verification_column md b
      (haetae_mode23_qj_vector md sd)
  with md = Mode5 =>
    haetae_mode5_verification_column md b.
op haetae_verification_matrix_from_unpacked
   (md : mode) (sd : seed) (b : polyveck) : matrix =
  mkseq
    (fun i =>
      mkseq
        (fun j =>
          if j = 0
          then nth poly_zero
                 (haetae_verification_column_from_unpacked md sd b) i
          else poly_double
                 (nth poly_zero
                   (nth [] (haetae_keygen_a0_matrix md sd) i)
                   (j - 1)))
        (mode_l md))
    (mode_k md).
op packed_haetae_public_key (md : mode) (sd : seed) : pkey =
  (sd, haetae_keygen_public_vector md sd).
op packed_haetae_verification_matrix (md : mode) (pk : pkey) : matrix =
  haetae_verification_matrix_from_unpacked md pk.`1 pk.`2.
op packed_haetae_keygen_verification_matrix (md : mode) (sd : seed) :
  matrix =
  packed_haetae_verification_matrix md (packed_haetae_public_key md sd).
op public_verification_matrix (md : mode) (pk : pkey) : matrix =
  packed_haetae_verification_matrix md pk.
op challenge_embedding (md : mode) (ch : challenge) : polyvecl =
  mkseq (fun i => if i = 0 then ch else poly_zero) (mode_l md).
op public_key_challenge_term
   (md : mode) (pk : pkey) (ch : challenge) : polyveck =
  matrix_vec_mul md (public_verification_matrix md pk)
    (challenge_embedding md ch).
op reconstructed_highbits
   (md : mode) (aux pk_ch : polyveck) : polyveck =
  polyveck_add md aux pk_ch.

op public_key_of_secret (md : mode) (sk : skey) : pkey =
  (sk.`1, public_key_vector_seed md sk.`1).
op haetae_public_key_body_bytes (md : mode) : int =
  mode_k md * mode_polyq_packedbytes md.
op haetae_public_key_bytes (md : mode) : int =
  mode_publickeybytes md.
op haetae_public_key_encoding_wf (md : mode) (enc : encoded_pkey) : bool =
  size enc = haetae_public_key_bytes md.
op haetae_public_key_unpacked_wf (md : mode) (pk : pkey) : bool =
  size pk.`1 = seedbytes /\ polyveck_wf md pk.`2.
op haetae_pack_seed (sd : seed) : byte list =
  mkseq (fun i => nth 0 sd i) seedbytes.
op haetae_unpack_seed (enc : encoded_pkey) : seed =
  mkseq (fun i => nth 0 enc i) seedbytes.
op haetae_pack_poly_q (md : mode) (p : poly) : byte list =
  mkseq
    (fun i => if i < n then poly_coeff p i else 0)
    (mode_polyq_packedbytes md).
op haetae_unpack_poly_q_at
   (md : mode) (enc : encoded_pkey) (offset : int) : poly =
  mkseq (fun i => nth 0 enc (offset + i)) n.

op haetae_byte_modulus : int = 256.
op haetae_polyq_mode23_bound : int = 32768.
op haetae_polyq_mode5_bound : int = 65536.

op haetae_byte_norm (x : int) : byte = x %% haetae_byte_modulus.

op haetae_polyq_coeff_bound (md : mode) : int =
  with md = Mode2 => haetae_polyq_mode23_bound
  with md = Mode3 => haetae_polyq_mode23_bound
  with md = Mode5 => haetae_polyq_mode5_bound.

op haetae_polyq_coeffs_wf (md : mode) (p : poly) : bool =
  poly_wf p /\
  forall i, 0 <= i < n =>
    0 <= poly_coeff p i < haetae_polyq_coeff_bound md.

op haetae_polyveck_polyq_coeffs_wf
   (md : mode) (b : polyveck) : bool =
  polyveck_wf md b /\
  forall row, 0 <= row < mode_k md =>
    haetae_polyq_coeffs_wf md (nth poly_zero b row).

lemma coeff_decompose_hint_high_polyq_bound md x :
  coeff_q_bound x =>
  0 <= coeff_decompose_hint_high md x < haetae_polyq_coeff_bound md.
proof.
case: md; rewrite /coeff_q_bound /coeff_decompose_hint_high
                  /mode_alpha_hint /haetae_polyq_coeff_bound
                  /haetae_polyq_mode23_bound /haetae_polyq_mode5_bound
                  /dq /q; smt().
qed.

lemma poly_hint_highbits_polyq_wf md p :
  poly_coeffs_q_bound p =>
  haetae_polyq_coeffs_wf md (poly_hint_highbits md p).
proof.
move=> p_bd.
rewrite /haetae_polyq_coeffs_wf.
split.
+ by apply poly_hint_highbits_wf.
move=> i i_rng.
rewrite /poly_hint_highbits /poly_coeff nth_mkseq; first by smt().
apply coeff_decompose_hint_high_polyq_bound.
by apply p_bd.
qed.

lemma polyveck_highbits_hint_polyq_wf md xs :
  polyveck_coeffs_q_bound md xs =>
  haetae_polyveck_polyq_coeffs_wf md (polyveck_highbits_hint md xs).
proof.
move=> xs_bd.
rewrite /haetae_polyveck_polyq_coeffs_wf.
split.
+ by apply polyveck_highbits_hint_wf.
move=> row row_rng.
rewrite /polyveck_highbits_hint nth_mkseq; first by smt().
apply poly_hint_highbits_polyq_wf.
by apply xs_bd.
qed.

lemma coeff_decompose_vk_high_mode23_polyq_bound md x :
  (md = Mode2 \/ md = Mode3) =>
  coeff_q_bound x =>
  0 <= coeff_decompose_vk_high x < haetae_polyq_coeff_bound md.
proof.
case: md; rewrite /coeff_q_bound /coeff_decompose_vk_high
                  /coeff_decompose_vk_low /haetae_polyq_coeff_bound
                  /haetae_polyq_mode23_bound /haetae_polyq_mode5_bound
                  /q; smt().
qed.

lemma poly_vk_highbits_mode23_polyq_wf md p :
  (md = Mode2 \/ md = Mode3) =>
  poly_coeffs_q_bound p =>
  haetae_polyq_coeffs_wf md (poly_vk_highbits p).
proof.
move=> md23 p_bd.
rewrite /haetae_polyq_coeffs_wf.
split.
+ by apply poly_vk_highbits_wf.
move=> i i_rng.
rewrite /poly_vk_highbits /poly_coeff nth_mkseq; first by smt().
apply coeff_decompose_vk_high_mode23_polyq_bound; first by apply md23.
by apply p_bd.
qed.

lemma polyveck_vk_highbits_mode23_polyq_wf md xs :
  (md = Mode2 \/ md = Mode3) =>
  polyveck_coeffs_q_bound md xs =>
  haetae_polyveck_polyq_coeffs_wf md (polyveck_vk_highbits md xs).
proof.
move=> md23 xs_bd.
rewrite /haetae_polyveck_polyq_coeffs_wf.
split.
+ by apply polyveck_vk_highbits_wf.
move=> row row_rng.
rewrite /polyveck_vk_highbits nth_mkseq; first by smt().
apply poly_vk_highbits_mode23_polyq_wf; first by apply md23.
by apply xs_bd.
qed.

lemma coeff_q_bound_mode5_polyq_bound x :
  coeff_q_bound x =>
  0 <= x < haetae_polyq_coeff_bound Mode5.
proof.
by rewrite /coeff_q_bound /haetae_polyq_coeff_bound
           /haetae_polyq_mode5_bound /q; smt().
qed.

lemma poly_q_bound_mode5_polyq_wf p :
  poly_wf p =>
  poly_coeffs_q_bound p =>
  haetae_polyq_coeffs_wf Mode5 p.
proof.
move=> p_wf p_bd.
rewrite /haetae_polyq_coeffs_wf.
split; first by apply p_wf.
move=> i i_rng.
by apply coeff_q_bound_mode5_polyq_bound; apply p_bd.
qed.

lemma polyveck_q_bound_mode5_polyq_wf xs :
  polyveck_wf Mode5 xs =>
  polyveck_coeffs_q_bound Mode5 xs =>
  haetae_polyveck_polyq_coeffs_wf Mode5 xs.
proof.
move=> xs_wf xs_bd.
rewrite /haetae_polyveck_polyq_coeffs_wf.
split; first by apply xs_wf.
move=> row row_rng.
apply poly_q_bound_mode5_polyq_wf.
+ by apply (polyveck_wf_nth Mode5 xs row).
by apply (xs_bd row row_rng).
qed.

op haetae_pack_poly_q_mode23_byte
   (p : poly) (blk ofs : int) : byte =
  let c0 = poly_coeff p (8 * blk + 0) in
  let c1 = poly_coeff p (8 * blk + 1) in
  let c2 = poly_coeff p (8 * blk + 2) in
  let c3 = poly_coeff p (8 * blk + 3) in
  let c4 = poly_coeff p (8 * blk + 4) in
  let c5 = poly_coeff p (8 * blk + 5) in
  let c6 = poly_coeff p (8 * blk + 6) in
  let c7 = poly_coeff p (8 * blk + 7) in
  if ofs = 0 then haetae_byte_norm c0
  else if ofs = 1 then
    haetae_byte_norm ((c0 %/ 256) %% 128 + (c1 %% 2) * 128)
  else if ofs = 2 then haetae_byte_norm (c1 %/ 2)
  else if ofs = 3 then
    haetae_byte_norm ((c1 %/ 512) %% 64 + (c2 %% 4) * 64)
  else if ofs = 4 then haetae_byte_norm (c2 %/ 4)
  else if ofs = 5 then
    haetae_byte_norm ((c2 %/ 1024) %% 32 + (c3 %% 8) * 32)
  else if ofs = 6 then haetae_byte_norm (c3 %/ 8)
  else if ofs = 7 then
    haetae_byte_norm ((c3 %/ 2048) %% 16 + (c4 %% 16) * 16)
  else if ofs = 8 then haetae_byte_norm (c4 %/ 16)
  else if ofs = 9 then
    haetae_byte_norm ((c4 %/ 4096) %% 8 + (c5 %% 32) * 8)
  else if ofs = 10 then haetae_byte_norm (c5 %/ 32)
  else if ofs = 11 then
    haetae_byte_norm ((c5 %/ 8192) %% 4 + (c6 %% 64) * 4)
  else if ofs = 12 then haetae_byte_norm (c6 %/ 64)
  else if ofs = 13 then
    haetae_byte_norm ((c6 %/ 16384) %% 2 + (c7 %% 128) * 2)
  else haetae_byte_norm (c7 %/ 128).

op haetae_pack_poly_q_mode5_byte (p : poly) (j : int) : byte =
  let c = poly_coeff p (j %/ 2) in
  if j %% 2 = 0 then haetae_byte_norm c
  else haetae_byte_norm (c %/ 256).

op haetae_pack_poly_q_ref (md : mode) (p : poly) : byte list =
  with md = Mode2 =>
    mkseq
      (fun j => haetae_pack_poly_q_mode23_byte p (j %/ 15) (j %% 15))
      (mode_polyq_packedbytes Mode2)
  with md = Mode3 =>
    mkseq
      (fun j => haetae_pack_poly_q_mode23_byte p (j %/ 15) (j %% 15))
      (mode_polyq_packedbytes Mode3)
  with md = Mode5 =>
    mkseq
      (fun j => haetae_pack_poly_q_mode5_byte p j)
      (mode_polyq_packedbytes Mode5).

op haetae_unpack_poly_q_mode23_coeff_at
   (enc : encoded_pkey) (base blk ofs : int) : coeff =
  let a0 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 0)) in
  let a1 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 1)) in
  let a2 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 2)) in
  let a3 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 3)) in
  let a4 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 4)) in
  let a5 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 5)) in
  let a6 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 6)) in
  let a7 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 7)) in
  let a8 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 8)) in
  let a9 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 9)) in
  let a10 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 10)) in
  let a11 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 11)) in
  let a12 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 12)) in
  let a13 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 13)) in
  let a14 = haetae_byte_norm (nth 0 enc (base + 15 * blk + 14)) in
  if ofs = 0 then a0 + 256 * (a1 %% 128)
  else if ofs = 1 then
    ((a1 %/ 128) %% 2) + 2 * a2 + 512 * (a3 %% 64)
  else if ofs = 2 then
    ((a3 %/ 64) %% 4) + 4 * a4 + 1024 * (a5 %% 32)
  else if ofs = 3 then
    ((a5 %/ 32) %% 8) + 8 * a6 + 2048 * (a7 %% 16)
  else if ofs = 4 then
    ((a7 %/ 16) %% 16) + 16 * a8 + 4096 * (a9 %% 8)
  else if ofs = 5 then
    ((a9 %/ 8) %% 32) + 32 * a10 + 8192 * (a11 %% 4)
  else if ofs = 6 then
    ((a11 %/ 4) %% 64) + 64 * a12 + 16384 * (a13 %% 2)
  else ((a13 %/ 2) %% 128) + 128 * a14.

op haetae_unpack_poly_q_mode5_coeff_at
   (enc : encoded_pkey) (base i : int) : coeff =
  haetae_byte_norm (nth 0 enc (base + 2 * i)) +
  256 * haetae_byte_norm (nth 0 enc (base + 2 * i + 1)).

op haetae_unpack_poly_q_ref_at
   (md : mode) (enc : encoded_pkey) (offset : int) : poly =
  with md = Mode2 =>
    mkseq
      (fun i =>
        haetae_unpack_poly_q_mode23_coeff_at
          enc offset (i %/ 8) (i %% 8))
      n
  with md = Mode3 =>
    mkseq
      (fun i =>
        haetae_unpack_poly_q_mode23_coeff_at
          enc offset (i %/ 8) (i %% 8))
      n
  with md = Mode5 =>
    mkseq
      (fun i => haetae_unpack_poly_q_mode5_coeff_at enc offset i)
      n.

op haetae_pack_polyveck_body_ref (md : mode) (b : polyveck) : byte list =
  mkseq
    (fun i =>
      nth 0
        (haetae_pack_poly_q_ref md
          (nth poly_zero b (i %/ mode_polyq_packedbytes md)))
        (i %% mode_polyq_packedbytes md))
    (haetae_public_key_body_bytes md).

op haetae_unpack_polyveck_body_ref
   (md : mode) (enc : encoded_pkey) (offset : int) : polyveck =
  mkseq
    (fun row =>
      haetae_unpack_poly_q_ref_at md enc
        (offset + row * mode_polyq_packedbytes md))
    (mode_k md).

op haetae_pack_vk_ref (md : mode) (b : polyveck) (sd : seed) : encoded_pkey =
  haetae_pack_seed sd ++ haetae_pack_polyveck_body_ref md b.

op haetae_unpack_vk_public_key_ref
   (md : mode) (enc : encoded_pkey) : pkey =
  (haetae_unpack_seed enc,
   haetae_unpack_polyveck_body_ref md enc seedbytes).
op haetae_pack_polyveck_body (md : mode) (b : polyveck) : byte list =
  mkseq
    (fun i =>
      if i %% mode_polyq_packedbytes md < n then
        poly_coeff
          (nth poly_zero b (i %/ mode_polyq_packedbytes md))
          (i %% mode_polyq_packedbytes md)
      else 0)
    (haetae_public_key_body_bytes md).
op haetae_unpack_polyveck_body
   (md : mode) (enc : encoded_pkey) (offset : int) : polyveck =
  mkseq
    (fun row =>
      haetae_unpack_poly_q_at md enc
        (offset + row * mode_polyq_packedbytes md))
    (mode_k md).
op haetae_pack_vk (md : mode) (b : polyveck) (sd : seed) : encoded_pkey =
  haetae_pack_seed sd ++ haetae_pack_polyveck_body md b.
op haetae_unpack_vk_public_key
   (md : mode) (enc : encoded_pkey) : pkey =
  (haetae_unpack_seed enc,
   haetae_unpack_polyveck_body md enc seedbytes).
op haetae_unpack_vk_matrix (md : mode) (enc : encoded_pkey) : matrix =
  packed_haetae_verification_matrix md
    (haetae_unpack_vk_public_key md enc).
op haetae_pack_public_key_bytes (md : mode) (pk : pkey) : encoded_pkey =
  haetae_pack_vk md pk.`2 pk.`1.
op haetae_unpack_public_key_bytes
   (md : mode) (enc : encoded_pkey) : pkey =
  haetae_unpack_vk_public_key md enc.
op concrete_haetae_keygen_packed_public_key
   (md : mode) (sd : seed) : encoded_pkey =
  haetae_pack_public_key_bytes md (packed_haetae_public_key md sd).
op concrete_haetae_keygen_unpacked_public_key
   (md : mode) (sd : seed) : pkey =
  haetae_unpack_public_key_bytes md
    (concrete_haetae_keygen_packed_public_key md sd).
op concrete_haetae_keygen_verification_matrix (md : mode) (sd : seed) :
  matrix =
  packed_haetae_verification_matrix md
    (concrete_haetae_keygen_unpacked_public_key md sd).
op haetae_pack_public_key_bytes_ref (md : mode) (pk : pkey) :
  encoded_pkey =
  haetae_pack_vk_ref md pk.`2 pk.`1.
op haetae_unpack_public_key_bytes_ref
   (md : mode) (enc : encoded_pkey) : pkey =
  haetae_unpack_vk_public_key_ref md enc.
op concrete_haetae_keygen_packed_public_key_ref
   (md : mode) (sd : seed) : encoded_pkey =
  haetae_pack_public_key_bytes_ref md (packed_haetae_public_key md sd).
op concrete_haetae_keygen_unpacked_public_key_ref
   (md : mode) (sd : seed) : pkey =
  haetae_unpack_public_key_bytes_ref md
    (concrete_haetae_keygen_packed_public_key_ref md sd).
op concrete_haetae_keygen_verification_matrix_ref
   (md : mode) (sd : seed) : matrix =
  packed_haetae_verification_matrix md
    (concrete_haetae_keygen_unpacked_public_key_ref md sd).
op concrete_haetae_reference_keygen_packed_public_key_ref
   (md : mode) (sd : seed) : encoded_pkey =
  haetae_pack_public_key_bytes_ref md
    (packed_haetae_reference_public_key md sd).
op concrete_haetae_reference_keygen_unpacked_public_key_ref
   (md : mode) (sd : seed) : pkey =
  haetae_unpack_public_key_bytes_ref md
    (concrete_haetae_reference_keygen_packed_public_key_ref md sd).
op concrete_haetae_reference_keygen_verification_matrix_ref
   (md : mode) (sd : seed) : matrix =
  packed_haetae_verification_matrix md
    (concrete_haetae_reference_keygen_unpacked_public_key_ref md sd).
op haetae_public_key_roundtrip_ok (md : mode) (pk : pkey) : bool =
  haetae_unpack_public_key_bytes md
    (haetae_pack_public_key_bytes md pk) = pk.
op haetae_keygen_public_key_roundtrip_ok (md : mode) (sd : seed) : bool =
  haetae_public_key_roundtrip_ok md (packed_haetae_public_key md sd).

lemma public_key_seed_poly_wf tag src :
  poly_wf (public_key_seed_poly tag src).
proof. by rewrite /poly_wf /public_key_seed_poly size_mkseq /n. qed.

lemma public_key_seed_polyvecl_wf md tag src :
  polyvecl_wf md (public_key_seed_polyvecl md tag src).
proof.
rewrite /polyvecl_wf /public_key_seed_polyvecl size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply public_key_seed_poly_wf.
qed.

lemma public_key_seed_polyveck_wf md tag src :
  polyveck_wf md (public_key_seed_polyveck md tag src).
proof.
rewrite /polyveck_wf /public_key_seed_polyveck size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply public_key_seed_poly_wf.
qed.

lemma haetae_keygen_seedbuf_bytes_gt0 :
  0 < haetae_keygen_seedbuf_bytes.
proof. by rewrite /haetae_keygen_seedbuf_bytes /seedbytes /crhbytes. qed.

lemma haetae_reference_keygen_seedbuf_bytesE :
  haetae_reference_keygen_seedbuf_bytes = haetae_keygen_seedbuf_bytes.
proof.
by rewrite /haetae_reference_keygen_seedbuf_bytes
           /haetae_keygen_seedbuf_bytes.
qed.

lemma haetae_reference_keygen_xof_absorb_bytesE :
  haetae_reference_keygen_xof_absorb_bytes = seedbytes.
proof. by rewrite /haetae_reference_keygen_xof_absorb_bytes. qed.

lemma haetae_reference_keygen_xof_squeeze_bytesE :
  haetae_reference_keygen_xof_squeeze_bytes =
  haetae_reference_keygen_seedbuf_bytes.
proof. by rewrite /haetae_reference_keygen_xof_squeeze_bytes. qed.

lemma haetae_keygen_rhoprime_offsetE :
  haetae_keygen_rhoprime_offset = 0.
proof. by rewrite /haetae_keygen_rhoprime_offset. qed.

lemma haetae_keygen_sigma_offsetE :
  haetae_keygen_sigma_offset = seedbytes.
proof. by rewrite /haetae_keygen_sigma_offset. qed.

lemma haetae_keygen_key_offsetE :
  haetae_keygen_key_offset = seedbytes + crhbytes.
proof. by rewrite /haetae_keygen_key_offset. qed.

lemma haetae_shake256_rate_bytesE :
  haetae_shake256_rate_bytes = 136.
proof.
by rewrite /haetae_shake256_rate_bytes shake256_rate_bytesE.
qed.

lemma haetae_shake256_domain_separatorE :
  haetae_shake256_domain_separator = 31.
proof.
by rewrite /haetae_shake256_domain_separator shake256_domain_separatorE.
qed.

lemma haetae_shake256_bytes_size input outlen :
  0 <= outlen =>
  size (haetae_shake256_bytes input outlen) = outlen.
proof.
move=> ge0_outlen.
by rewrite /haetae_shake256_bytes shake256_size.
qed.

lemma haetae_xof256_squeeze_size st outlen :
  0 <= outlen =>
  size (haetae_xof256_squeeze st outlen) = outlen.
proof.
move=> ge0_outlen.
by rewrite /haetae_xof256_squeeze
           shake256_squeeze_size.
qed.

lemma haetae_xof256_absorb_once_squeeze_size input inlen outlen :
  0 <= outlen =>
  size (haetae_xof256_absorb_once_squeeze input inlen outlen) = outlen.
proof.
move=> ge0_outlen.
by rewrite /haetae_xof256_absorb_once_squeeze
           haetae_xof256_squeeze_size.
qed.

lemma haetae_reference_keygen_seedbuf_after_memcpy_size sd :
  size (haetae_reference_keygen_seedbuf_after_memcpy sd) =
  haetae_reference_keygen_seedbuf_bytes.
proof.
by rewrite /haetae_reference_keygen_seedbuf_after_memcpy size_mkseq.
qed.

lemma haetae_keygen_xof_seedbuf_size sd :
  size (haetae_keygen_xof_seedbuf sd) = haetae_keygen_seedbuf_bytes.
proof.
by rewrite /haetae_keygen_xof_seedbuf
           /haetae_xof256_absorb_once_squeeze
           /haetae_xof256_squeeze /shake256_squeeze
           /haetae_reference_keygen_xof_squeeze_bytes
           /haetae_reference_keygen_seedbuf_bytes
           /haetae_keygen_seedbuf_bytes size_mkseq.
qed.

lemma haetae_reference_keygen_xof256_seedbuf_size sd :
  size (haetae_reference_keygen_xof256_seedbuf sd) =
  haetae_reference_keygen_seedbuf_bytes.
proof.
by rewrite /haetae_reference_keygen_xof256_seedbuf
           haetae_keygen_xof_seedbuf_size
           haetae_reference_keygen_seedbuf_bytesE.
qed.

lemma haetae_seed_slice_size src offset len :
  0 <= len =>
  size (haetae_seed_slice src offset len) = len.
proof.
move=> ge0_len.
rewrite /haetae_seed_slice size_mkseq.
by smt().
qed.

lemma haetae_reference_keygen_xof_input_size sd :
  size (haetae_reference_keygen_xof_input sd) =
  haetae_reference_keygen_xof_absorb_bytes.
proof.
rewrite /haetae_reference_keygen_xof_input.
apply haetae_seed_slice_size.
by rewrite /haetae_reference_keygen_xof_absorb_bytes /seedbytes.
qed.

lemma haetae_xof256_absorb_input_size input inlen :
  0 <= inlen =>
  size (haetae_xof256_absorb_input input inlen) = inlen.
proof.
move=> ge0_inlen.
rewrite /haetae_xof256_absorb_input.
by apply haetae_seed_slice_size.
qed.

lemma haetae_reference_keygen_xof_absorb_inputE sd :
  haetae_xof256_absorb_input
    (haetae_reference_keygen_seedbuf_after_memcpy sd)
    haetae_reference_keygen_xof_absorb_bytes =
  haetae_reference_keygen_xof_input sd.
proof.
by rewrite /haetae_xof256_absorb_input
           /haetae_reference_keygen_xof_input.
qed.

lemma haetae_reference_keygen_shake256_domain sd :
  shake256_absorb_once_short_domain
    (haetae_reference_keygen_xof_input sd)
    haetae_reference_keygen_xof_absorb_bytes.
proof.
by rewrite /shake256_absorb_once_short_domain
           /haetae_reference_keygen_xof_absorb_bytes
           shake256_rate_bytesE /seedbytes.
qed.

lemma haetae_reference_keygen_xof_squeeze_bytes_lt_rate :
  haetae_reference_keygen_xof_squeeze_bytes < haetae_shake256_rate_bytes.
proof.
by rewrite /haetae_reference_keygen_xof_squeeze_bytes
           /haetae_reference_keygen_seedbuf_bytes
           /haetae_shake256_rate_bytes
           shake256_rate_bytesE /seedbytes /crhbytes.
qed.

lemma haetae_reference_keygen_xof_absorb_once_stateE sd :
  haetae_xof256_absorb_once
    (haetae_reference_keygen_seedbuf_after_memcpy sd)
    haetae_reference_keygen_xof_absorb_bytes =
  shake256_absorb_once
    (haetae_reference_keygen_xof_input sd)
    haetae_reference_keygen_xof_absorb_bytes.
proof.
by rewrite /haetae_xof256_absorb_once
           haetae_reference_keygen_xof_absorb_inputE.
qed.

lemma haetae_keygen_xof_seedbuf_incrementalE sd :
  haetae_keygen_xof_seedbuf sd =
  haetae_xof256_squeeze
    (haetae_xof256_absorb_once
      (haetae_reference_keygen_seedbuf_after_memcpy sd)
      haetae_reference_keygen_xof_absorb_bytes)
    haetae_reference_keygen_xof_squeeze_bytes.
proof. by rewrite /haetae_keygen_xof_seedbuf
                  /haetae_xof256_absorb_once_squeeze. qed.

lemma haetae_keygen_xof_seedbuf_shake256E sd :
  haetae_keygen_xof_seedbuf sd =
  haetae_shake256_bytes
    (haetae_reference_keygen_xof_input sd)
    haetae_reference_keygen_xof_squeeze_bytes.
proof.
by rewrite haetae_keygen_xof_seedbuf_incrementalE
           haetae_reference_keygen_xof_absorb_once_stateE
           /haetae_shake256_bytes
           /shake256 haetae_reference_keygen_xof_input_size.
qed.

lemma haetae_keygen_seedbuf_rhoprime_size seedbuf :
  size (haetae_keygen_seedbuf_rhoprime seedbuf) = seedbytes.
proof.
rewrite /haetae_keygen_seedbuf_rhoprime.
apply haetae_seed_slice_size.
by rewrite /seedbytes.
qed.

lemma haetae_keygen_seedbuf_sigma_size seedbuf :
  size (haetae_keygen_seedbuf_sigma seedbuf) = crhbytes.
proof.
rewrite /haetae_keygen_seedbuf_sigma.
apply haetae_seed_slice_size.
by rewrite /crhbytes.
qed.

lemma haetae_keygen_seedbuf_key_size seedbuf :
  size (haetae_keygen_seedbuf_key seedbuf) = seedbytes.
proof.
rewrite /haetae_keygen_seedbuf_key.
apply haetae_seed_slice_size.
by rewrite /seedbytes.
qed.

lemma haetae_reference_keygen_xof_seedbuf_layout_wf sd :
  haetae_keygen_seedbuf_layout_wf
    (haetae_reference_keygen_xof256_seedbuf sd).
proof.
by rewrite /haetae_keygen_seedbuf_layout_wf
           haetae_reference_keygen_xof256_seedbuf_size
           haetae_keygen_rhoprime_offsetE
           haetae_keygen_sigma_offsetE
           haetae_keygen_key_offsetE
           haetae_keygen_seedbuf_rhoprime_size
           haetae_keygen_seedbuf_sigma_size
           haetae_keygen_seedbuf_key_size.
qed.

lemma haetae_reference_keygen_xof_call_wf_ok sd :
  size sd = seedbytes =>
  haetae_reference_keygen_xof_call_wf sd
    (haetae_reference_keygen_xof256_seedbuf sd).
proof.
move=> sd_sz.
by rewrite /haetae_reference_keygen_xof_call_wf
           sd_sz
           haetae_reference_keygen_seedbuf_after_memcpy_size
           haetae_reference_keygen_xof_absorb_inputE
           haetae_reference_keygen_shake256_domain
           haetae_reference_keygen_xof_squeeze_bytes_lt_rate
           haetae_reference_keygen_xof_absorb_once_stateE
           haetae_reference_keygen_xof256_seedbuf_size
           /haetae_reference_keygen_xof256_seedbuf
           haetae_keygen_xof_seedbuf_incrementalE
           /haetae_xof256_squeeze
           haetae_reference_keygen_xof_absorb_bytesE
           haetae_reference_keygen_xof_squeeze_bytesE.
qed.

lemma haetae_keygen_rhoprime_ref_sliceE sd :
  haetae_keygen_rhoprime sd =
  haetae_keygen_seedbuf_rhoprime
    (haetae_reference_keygen_xof256_seedbuf sd).
proof. by rewrite /haetae_keygen_rhoprime. qed.

lemma haetae_keygen_sigma_ref_sliceE sd :
  haetae_keygen_sigma sd =
  haetae_keygen_seedbuf_sigma
    (haetae_reference_keygen_xof256_seedbuf sd).
proof. by rewrite /haetae_keygen_sigma. qed.

lemma haetae_keygen_key_ref_sliceE sd :
  haetae_keygen_key sd =
  haetae_keygen_seedbuf_key
    (haetae_reference_keygen_xof256_seedbuf sd).
proof. by rewrite /haetae_keygen_key. qed.

lemma haetae_keygen_rhoprime_size sd :
  size (haetae_keygen_rhoprime sd) = seedbytes.
proof.
by rewrite /haetae_keygen_rhoprime haetae_keygen_seedbuf_rhoprime_size.
qed.

lemma haetae_keygen_sigma_size sd :
  size (haetae_keygen_sigma sd) = crhbytes.
proof.
by rewrite /haetae_keygen_sigma haetae_keygen_seedbuf_sigma_size.
qed.

lemma haetae_keygen_key_size sd :
  size (haetae_keygen_key sd) = seedbytes.
proof.
by rewrite /haetae_keygen_key haetae_keygen_seedbuf_key_size.
qed.

lemma haetae_keygen_sampler_seed_size sigma counter :
  size (haetae_keygen_sampler_seed sigma counter) = seedbytes.
proof. by rewrite /haetae_keygen_sampler_seed size_mkseq. qed.

lemma haetae_keygen_counter_next_gt counter md :
  counter < haetae_keygen_counter_next md counter.
proof. by rewrite /haetae_keygen_counter_next; smt(mode_m_gt0 mode_k_gt0). qed.

lemma public_matrix_seed_size md sd :
  size (public_matrix_seed md sd) = mode_k md.
proof. by rewrite /public_matrix_seed size_mkseq; case md. qed.

lemma public_matrix_seed_rows_wf md sd :
  all (polyvecl_wf md) (public_matrix_seed md sd).
proof.
rewrite /public_matrix_seed.
apply/allP=> row /mkseqP [i [i_rng ->]].
by apply public_key_seed_polyvecl_wf.
qed.

lemma public_secret_vector_seed_wf md sd :
  polyvecl_wf md (public_secret_vector_seed md sd).
proof. by rewrite /public_secret_vector_seed; apply public_key_seed_polyvecl_wf. qed.

lemma public_error_vector_seed_wf md sd :
  polyveck_wf md (public_error_vector_seed md sd).
proof. by rewrite /public_error_vector_seed; apply public_key_seed_polyveck_wf. qed.

lemma public_rounding_vector_seed_wf md sd :
  polyveck_wf md (public_rounding_vector_seed md sd).
proof. by rewrite /public_rounding_vector_seed; apply public_key_seed_polyveck_wf. qed.

lemma haetae_reference_polymatkm_expand_matA_size md rhoprime :
  size (haetae_reference_polymatkm_expand_matA md rhoprime) = mode_k md.
proof.
by rewrite /haetae_reference_polymatkm_expand_matA public_matrix_seed_size.
qed.

lemma haetae_reference_polymatkm_expand_matA_rows_wf md rhoprime :
  all (polyvecl_wf md)
    (haetae_reference_polymatkm_expand_matA md rhoprime).
proof.
by rewrite /haetae_reference_polymatkm_expand_matA;
   apply public_matrix_seed_rows_wf.
qed.

lemma haetae_reference_polyveck_expand_vecA_wf md rhoprime :
  polyveck_wf md (haetae_reference_polyveck_expand_vecA md rhoprime).
proof.
by rewrite /haetae_reference_polyveck_expand_vecA;
   apply public_rounding_vector_seed_wf.
qed.

lemma haetae_reference_polyvecmk_expand_S_s1_wf md sigma counter :
  polyvecl_wf md
    (haetae_reference_polyvecmk_expand_S_s1 md sigma counter).
proof.
by rewrite /haetae_reference_polyvecmk_expand_S_s1;
   apply public_secret_vector_seed_wf.
qed.

lemma haetae_reference_polyvecmk_expand_S_s2_wf md sigma counter :
  polyveck_wf md
    (haetae_reference_polyvecmk_expand_S_s2 md sigma counter).
proof.
by rewrite /haetae_reference_polyvecmk_expand_S_s2;
   apply public_error_vector_seed_wf.
qed.

lemma haetae_reference_keygen_secret_vector_wf md sd :
  polyvecl_wf md (haetae_reference_keygen_secret_vector md sd).
proof.
by rewrite /haetae_reference_keygen_secret_vector;
   apply haetae_reference_polyvecmk_expand_S_s1_wf.
qed.

lemma haetae_reference_keygen_error_vector_wf md sd :
  polyveck_wf md (haetae_reference_keygen_error_vector md sd).
proof.
by rewrite /haetae_reference_keygen_error_vector;
   apply haetae_reference_polyvecmk_expand_S_s2_wf.
qed.

lemma haetae_reference_keygen_raw_public_vector_wf md sd :
  polyveck_wf md (haetae_reference_keygen_raw_public_vector md sd).
proof.
by rewrite /haetae_reference_keygen_raw_public_vector;
   apply polyveck_add_wf.
qed.

lemma haetae_reference_keygen_raw_public_vector_coeffs_q_bound md sd :
  polyveck_coeffs_q_bound md
    (haetae_reference_keygen_raw_public_vector md sd).
proof.
by rewrite /haetae_reference_keygen_raw_public_vector;
   apply polyveck_add_coeffs_q_bound.
qed.

lemma haetae_reference_keygen_mode23_predecompose_vector_wf md sd :
  polyveck_wf md
    (haetae_reference_keygen_mode23_predecompose_vector md sd).
proof.
by rewrite /haetae_reference_keygen_mode23_predecompose_vector;
   apply polyveck_add_wf.
qed.

lemma haetae_reference_keygen_mode23_predecompose_vector_coeffs_q_bound
   md sd :
  polyveck_coeffs_q_bound md
    (haetae_reference_keygen_mode23_predecompose_vector md sd).
proof.
by rewrite /haetae_reference_keygen_mode23_predecompose_vector;
   apply polyveck_add_coeffs_q_bound.
qed.

lemma haetae_reference_keygen_mode23_public_vector_polyq_wf md sd :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyveck_polyq_coeffs_wf md
    (haetae_reference_keygen_mode23_public_vector md sd).
proof.
move=> md23.
rewrite /haetae_reference_keygen_mode23_public_vector.
apply polyveck_vk_highbits_mode23_polyq_wf; first by apply md23.
by apply haetae_reference_keygen_mode23_predecompose_vector_coeffs_q_bound.
qed.

lemma haetae_reference_keygen_mode23_adjusted_error_vector_wf md sd :
  polyveck_wf md
    (haetae_reference_keygen_mode23_adjusted_error_vector md sd).
proof.
by rewrite /haetae_reference_keygen_mode23_adjusted_error_vector;
   apply polyveck_sub_wf.
qed.

lemma haetae_reference_keygen_mode5_public_vector_wf sd :
  polyveck_wf Mode5
    (haetae_reference_keygen_mode5_public_vector Mode5 sd).
proof.
by rewrite /haetae_reference_keygen_mode5_public_vector;
   apply polyveck_neg_wf.
qed.

lemma haetae_reference_keygen_mode5_public_vector_coeffs_q_bound sd :
  polyveck_coeffs_q_bound Mode5
    (haetae_reference_keygen_mode5_public_vector Mode5 sd).
proof.
by rewrite /haetae_reference_keygen_mode5_public_vector;
   apply polyveck_neg_coeffs_q_bound.
qed.

lemma haetae_reference_keygen_mode5_public_vector_polyq_wf sd :
  haetae_polyveck_polyq_coeffs_wf Mode5
    (haetae_reference_keygen_mode5_public_vector Mode5 sd).
proof.
apply polyveck_q_bound_mode5_polyq_wf.
+ by apply haetae_reference_keygen_mode5_public_vector_wf.
by apply haetae_reference_keygen_mode5_public_vector_coeffs_q_bound.
qed.

lemma haetae_keygen_raw_public_vector_wf md sd :
  polyveck_wf md (haetae_keygen_raw_public_vector md sd).
proof. by rewrite /haetae_keygen_raw_public_vector; apply polyveck_add_wf. qed.

lemma haetae_keygen_raw_public_vector_coeffs_q_bound md sd :
  polyveck_coeffs_q_bound md (haetae_keygen_raw_public_vector md sd).
proof.
by rewrite /haetae_keygen_raw_public_vector;
   apply polyveck_add_coeffs_q_bound.
qed.

lemma haetae_keygen_mode23_predecompose_vector_wf md sd :
  polyveck_wf md (haetae_keygen_mode23_predecompose_vector md sd).
proof.
by rewrite /haetae_keygen_mode23_predecompose_vector;
   apply polyveck_add_wf.
qed.

lemma haetae_keygen_mode23_predecompose_vector_coeffs_q_bound md sd :
  polyveck_coeffs_q_bound md
    (haetae_keygen_mode23_predecompose_vector md sd).
proof.
by rewrite /haetae_keygen_mode23_predecompose_vector;
   apply polyveck_add_coeffs_q_bound.
qed.

lemma haetae_keygen_mode23_public_vector_polyq_wf md sd :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyveck_polyq_coeffs_wf md
    (haetae_keygen_mode23_public_vector md sd).
proof.
move=> md23.
rewrite /haetae_keygen_mode23_public_vector.
apply polyveck_vk_highbits_mode23_polyq_wf; first by apply md23.
by apply haetae_keygen_mode23_predecompose_vector_coeffs_q_bound.
qed.

lemma haetae_keygen_mode23_rounding_lowbits_wf md sd :
  polyveck_wf md (haetae_keygen_mode23_rounding_lowbits md sd).
proof.
by rewrite /haetae_keygen_mode23_rounding_lowbits;
   apply polyveck_vk_lowbits_wf.
qed.

lemma haetae_keygen_mode23_adjusted_error_vector_wf md sd :
  polyveck_wf md (haetae_keygen_mode23_adjusted_error_vector md sd).
proof.
by rewrite /haetae_keygen_mode23_adjusted_error_vector;
   apply polyveck_sub_wf.
qed.

lemma haetae_keygen_mode5_public_vector_wf sd :
  polyveck_wf Mode5 (haetae_keygen_mode5_public_vector Mode5 sd).
proof.
by rewrite /haetae_keygen_mode5_public_vector;
   apply polyveck_neg_wf.
qed.

lemma haetae_keygen_mode5_public_vector_coeffs_q_bound sd :
  polyveck_coeffs_q_bound Mode5
    (haetae_keygen_mode5_public_vector Mode5 sd).
proof.
by rewrite /haetae_keygen_mode5_public_vector;
   apply polyveck_neg_coeffs_q_bound.
qed.

lemma haetae_keygen_mode5_public_vector_polyq_wf sd :
  haetae_polyveck_polyq_coeffs_wf Mode5
    (haetae_keygen_mode5_public_vector Mode5 sd).
proof.
apply polyveck_q_bound_mode5_polyq_wf.
+ by apply haetae_keygen_mode5_public_vector_wf.
by apply haetae_keygen_mode5_public_vector_coeffs_q_bound.
qed.

lemma haetae_public_key_vector_from_relation_polyq_wf md sd s e :
  haetae_polyveck_polyq_coeffs_wf md
    (haetae_public_key_vector_from_relation md sd s e).
proof.
rewrite /haetae_public_key_vector_from_relation.
case: md => /=.
+ apply polyveck_vk_highbits_mode23_polyq_wf.
  + by left.
  by apply polyveck_add_coeffs_q_bound.
+ apply polyveck_vk_highbits_mode23_polyq_wf.
  + by right.
  by apply polyveck_add_coeffs_q_bound.
apply polyveck_q_bound_mode5_polyq_wf.
+ by apply polyveck_neg_wf.
by apply polyveck_neg_coeffs_q_bound.
qed.

lemma haetae_reference_keygen_public_vector_polyq_wf md sd :
  haetae_polyveck_polyq_coeffs_wf md
    (haetae_reference_keygen_public_vector md sd).
proof.
by rewrite /haetae_reference_keygen_public_vector;
   apply haetae_public_key_vector_from_relation_polyq_wf.
qed.

lemma haetae_keygen_public_vector_polyq_wf md sd :
  haetae_polyveck_polyq_coeffs_wf md (haetae_keygen_public_vector md sd).
proof.
by rewrite /haetae_keygen_public_vector;
   apply haetae_public_key_vector_from_relation_polyq_wf.
qed.

lemma public_key_vector_seed_wf md sd :
  polyveck_wf md (public_key_vector_seed md sd).
proof.
have h := haetae_keygen_public_vector_polyq_wf md sd.
by move: h; rewrite /haetae_polyveck_polyq_coeffs_wf /public_key_vector_seed.
qed.

lemma public_key_mode23_column_wf md pk :
  polyveck_wf md (public_key_mode23_column md pk).
proof. by rewrite /public_key_mode23_column
                  /haetae_mode23_verification_column; apply polyveck_double_wf. qed.

lemma haetae_verification_column_from_unpacked_wf md sd b :
  polyveck_wf md (haetae_verification_column_from_unpacked md sd b).
proof.
case md; rewrite /haetae_verification_column_from_unpacked /=.
+ by rewrite /haetae_mode23_verification_column; apply polyveck_double_wf.
+ by rewrite /haetae_mode23_verification_column; apply polyveck_double_wf.
rewrite /haetae_mode5_verification_column.
rewrite /polyveck_wf size_mkseq.
split.
+ by trivial.
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_normalize_wf.
qed.

lemma public_key_verification_column_wf md pk :
  polyveck_wf md (public_key_verification_column md pk).
proof.
case md; rewrite /public_key_verification_column /=.
+ by apply public_key_mode23_column_wf.
+ by apply public_key_mode23_column_wf.
rewrite /public_key_mode5_column.
rewrite /polyveck_wf size_mkseq.
split.
+ by trivial.
apply/allP=> p /mkseqP [i [_ ->]].
by apply poly_normalize_wf.
qed.

lemma public_verification_matrix_size md pk :
  size (public_verification_matrix md pk) = mode_k md.
proof.
by rewrite /public_verification_matrix /packed_haetae_verification_matrix
           /haetae_verification_matrix_from_unpacked size_mkseq; case md.
qed.

lemma public_verification_matrix_rows_wf md pk :
  all (polyvecl_wf md) (public_verification_matrix md pk).
proof.
rewrite /public_verification_matrix /packed_haetae_verification_matrix
        /haetae_verification_matrix_from_unpacked.
apply/allP=> row /mkseqP [i [i_rng ->]].
rewrite /polyvecl_wf size_mkseq.
split.
+ by smt(mode_l_gt0).
apply/allP=> p /mkseqP [j [_ ->]].
case: (j = 0) => j0; rewrite j0 /=.
+ have col_wf :=
    haetae_verification_column_from_unpacked_wf md pk.`1 pk.`2.
  smt(polyveck_wf_nth).
by apply poly_double_wf.
qed.

lemma challenge_embedding_wf md ch :
  challenge_wf ch => polyvecl_wf md (challenge_embedding md ch).
proof.
move=> ch_wf.
rewrite /polyvecl_wf /challenge_embedding size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
case: (i = 0) => i0; rewrite i0 /=.
+ by rewrite /challenge_wf in ch_wf; smt.
by apply poly_zero_wf.
qed.

lemma public_key_of_secret_wf md sk :
  polyveck_wf md (public_key_of_secret md sk).`2.
proof. by rewrite /public_key_of_secret /=; apply public_key_vector_seed_wf. qed.

lemma haetae_pack_seed_size sd :
  size (haetae_pack_seed sd) = seedbytes.
proof. by rewrite /haetae_pack_seed size_mkseq /seedbytes. qed.

lemma haetae_unpack_seed_size enc :
  size (haetae_unpack_seed enc) = seedbytes.
proof. by rewrite /haetae_unpack_seed size_mkseq /seedbytes. qed.

lemma haetae_unpack_seed_pack sd :
  size sd = seedbytes =>
  haetae_unpack_seed (haetae_pack_seed sd) = sd.
proof.
move=> sd_sz.
rewrite /haetae_unpack_seed /haetae_pack_seed.
apply/(eq_from_nth 0).
+ by rewrite size_mkseq /seedbytes sd_sz.
move=> i i_rng.
rewrite size_mkseq /seedbytes in i_rng.
rewrite nth_mkseq; first by smt().
by smt().
qed.

lemma haetae_unpack_seed_pack_cat sd tail :
  size sd = seedbytes =>
  haetae_unpack_seed (haetae_pack_seed sd ++ tail) = sd.
proof.
move=> sd_sz.
rewrite /haetae_unpack_seed /haetae_pack_seed.
apply/(eq_from_nth 0).
+ by rewrite size_mkseq /seedbytes sd_sz.
move=> i i_rng.
rewrite size_mkseq /seedbytes in i_rng.
by smt(nth_cat nth_mkseq size_mkseq).
qed.

lemma haetae_polyq_coeff_bound_gt0 md :
  0 < haetae_polyq_coeff_bound md.
proof.
by case md; rewrite /haetae_polyq_coeff_bound
                   /haetae_polyq_mode23_bound /haetae_polyq_mode5_bound.
qed.

lemma haetae_byte_norm_bounds x :
  0 <= haetae_byte_norm x < haetae_byte_modulus.
proof. by rewrite /haetae_byte_norm /haetae_byte_modulus; smt(). qed.

lemma haetae_byte_norm_small x :
  0 <= x < haetae_byte_modulus => haetae_byte_norm x = x.
proof. by rewrite /haetae_byte_norm /haetae_byte_modulus; smt(). qed.

lemma haetae_byte_norm_idempotent x :
  haetae_byte_norm (haetae_byte_norm x) = haetae_byte_norm x.
proof. by rewrite /haetae_byte_norm /haetae_byte_modulus; smt(). qed.

lemma haetae_unpack15_coeff0 c0 c1 :
  0 <= c0 < 32768 =>
  0 <= c1 < 32768 =>
  haetae_byte_norm c0 +
    256 * (haetae_byte_norm ((c0 %/ 256) %% 128 + (c1 %% 2) * 128) %% 128) =
  c0.
proof. by rewrite /haetae_byte_norm /haetae_byte_modulus; smt(). qed.

lemma haetae_unpack15_coeff1 c0 c1 c2 :
  0 <= c0 < 32768 =>
  0 <= c1 < 32768 =>
  0 <= c2 < 32768 =>
  ((haetae_byte_norm ((c0 %/ 256) %% 128 + (c1 %% 2) * 128) %/ 128) %% 2) +
    2 * haetae_byte_norm (c1 %/ 2) +
    512 * (haetae_byte_norm ((c1 %/ 512) %% 64 + (c2 %% 4) * 64) %% 64) =
  c1.
proof. by rewrite /haetae_byte_norm /haetae_byte_modulus; smt(). qed.

lemma haetae_unpack15_coeff2 c1 c2 c3 :
  0 <= c1 < 32768 =>
  0 <= c2 < 32768 =>
  0 <= c3 < 32768 =>
  ((haetae_byte_norm ((c1 %/ 512) %% 64 + (c2 %% 4) * 64) %/ 64) %% 4) +
    4 * haetae_byte_norm (c2 %/ 4) +
    1024 * (haetae_byte_norm ((c2 %/ 1024) %% 32 + (c3 %% 8) * 32) %% 32) =
  c2.
proof. by rewrite /haetae_byte_norm /haetae_byte_modulus; smt(). qed.

lemma haetae_unpack15_coeff3 c2 c3 c4 :
  0 <= c2 < 32768 =>
  0 <= c3 < 32768 =>
  0 <= c4 < 32768 =>
  ((haetae_byte_norm ((c2 %/ 1024) %% 32 + (c3 %% 8) * 32) %/ 32) %% 8) +
    8 * haetae_byte_norm (c3 %/ 8) +
    2048 * (haetae_byte_norm ((c3 %/ 2048) %% 16 + (c4 %% 16) * 16) %% 16) =
  c3.
proof. by rewrite /haetae_byte_norm /haetae_byte_modulus; smt(). qed.

lemma haetae_unpack15_coeff4 c3 c4 c5 :
  0 <= c3 < 32768 =>
  0 <= c4 < 32768 =>
  0 <= c5 < 32768 =>
  ((haetae_byte_norm ((c3 %/ 2048) %% 16 + (c4 %% 16) * 16) %/ 16) %% 16) +
    16 * haetae_byte_norm (c4 %/ 16) +
    4096 * (haetae_byte_norm ((c4 %/ 4096) %% 8 + (c5 %% 32) * 8) %% 8) =
  c4.
proof. by rewrite /haetae_byte_norm /haetae_byte_modulus; smt(). qed.

lemma haetae_unpack15_coeff5 c4 c5 c6 :
  0 <= c4 < 32768 =>
  0 <= c5 < 32768 =>
  0 <= c6 < 32768 =>
  ((haetae_byte_norm ((c4 %/ 4096) %% 8 + (c5 %% 32) * 8) %/ 8) %% 32) +
    32 * haetae_byte_norm (c5 %/ 32) +
    8192 * (haetae_byte_norm ((c5 %/ 8192) %% 4 + (c6 %% 64) * 4) %% 4) =
  c5.
proof. by rewrite /haetae_byte_norm /haetae_byte_modulus; smt(). qed.

lemma haetae_unpack15_coeff6 c5 c6 c7 :
  0 <= c5 < 32768 =>
  0 <= c6 < 32768 =>
  0 <= c7 < 32768 =>
  ((haetae_byte_norm ((c5 %/ 8192) %% 4 + (c6 %% 64) * 4) %/ 4) %% 64) +
    64 * haetae_byte_norm (c6 %/ 64) +
    16384 * (haetae_byte_norm ((c6 %/ 16384) %% 2 + (c7 %% 128) * 2) %% 2) =
  c6.
proof. by rewrite /haetae_byte_norm /haetae_byte_modulus; smt(). qed.

lemma haetae_unpack15_coeff7 c6 c7 :
  0 <= c6 < 32768 =>
  0 <= c7 < 32768 =>
  ((haetae_byte_norm ((c6 %/ 16384) %% 2 + (c7 %% 128) * 2) %/ 2) %% 128) +
    128 * haetae_byte_norm (c7 %/ 128) =
  c7.
proof. by rewrite /haetae_byte_norm /haetae_byte_modulus; smt(). qed.

lemma haetae_pack_poly_q_ref_size md p :
  size (haetae_pack_poly_q_ref md p) = mode_polyq_packedbytes md.
proof.
rewrite /haetae_pack_poly_q_ref.
by case md; smt(size_mkseq).
qed.

lemma haetae_unpack_poly_q_ref_at_wf md enc offset :
  poly_wf (haetae_unpack_poly_q_ref_at md enc offset).
proof.
rewrite /haetae_unpack_poly_q_ref_at.
case md; rewrite /poly_wf; smt(size_mkseq).
qed.

lemma haetae_pack_polyveck_body_ref_size md b :
  size (haetae_pack_polyveck_body_ref md b) =
    haetae_public_key_body_bytes md.
proof.
by rewrite /haetae_pack_polyveck_body_ref /haetae_public_key_body_bytes
           size_mkseq; case md.
qed.

lemma haetae_unpack_polyveck_body_ref_wf md enc offset :
  polyveck_wf md (haetae_unpack_polyveck_body_ref md enc offset).
proof.
rewrite /polyveck_wf /haetae_unpack_polyveck_body_ref size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply haetae_unpack_poly_q_ref_at_wf.
qed.

lemma haetae_pack_vk_ref_size md b sd :
  size (haetae_pack_vk_ref md b sd) = haetae_public_key_bytes md.
proof.
rewrite /haetae_pack_vk_ref size_cat haetae_pack_seed_size
        haetae_pack_polyveck_body_ref_size.
by rewrite /haetae_public_key_bytes /haetae_public_key_body_bytes;
   case md.
qed.

lemma haetae_unpack_vk_public_key_ref_wf md enc :
  haetae_public_key_unpacked_wf md
    (haetae_unpack_vk_public_key_ref md enc).
proof.
rewrite /haetae_public_key_unpacked_wf
        /haetae_unpack_vk_public_key_ref /=.
by split; [apply haetae_unpack_seed_size | apply haetae_unpack_polyveck_body_ref_wf].
qed.

lemma nth_cat_size_plus ['a] (d : 'a) (xs ys : 'a list) j :
  0 <= j =>
  nth d (xs ++ ys) (size xs + j) = nth d ys j.
proof. by smt(nth_cat). qed.

lemma haetae_pack_polyveck_body_ref_nth md b row k :
  0 <= row < mode_k md =>
  0 <= k < mode_polyq_packedbytes md =>
  nth 0 (haetae_pack_polyveck_body_ref md b)
    (row * mode_polyq_packedbytes md + k) =
  nth 0 (haetae_pack_poly_q_ref md (nth poly_zero b row)) k.
proof.
move=> row_rng k_rng.
rewrite /haetae_pack_polyveck_body_ref.
rewrite nth_mkseq.
+ rewrite /haetae_public_key_body_bytes.
  by smt(mode_polyq_packedbytes_gt0).
by smt(nth_mkseq haetae_pack_poly_q_ref_size
       mode_polyq_packedbytes_gt0).
qed.

lemma haetae_pack_polyveck_body_ref_mode5_nth b row k :
  0 <= row < mode_k Mode5 =>
  0 <= k < mode_polyq_packedbytes Mode5 =>
  nth 0 (haetae_pack_polyveck_body_ref Mode5 b)
    (row * mode_polyq_packedbytes Mode5 + k) =
  nth 0 (haetae_pack_poly_q_ref Mode5 (nth poly_zero b row)) k.
proof.
by apply haetae_pack_polyveck_body_ref_nth.
qed.

lemma haetae_unpack_poly_q_mode23_coeff_at_cat prefix bytes blk ofs :
  0 <= blk =>
  haetae_unpack_poly_q_mode23_coeff_at
    (prefix ++ bytes) (size prefix) blk ofs =
  haetae_unpack_poly_q_mode23_coeff_at bytes 0 blk ofs.
proof.
move=> blk_ge0.
rewrite /haetae_unpack_poly_q_mode23_coeff_at.
by smt(nth_cat).
qed.

lemma haetae_polyq_mode23_coeff_rng md p j :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyq_coeffs_wf md p =>
  0 <= j < n =>
  0 <= poly_coeff p j < 32768.
proof.
move=> md23 p_wf j_rng.
move: p_wf md23; rewrite /haetae_polyq_coeffs_wf
                    /haetae_polyq_coeff_bound
                    /haetae_polyq_mode23_bound => -[p_sz p_rng].
by smt().
qed.

lemma haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs0 md p blk :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyq_coeffs_wf md p =>
  0 <= blk < 32 =>
  haetae_unpack_poly_q_mode23_coeff_at
    (haetae_pack_poly_q_ref md p) 0 blk 0 =
  poly_coeff p (8 * blk + 0).
proof.
move=> md23 p_wf blk_rng.
have c0_rng : 0 <= poly_coeff p (8 * blk + 0) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c1_rng : 0 <= poly_coeff p (8 * blk + 1) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
move: p_wf md23; case: md => /=.
+ move=> p_wf2.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff0).
+ move=> p_wf3.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff0).
by smt().
qed.

lemma haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs1 md p blk :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyq_coeffs_wf md p =>
  0 <= blk < 32 =>
  haetae_unpack_poly_q_mode23_coeff_at
    (haetae_pack_poly_q_ref md p) 0 blk 1 =
  poly_coeff p (8 * blk + 1).
proof.
move=> md23 p_wf blk_rng.
have c0_rng : 0 <= poly_coeff p (8 * blk + 0) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c1_rng : 0 <= poly_coeff p (8 * blk + 1) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c2_rng : 0 <= poly_coeff p (8 * blk + 2) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
move: p_wf md23; case: md => /=.
+ move=> p_wf2.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff1).
+ move=> p_wf3.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff1).
by smt().
qed.

lemma haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs2 md p blk :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyq_coeffs_wf md p =>
  0 <= blk < 32 =>
  haetae_unpack_poly_q_mode23_coeff_at
    (haetae_pack_poly_q_ref md p) 0 blk 2 =
  poly_coeff p (8 * blk + 2).
proof.
move=> md23 p_wf blk_rng.
have c1_rng : 0 <= poly_coeff p (8 * blk + 1) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c2_rng : 0 <= poly_coeff p (8 * blk + 2) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c3_rng : 0 <= poly_coeff p (8 * blk + 3) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
move: p_wf md23; case: md => /=.
+ move=> p_wf2.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff2).
+ move=> p_wf3.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff2).
by smt().
qed.

lemma haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs3 md p blk :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyq_coeffs_wf md p =>
  0 <= blk < 32 =>
  haetae_unpack_poly_q_mode23_coeff_at
    (haetae_pack_poly_q_ref md p) 0 blk 3 =
  poly_coeff p (8 * blk + 3).
proof.
move=> md23 p_wf blk_rng.
have c2_rng : 0 <= poly_coeff p (8 * blk + 2) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c3_rng : 0 <= poly_coeff p (8 * blk + 3) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c4_rng : 0 <= poly_coeff p (8 * blk + 4) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
move: p_wf md23; case: md => /=.
+ move=> p_wf2.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff3).
+ move=> p_wf3.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff3).
by smt().
qed.

lemma haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs4 md p blk :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyq_coeffs_wf md p =>
  0 <= blk < 32 =>
  haetae_unpack_poly_q_mode23_coeff_at
    (haetae_pack_poly_q_ref md p) 0 blk 4 =
  poly_coeff p (8 * blk + 4).
proof.
move=> md23 p_wf blk_rng.
have c3_rng : 0 <= poly_coeff p (8 * blk + 3) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c4_rng : 0 <= poly_coeff p (8 * blk + 4) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c5_rng : 0 <= poly_coeff p (8 * blk + 5) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
move: p_wf md23; case: md => /=.
+ move=> p_wf2.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff4).
+ move=> p_wf3.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff4).
by smt().
qed.

lemma haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs5 md p blk :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyq_coeffs_wf md p =>
  0 <= blk < 32 =>
  haetae_unpack_poly_q_mode23_coeff_at
    (haetae_pack_poly_q_ref md p) 0 blk 5 =
  poly_coeff p (8 * blk + 5).
proof.
move=> md23 p_wf blk_rng.
have c4_rng : 0 <= poly_coeff p (8 * blk + 4) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c5_rng : 0 <= poly_coeff p (8 * blk + 5) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c6_rng : 0 <= poly_coeff p (8 * blk + 6) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
move: p_wf md23; case: md => /=.
+ move=> p_wf2.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff5).
+ move=> p_wf3.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff5).
by smt().
qed.

lemma haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs6 md p blk :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyq_coeffs_wf md p =>
  0 <= blk < 32 =>
  haetae_unpack_poly_q_mode23_coeff_at
    (haetae_pack_poly_q_ref md p) 0 blk 6 =
  poly_coeff p (8 * blk + 6).
proof.
move=> md23 p_wf blk_rng.
have c5_rng : 0 <= poly_coeff p (8 * blk + 5) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c6_rng : 0 <= poly_coeff p (8 * blk + 6) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c7_rng : 0 <= poly_coeff p (8 * blk + 7) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
move: p_wf md23; case: md => /=.
+ move=> p_wf2.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff6).
+ move=> p_wf3.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff6).
by smt().
qed.

lemma haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs7 md p blk :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyq_coeffs_wf md p =>
  0 <= blk < 32 =>
  haetae_unpack_poly_q_mode23_coeff_at
    (haetae_pack_poly_q_ref md p) 0 blk 7 =
  poly_coeff p (8 * blk + 7).
proof.
move=> md23 p_wf blk_rng.
have c6_rng : 0 <= poly_coeff p (8 * blk + 6) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
have c7_rng : 0 <= poly_coeff p (8 * blk + 7) < 32768
  by smt(haetae_polyq_mode23_coeff_rng).
move: p_wf md23; case: md => /=.
+ move=> p_wf2.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff7).
+ move=> p_wf3.
  rewrite /haetae_unpack_poly_q_mode23_coeff_at
          /haetae_pack_poly_q_ref /haetae_pack_poly_q_mode23_byte /=.
  by smt(nth_mkseq size_mkseq haetae_byte_norm_idempotent
         haetae_unpack15_coeff7).
by smt().
qed.

lemma haetae_unpack_poly_q_ref_pack_mode23_coeff md p i :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyq_coeffs_wf md p =>
  0 <= i < n =>
  haetae_unpack_poly_q_mode23_coeff_at
    (haetae_pack_poly_q_ref md p) 0 (i %/ 8) (i %% 8) =
  poly_coeff p i.
proof.
move=> md23 p_wf i_rng.
have blk_rng : 0 <= i %/ 8 < 32 by rewrite /n in i_rng; smt().
have ofs_cases :
  i %% 8 = 0 \/ i %% 8 = 1 \/ i %% 8 = 2 \/ i %% 8 = 3 \/
  i %% 8 = 4 \/ i %% 8 = 5 \/ i %% 8 = 6 \/ i %% 8 = 7
  by smt().
case: ofs_cases => [ofs0 | ofs_cases].
+ rewrite ofs0.
  have rhs0 : poly_coeff p i = poly_coeff p (8 * (i %/ 8) + 0)
    by smt().
  rewrite rhs0.
  by apply haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs0.
case: ofs_cases => [ofs1 | ofs_cases].
+ rewrite ofs1.
  have rhs1 : poly_coeff p i = poly_coeff p (8 * (i %/ 8) + 1)
    by smt().
  rewrite rhs1.
  by apply haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs1.
case: ofs_cases => [ofs2 | ofs_cases].
+ rewrite ofs2.
  have rhs2 : poly_coeff p i = poly_coeff p (8 * (i %/ 8) + 2)
    by smt().
  rewrite rhs2.
  by apply haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs2.
case: ofs_cases => [ofs3 | ofs_cases].
+ rewrite ofs3.
  have rhs3 : poly_coeff p i = poly_coeff p (8 * (i %/ 8) + 3)
    by smt().
  rewrite rhs3.
  by apply haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs3.
case: ofs_cases => [ofs4 | ofs_cases].
+ rewrite ofs4.
  have rhs4 : poly_coeff p i = poly_coeff p (8 * (i %/ 8) + 4)
    by smt().
  rewrite rhs4.
  by apply haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs4.
case: ofs_cases => [ofs5 | ofs_cases].
+ rewrite ofs5.
  have rhs5 : poly_coeff p i = poly_coeff p (8 * (i %/ 8) + 5)
    by smt().
  rewrite rhs5.
  by apply haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs5.
case: ofs_cases => [ofs6 | ofs7].
+ rewrite ofs6.
  have rhs6 : poly_coeff p i = poly_coeff p (8 * (i %/ 8) + 6)
    by smt().
  rewrite rhs6.
  by apply haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs6.
rewrite ofs7.
have rhs7 : poly_coeff p i = poly_coeff p (8 * (i %/ 8) + 7)
  by smt().
rewrite rhs7.
by apply haetae_unpack_poly_q_ref_pack_mode23_coeff_ofs7.
qed.

lemma haetae_unpack_poly_q_ref_pack_mode23_at md prefix p :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyq_coeffs_wf md p =>
  haetae_unpack_poly_q_ref_at md
    (prefix ++ haetae_pack_poly_q_ref md p) (size prefix) = p.
proof.
move=> md23 p_wf.
case: md md23 p_wf => /=.
+ move=> p_wf2.
  rewrite /haetae_unpack_poly_q_ref_at /=.
  apply/(eq_from_nth 0).
  + rewrite size_mkseq.
    move: p_wf2; rewrite /haetae_polyq_coeffs_wf /poly_wf => -[p_sz _].
    by rewrite p_sz.
  move=> i i_rng.
  rewrite size_mkseq in i_rng.
  rewrite nth_mkseq; first by smt().
  by smt(haetae_unpack_poly_q_mode23_coeff_at_cat
         haetae_unpack_poly_q_ref_pack_mode23_coeff).
+ move=> p_wf3.
  rewrite /haetae_unpack_poly_q_ref_at /=.
  apply/(eq_from_nth 0).
  + rewrite size_mkseq.
    move: p_wf3; rewrite /haetae_polyq_coeffs_wf /poly_wf => -[p_sz _].
    by rewrite p_sz.
  move=> i i_rng.
  rewrite size_mkseq in i_rng.
  rewrite nth_mkseq; first by smt().
  by smt(haetae_unpack_poly_q_mode23_coeff_at_cat
         haetae_unpack_poly_q_ref_pack_mode23_coeff).
by smt().
qed.

lemma haetae_unpack_poly_q_mode23_coeff_at_body md prefix b row blk ofs :
  (md = Mode2 \/ md = Mode3) =>
  0 <= row < mode_k md =>
  0 <= blk < 32 =>
  haetae_unpack_poly_q_mode23_coeff_at
    (prefix ++ haetae_pack_polyveck_body_ref md b)
    (size prefix + row * mode_polyq_packedbytes md) blk ofs =
  haetae_unpack_poly_q_mode23_coeff_at
    (haetae_pack_poly_q_ref md (nth poly_zero b row)) 0 blk ofs.
proof.
move=> md23 row_rng blk_rng.
rewrite /haetae_unpack_poly_q_mode23_coeff_at.
by smt(nth_cat haetae_pack_polyveck_body_ref_nth
       mode_polyq_packedbytes_gt0).
qed.

lemma haetae_unpack_polyveck_body_ref_pack_mode23_coeff md prefix b row i :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyveck_polyq_coeffs_wf md b =>
  0 <= row < mode_k md =>
  0 <= i < n =>
  haetae_unpack_poly_q_mode23_coeff_at
    (prefix ++ haetae_pack_polyveck_body_ref md b)
    (size prefix + row * mode_polyq_packedbytes md) (i %/ 8) (i %% 8) =
  poly_coeff (nth poly_zero b row) i.
proof.
move=> md23 b_wf row_rng i_rng.
have row_wf :
  haetae_polyq_coeffs_wf md (nth poly_zero b row).
+ move: b_wf; rewrite /haetae_polyveck_polyq_coeffs_wf => -[_ b_rng].
  by apply b_rng.
rewrite (haetae_unpack_poly_q_mode23_coeff_at_body md prefix b row
           (i %/ 8) (i %% 8)).
+ by smt().
+ by smt().
+ by rewrite /n in i_rng; smt().
by apply haetae_unpack_poly_q_ref_pack_mode23_coeff.
qed.

lemma haetae_unpack_polyveck_body_ref_pack_mode23 md prefix b :
  (md = Mode2 \/ md = Mode3) =>
  haetae_polyveck_polyq_coeffs_wf md b =>
  haetae_unpack_polyveck_body_ref md
    (prefix ++ haetae_pack_polyveck_body_ref md b)
    (size prefix) = b.
proof.
move=> md23 b_wf.
rewrite /haetae_unpack_polyveck_body_ref.
apply/(eq_from_nth poly_zero).
  + rewrite size_mkseq.
    move: b_wf; rewrite /haetae_polyveck_polyq_coeffs_wf
                            /polyveck_wf => -[[b_sz _] _].
    by smt().
move=> row row_rng.
rewrite size_mkseq in row_rng.
rewrite nth_mkseq; first by smt().
case: md md23 b_wf row_rng => /=.
+ move=> b_wf2 row_rng2.
  rewrite /haetae_unpack_poly_q_ref_at /=.
  apply/(eq_from_nth 0).
  + rewrite size_mkseq.
    move: b_wf2; rewrite /haetae_polyveck_polyq_coeffs_wf
                       /polyveck_wf => -[[b_sz _] b_rng].
    have row_p_wf := b_rng row _.
    + by smt().
    move: row_p_wf; rewrite /haetae_polyq_coeffs_wf /poly_wf => -[row_sz _].
    by rewrite row_sz.
  move=> i i_rng.
  rewrite size_mkseq in i_rng.
  rewrite nth_mkseq; first by smt().
  by apply haetae_unpack_polyveck_body_ref_pack_mode23_coeff.
+ move=> b_wf3 row_rng3.
  rewrite /haetae_unpack_poly_q_ref_at /=.
  apply/(eq_from_nth 0).
  + rewrite size_mkseq.
    move: b_wf3; rewrite /haetae_polyveck_polyq_coeffs_wf
                       /polyveck_wf => -[[b_sz _] b_rng].
    have row_p_wf := b_rng row _.
    + by smt().
    move: row_p_wf; rewrite /haetae_polyq_coeffs_wf /poly_wf => -[row_sz _].
    by rewrite row_sz.
  move=> i i_rng.
  rewrite size_mkseq in i_rng.
  rewrite nth_mkseq; first by smt().
  by apply haetae_unpack_polyveck_body_ref_pack_mode23_coeff.
by smt().
qed.

lemma haetae_pack_vk_ref_roundtrip_mode23 md sd b :
  (md = Mode2 \/ md = Mode3) =>
  size sd = seedbytes =>
  haetae_polyveck_polyq_coeffs_wf md b =>
  haetae_unpack_vk_public_key_ref md
    (haetae_pack_vk_ref md b sd) = (sd, b).
proof.
move=> md23 sd_sz b_wf.
rewrite /haetae_unpack_vk_public_key_ref /haetae_pack_vk_ref /=.
rewrite (haetae_unpack_seed_pack_cat sd
          (haetae_pack_polyveck_body_ref md b) sd_sz).
have seed_sz : seedbytes = size (haetae_pack_seed sd).
+ by rewrite haetae_pack_seed_size.
rewrite seed_sz.
by rewrite (haetae_unpack_polyveck_body_ref_pack_mode23
              md (haetae_pack_seed sd) b md23 b_wf).
qed.

lemma haetae_unpack_poly_q_ref_pack_mode5_coeff p i :
  haetae_polyq_coeffs_wf Mode5 p =>
  0 <= i < n =>
  haetae_unpack_poly_q_mode5_coeff_at
    (haetae_pack_poly_q_ref Mode5 p) 0 i = poly_coeff p i.
proof.
move=> p_wf i_rng.
rewrite /haetae_unpack_poly_q_mode5_coeff_at
        /haetae_pack_poly_q_ref /= /haetae_pack_poly_q_mode5_byte
        /haetae_byte_norm /haetae_byte_modulus.
move: p_wf; rewrite /haetae_polyq_coeffs_wf
                  /haetae_polyq_coeff_bound
                  /haetae_polyq_mode5_bound => -[p_sz p_rng].
have ci_rng :
  0 <= poly_coeff p i < 65536 by smt().
by smt(nth_mkseq size_mkseq).
qed.

lemma haetae_unpack_poly_q_ref_pack_mode5_at prefix p :
  haetae_polyq_coeffs_wf Mode5 p =>
  haetae_unpack_poly_q_ref_at Mode5
    (prefix ++ haetae_pack_poly_q_ref Mode5 p) (size prefix) = p.
proof.
move=> p_wf.
rewrite /haetae_unpack_poly_q_ref_at /=.
apply/(eq_from_nth 0).
+ rewrite size_mkseq.
  move: p_wf; rewrite /haetae_polyq_coeffs_wf /poly_wf => -[p_sz _].
  by rewrite p_sz.
move=> i i_rng.
rewrite size_mkseq in i_rng.
rewrite nth_mkseq; first by smt().
rewrite /haetae_unpack_poly_q_mode5_coeff_at
        /haetae_pack_poly_q_ref /= /haetae_pack_poly_q_mode5_byte
        /haetae_byte_norm /haetae_byte_modulus.
move: p_wf; rewrite /haetae_polyq_coeffs_wf
                  /haetae_polyq_coeff_bound
                  /haetae_polyq_mode5_bound => -[p_sz p_rng].
have ci_rng :
  0 <= poly_coeff p i < 65536 by smt().
by smt(nth_cat nth_mkseq size_mkseq).
qed.

lemma haetae_unpack_polyveck_body_ref_pack_mode5_coeff prefix b row i :
  haetae_polyveck_polyq_coeffs_wf Mode5 b =>
  0 <= row < mode_k Mode5 =>
  0 <= i < n =>
  haetae_unpack_poly_q_mode5_coeff_at
    (prefix ++ haetae_pack_polyveck_body_ref Mode5 b)
    (size prefix + row * mode_polyq_packedbytes Mode5) i =
  poly_coeff (nth poly_zero b row) i.
proof.
move=> b_wf row_rng i_rng.
have row_wf :
  haetae_polyq_coeffs_wf Mode5 (nth poly_zero b row).
+ move: b_wf; rewrite /haetae_polyveck_polyq_coeffs_wf => -[_ b_rng].
  by apply b_rng.
rewrite /haetae_unpack_poly_q_mode5_coeff_at.
have lo :
  nth 0 (prefix ++ haetae_pack_polyveck_body_ref Mode5 b)
    (size prefix + row * mode_polyq_packedbytes Mode5 + 2 * i) =
  nth 0 (haetae_pack_poly_q_ref Mode5 (nth poly_zero b row))
    (2 * i).
+ have k_rng : 0 <= 2 * i < mode_polyq_packedbytes Mode5 by smt().
  have idxE :
    size prefix + row * mode_polyq_packedbytes Mode5 + 2 * i =
    size prefix + (row * mode_polyq_packedbytes Mode5 + 2 * i) by smt().
  have catE :
    nth 0 (prefix ++ haetae_pack_polyveck_body_ref Mode5 b)
      (size prefix + (row * mode_polyq_packedbytes Mode5 + 2 * i)) =
    nth 0 (haetae_pack_polyveck_body_ref Mode5 b)
      (row * mode_polyq_packedbytes Mode5 + 2 * i).
  + by apply nth_cat_size_plus; smt().
  rewrite idxE catE.
  by apply haetae_pack_polyveck_body_ref_mode5_nth.
have hi :
  nth 0 (prefix ++ haetae_pack_polyveck_body_ref Mode5 b)
    (size prefix + row * mode_polyq_packedbytes Mode5 + 2 * i + 1) =
  nth 0 (haetae_pack_poly_q_ref Mode5 (nth poly_zero b row))
    (2 * i + 1).
+ have k_rng : 0 <= 2 * i + 1 < mode_polyq_packedbytes Mode5 by smt().
  have idxE :
    size prefix + row * mode_polyq_packedbytes Mode5 + 2 * i + 1 =
    size prefix + (row * mode_polyq_packedbytes Mode5 + (2 * i + 1))
    by smt().
  have catE :
    nth 0 (prefix ++ haetae_pack_polyveck_body_ref Mode5 b)
      (size prefix + (row * mode_polyq_packedbytes Mode5 + (2 * i + 1))) =
    nth 0 (haetae_pack_polyveck_body_ref Mode5 b)
      (row * mode_polyq_packedbytes Mode5 + (2 * i + 1)).
  + by apply nth_cat_size_plus; smt().
  rewrite idxE catE.
  by apply haetae_pack_polyveck_body_ref_mode5_nth.
rewrite lo hi.
rewrite -/(haetae_unpack_poly_q_mode5_coeff_at
  (haetae_pack_poly_q_ref Mode5 (nth poly_zero b row)) 0 i).
by apply haetae_unpack_poly_q_ref_pack_mode5_coeff.
qed.

lemma haetae_unpack_polyveck_body_ref_pack_mode5 prefix b :
  haetae_polyveck_polyq_coeffs_wf Mode5 b =>
  haetae_unpack_polyveck_body_ref Mode5
    (prefix ++ haetae_pack_polyveck_body_ref Mode5 b)
    (size prefix) = b.
proof.
move=> b_wf.
rewrite /haetae_unpack_polyveck_body_ref /=.
apply/(eq_from_nth poly_zero).
+ rewrite size_mkseq.
  move: b_wf; rewrite /haetae_polyveck_polyq_coeffs_wf
                          /polyveck_wf => -[[b_sz _] _].
  by rewrite b_sz.
move=> row row_rng.
rewrite size_mkseq in row_rng.
rewrite nth_mkseq; first by smt().
rewrite /haetae_unpack_poly_q_ref_at /=.
apply/(eq_from_nth 0).
+ rewrite size_mkseq.
  move: b_wf; rewrite /haetae_polyveck_polyq_coeffs_wf
                     /polyveck_wf => -[[b_sz _] b_rng].
  have row_p_wf := b_rng row _.
  + by smt().
  move: row_p_wf; rewrite /haetae_polyq_coeffs_wf /poly_wf => -[row_sz _].
  by rewrite row_sz.
move=> i i_rng.
rewrite size_mkseq in i_rng.
rewrite nth_mkseq; first by smt().
by apply haetae_unpack_polyveck_body_ref_pack_mode5_coeff.
qed.

lemma haetae_pack_vk_ref_roundtrip_mode5 sd b :
  size sd = seedbytes =>
  haetae_polyveck_polyq_coeffs_wf Mode5 b =>
  haetae_unpack_vk_public_key_ref Mode5
    (haetae_pack_vk_ref Mode5 b sd) = (sd, b).
proof.
move=> sd_sz b_wf.
rewrite /haetae_unpack_vk_public_key_ref /haetae_pack_vk_ref /=.
rewrite (haetae_unpack_seed_pack_cat sd
          (haetae_pack_polyveck_body_ref Mode5 b) sd_sz).
have seed_sz : seedbytes = size (haetae_pack_seed sd).
+ by rewrite haetae_pack_seed_size.
rewrite seed_sz.
by rewrite (haetae_unpack_polyveck_body_ref_pack_mode5
              (haetae_pack_seed sd) b b_wf).
qed.

lemma haetae_public_key_ref_roundtrip md (pk : pkey) :
  size pk.`1 = seedbytes =>
  haetae_polyveck_polyq_coeffs_wf md pk.`2 =>
  haetae_unpack_public_key_bytes_ref md
    (haetae_pack_public_key_bytes_ref md pk) = pk.
proof.
case: pk => sd b /=.
move=> sd_sz b_wf.
rewrite /haetae_unpack_public_key_bytes_ref
        /haetae_pack_public_key_bytes_ref.
case: md b_wf => /= b_wf.
+ apply haetae_pack_vk_ref_roundtrip_mode23.
  + by left.
  + by apply sd_sz.
  by apply b_wf.
+ apply haetae_pack_vk_ref_roundtrip_mode23.
  + by right.
  + by apply sd_sz.
  by apply b_wf.
by apply haetae_pack_vk_ref_roundtrip_mode5;
   [apply sd_sz | apply b_wf].
qed.

lemma haetae_keygen_public_key_ref_roundtrip md sd :
  size sd = seedbytes =>
  haetae_unpack_vk_public_key_ref md
    (haetae_pack_vk_ref md (haetae_keygen_public_vector md sd) sd) =
  packed_haetae_public_key md sd.
proof.
move=> sd_sz.
rewrite /packed_haetae_public_key.
have h :=
  haetae_public_key_ref_roundtrip md
    (sd, haetae_keygen_public_vector md sd)
    sd_sz (haetae_keygen_public_vector_polyq_wf md sd).
by move: h; rewrite /haetae_unpack_public_key_bytes_ref
                   /haetae_pack_public_key_bytes_ref.
qed.

lemma haetae_pack_polyveck_body_size md b :
  size (haetae_pack_polyveck_body md b) = haetae_public_key_body_bytes md.
proof.
by rewrite /haetae_pack_polyveck_body /haetae_public_key_body_bytes
           size_mkseq; case md.
qed.

lemma haetae_pack_poly_q_size md p :
  size (haetae_pack_poly_q md p) = mode_polyq_packedbytes md.
proof. by rewrite /haetae_pack_poly_q size_mkseq; case md. qed.

lemma haetae_unpack_poly_q_at_wf md enc offset :
  poly_wf (haetae_unpack_poly_q_at md enc offset).
proof. by rewrite /poly_wf /haetae_unpack_poly_q_at size_mkseq /n. qed.

lemma haetae_unpack_poly_q_pack_at md prefix p :
  poly_wf p =>
  haetae_unpack_poly_q_at md (prefix ++ haetae_pack_poly_q md p)
    (size prefix) = p.
proof.
move=> p_wf.
rewrite /haetae_unpack_poly_q_at.
apply/(eq_from_nth 0).
+ rewrite size_mkseq.
  by move: p_wf; rewrite /poly_wf => ->.
move=> i i_rng.
rewrite size_mkseq in i_rng.
rewrite nth_mkseq; first by smt().
rewrite /haetae_pack_poly_q /poly_coeff.
by smt(nth_cat nth_mkseq n_le_mode_polyq_packedbytes).
qed.

lemma haetae_unpack_polyveck_body_wf md enc offset :
  polyveck_wf md (haetae_unpack_polyveck_body md enc offset).
proof.
rewrite /polyveck_wf /haetae_unpack_polyveck_body size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by rewrite /poly_wf size_mkseq /n.
qed.

lemma haetae_body_index_div md row col :
  0 <= row =>
  0 <= col < n =>
  (row * mode_polyq_packedbytes md + col)
    %/ mode_polyq_packedbytes md = row.
proof. by case md; rewrite /mode_polyq_packedbytes /n; smt(). qed.

lemma haetae_body_index_mod md row col :
  0 <= row =>
  0 <= col < n =>
  (row * mode_polyq_packedbytes md + col)
    %% mode_polyq_packedbytes md = col.
proof. by case md; rewrite /mode_polyq_packedbytes /n; smt(). qed.

lemma haetae_body_index_lt md row col :
  0 <= row < mode_k md =>
  0 <= col < n =>
  row * mode_polyq_packedbytes md + col <
    haetae_public_key_body_bytes md.
proof.
rewrite /haetae_public_key_body_bytes.
by smt(n_le_mode_polyq_packedbytes mode_polyq_packedbytes_gt0).
qed.

lemma haetae_unpack_polyveck_body_pack_at md prefix b :
  polyveck_wf md b =>
  haetae_unpack_polyveck_body md
    (prefix ++ haetae_pack_polyveck_body md b) (size prefix) = b.
proof.
move=> b_wf.
rewrite /haetae_unpack_polyveck_body.
apply/(eq_from_nth poly_zero).
+ by rewrite size_mkseq; smt().
move=> row row_rng.
rewrite size_mkseq in row_rng.
rewrite nth_mkseq; first by smt().
apply/(eq_from_nth 0).
+ by rewrite size_mkseq; smt(polyveck_wf_nth).
move=> col col_rng.
rewrite size_mkseq in col_rng.
rewrite nth_mkseq; first by smt().
rewrite /haetae_pack_polyveck_body /poly_coeff.
by smt(nth_cat nth_mkseq haetae_body_index_div haetae_body_index_mod
       haetae_body_index_lt n_le_mode_polyq_packedbytes
       mode_polyq_packedbytes_gt0).
qed.

lemma haetae_unpack_polyveck_body_pack md sd b :
  polyveck_wf md b =>
  haetae_unpack_polyveck_body md
    (haetae_pack_seed sd ++ haetae_pack_polyveck_body md b)
    seedbytes = b.
proof.
move=> b_wf.
have seed_sz := haetae_pack_seed_size sd.
rewrite -seed_sz.
by apply haetae_unpack_polyveck_body_pack_at.
qed.

lemma haetae_public_key_roundtrip md pk :
  haetae_public_key_unpacked_wf md pk =>
  haetae_public_key_roundtrip_ok md pk.
proof.
case: pk => sd b /=.
rewrite /haetae_public_key_unpacked_wf /haetae_public_key_roundtrip_ok
        /haetae_unpack_public_key_bytes /haetae_pack_public_key_bytes
        /haetae_unpack_vk_public_key /haetae_pack_vk /=.
move=> [sd_sz b_wf].
by rewrite (haetae_unpack_seed_pack_cat sd
             (haetae_pack_polyveck_body md b) sd_sz)
           (haetae_unpack_polyveck_body_pack md sd b b_wf).
qed.

lemma haetae_pack_public_key_bytes_size md pk :
  size (haetae_pack_public_key_bytes md pk) = haetae_public_key_bytes md.
proof.
rewrite /haetae_pack_public_key_bytes /haetae_pack_vk
        /haetae_public_key_bytes /mode_publickeybytes.
by rewrite size_cat haetae_pack_seed_size haetae_pack_polyveck_body_size.
qed.

lemma haetae_pack_public_key_bytes_wf md pk :
  haetae_public_key_encoding_wf md (haetae_pack_public_key_bytes md pk).
proof.
by rewrite /haetae_public_key_encoding_wf haetae_pack_public_key_bytes_size.
qed.

lemma haetae_pack_public_key_bytes_ref_size md pk :
  size (haetae_pack_public_key_bytes_ref md pk) =
  haetae_public_key_bytes md.
proof.
by rewrite /haetae_pack_public_key_bytes_ref haetae_pack_vk_ref_size.
qed.

lemma haetae_pack_public_key_bytes_ref_wf md pk :
  haetae_public_key_encoding_wf md
    (haetae_pack_public_key_bytes_ref md pk).
proof.
by rewrite /haetae_public_key_encoding_wf
           haetae_pack_public_key_bytes_ref_size.
qed.

lemma haetae_unpack_public_key_bytes_wf md enc :
  haetae_public_key_unpacked_wf md
    (haetae_unpack_public_key_bytes md enc).
proof.
rewrite /haetae_public_key_unpacked_wf /haetae_unpack_public_key_bytes
        /haetae_unpack_vk_public_key /=.
have seed_sz := haetae_unpack_seed_size enc.
have body_wf := haetae_unpack_polyveck_body_wf md enc seedbytes.
by rewrite seed_sz body_wf.
qed.

lemma haetae_unpack_public_key_bytes_ref_wf md enc :
  haetae_public_key_unpacked_wf md
    (haetae_unpack_public_key_bytes_ref md enc).
proof.
by rewrite /haetae_unpack_public_key_bytes_ref;
   apply haetae_unpack_vk_public_key_ref_wf.
qed.

lemma concrete_haetae_keygen_packed_public_key_wf md sd :
  haetae_public_key_encoding_wf md
    (concrete_haetae_keygen_packed_public_key md sd).
proof.
by rewrite /concrete_haetae_keygen_packed_public_key
           haetae_pack_public_key_bytes_wf.
qed.

lemma concrete_haetae_keygen_unpacked_public_key_wf md sd :
  haetae_public_key_unpacked_wf md
    (concrete_haetae_keygen_unpacked_public_key md sd).
proof.
by rewrite /concrete_haetae_keygen_unpacked_public_key;
   apply haetae_unpack_public_key_bytes_wf.
qed.

lemma concrete_haetae_keygen_packed_public_key_ref_wf md sd :
  haetae_public_key_encoding_wf md
    (concrete_haetae_keygen_packed_public_key_ref md sd).
proof.
by rewrite /concrete_haetae_keygen_packed_public_key_ref
           haetae_pack_public_key_bytes_ref_wf.
qed.

lemma concrete_haetae_keygen_unpacked_public_key_ref_wf md sd :
  haetae_public_key_unpacked_wf md
    (concrete_haetae_keygen_unpacked_public_key_ref md sd).
proof.
by rewrite /concrete_haetae_keygen_unpacked_public_key_ref;
   apply haetae_unpack_public_key_bytes_ref_wf.
qed.

lemma packed_haetae_reference_public_key_wf md sd :
  polyveck_wf md (packed_haetae_reference_public_key md sd).`2.
proof.
have h := haetae_reference_keygen_public_vector_polyq_wf md sd.
by move: h; rewrite /haetae_polyveck_polyq_coeffs_wf
                    /packed_haetae_reference_public_key.
qed.

lemma packed_haetae_reference_public_key_polyq_wf md sd :
  haetae_polyveck_polyq_coeffs_wf md
    (packed_haetae_reference_public_key md sd).`2.
proof.
by rewrite /packed_haetae_reference_public_key /=;
   apply haetae_reference_keygen_public_vector_polyq_wf.
qed.

lemma packed_haetae_reference_public_key_unpacked_wf md sd :
  haetae_public_key_unpacked_wf md
    (packed_haetae_reference_public_key md sd).
proof.
rewrite /haetae_public_key_unpacked_wf
        /packed_haetae_reference_public_key /=.
split.
+ by apply haetae_keygen_rhoprime_size.
have h := haetae_reference_keygen_public_vector_polyq_wf md sd.
by move: h; rewrite /haetae_polyveck_polyq_coeffs_wf.
qed.

lemma concrete_haetae_reference_keygen_packed_public_key_ref_wf md sd :
  haetae_public_key_encoding_wf md
    (concrete_haetae_reference_keygen_packed_public_key_ref md sd).
proof.
by rewrite /concrete_haetae_reference_keygen_packed_public_key_ref
           haetae_pack_public_key_bytes_ref_wf.
qed.

lemma concrete_haetae_reference_keygen_unpacked_public_key_ref_wf md sd :
  haetae_public_key_unpacked_wf md
    (concrete_haetae_reference_keygen_unpacked_public_key_ref md sd).
proof.
by rewrite /concrete_haetae_reference_keygen_unpacked_public_key_ref;
   apply haetae_unpack_public_key_bytes_ref_wf.
qed.

lemma haetae_reference_keygen_public_key_ref_roundtrip md sd :
  haetae_unpack_public_key_bytes_ref md
    (haetae_pack_public_key_bytes_ref md
      (packed_haetae_reference_public_key md sd)) =
  packed_haetae_reference_public_key md sd.
proof.
apply haetae_public_key_ref_roundtrip.
+ by rewrite /packed_haetae_reference_public_key /=;
      apply haetae_keygen_rhoprime_size.
by apply packed_haetae_reference_public_key_polyq_wf.
qed.

lemma public_key_of_secret_relation md sk :
  public_key_relation md
    (public_key_of_secret md sk)
    (public_secret_vector_seed md sk.`1)
    (public_error_vector_seed md sk.`1).
proof.
by rewrite /public_key_relation /public_key_of_secret
           /public_key_vector_seed /haetae_keygen_public_vector
           /haetae_keygen_secret_vector /haetae_keygen_error_vector.
qed.

lemma public_key_of_secret_equation_holds md sk :
  public_key_equation_holds md (public_key_of_secret md sk).
proof.
by rewrite /public_key_equation_holds public_key_of_secret_relation.
qed.

op valid_mode : mode -> bool = fun _ => true.
op valid_keypair (md : mode) (pk : pkey) (sk : skey) : bool =
  pk = public_key_of_secret md sk.
op valid_signature (md : mode) (sig : signature) : bool =
  polyveck_wf md sig.`1 /\
  poly_wf sig.`2 /\
  crh_wf sig.`3 /\
  challenge_wf sig.`4 /\
  polyvecl_wf md (sig.`5).`1 /\
  polyveck_wf md (sig.`5).`2 /\
  polyveck_wf md (sig.`5).`3.

op sig_commitment_highbits (sig : signature) : polyveck = sig.`1.
op sig_commitment_lowbits (sig : signature) : poly = sig.`2.
op sig_message_hash (sig : signature) : crh = sig.`3.
op sig_challenge (sig : signature) : challenge = sig.`4.
op sig_token_value (sig : signature) : sig_token = sig.`5.
op sig_response (sig : signature) : polyvecl = (sig_token_value sig).`1.
op sig_response_aux (sig : signature) : polyveck = (sig_token_value sig).`2.
op sig_hint (sig : signature) : hint_t = (sig_token_value sig).`3.

op encode_poly (p : poly) : byte list = p.
op encode_polyveck (xs : polyveck) : byte list = flatten xs.
op encode_pkey (pk : pkey) : byte list = pk.`1 ++ encode_polyveck pk.`2.

op deterministic_poly (tag : int) (src : byte list) : poly =
  mkseq (fun i => coeff_mod (tag + i + nth 0 src i)) n.
op deterministic_polyveck (md : mode) (src : byte list) : polyveck =
  mkseq
    (fun i => deterministic_poly i (i :: src))
    (mode_k md).
op deterministic_unit_coeff (tag : int) (src : byte list) (i : int) :
  coeff =
  if (tag + i + nth 0 src i) %% 2 = 0 then 1 else -1.
op deterministic_unit_poly (tag : int) (src : byte list) : poly =
  mkseq (fun i => deterministic_unit_coeff tag src i) n.
op deterministic_unit_polyveck
   (md : mode) (tag : int) (src : byte list) : polyveck =
  mkseq
    (fun i => deterministic_unit_poly (tag + i) (i :: src))
    (mode_k md).
op deterministic_unit_polyvecl
   (md : mode) (tag : int) (src : byte list) : polyvecl =
  mkseq
    (fun i => deterministic_unit_poly (tag + i) (i :: src))
    (mode_l md).
op commitment_source
   (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) : byte list =
  coins ++ sk.`1 ++ ctx ++ m.
op commitment_raw :
  mode -> skey -> message -> context -> random_coins -> polyveck =
  fun md sk m ctx coins =>
    deterministic_polyveck md (commitment_source sk m ctx coins).
op response_source
   (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) : byte list =
  coins ++ sk.`1 ++ ctx ++ m.
op response_aux_vector :
  mode -> skey -> message -> context -> random_coins -> polyveck =
  fun md sk m ctx coins =>
    deterministic_unit_polyveck md 29 (response_source sk m ctx coins).
op signing_sample_y1 :
  mode -> skey -> message -> context -> random_coins -> polyvecl =
  fun md sk m ctx coins =>
    deterministic_unit_polyvecl md 73 (response_source sk m ctx coins).
op signing_sample_y2 :
  mode -> skey -> message -> context -> random_coins -> polyveck =
  fun md sk m ctx coins =>
    deterministic_unit_polyveck md 79 (response_source sk m ctx coins).
op signing_entropy_token_of_coins (coins : random_coins) : int =
  nth 0 coins 0 +
  256 * nth 0 coins 1 +
  65536 * nth 0 coins 2 +
  16777216 * nth 0 coins 3 +
  4294967296 * nth 0 coins 4 +
  1099511627776 * nth 0 coins 5 +
  281474976710656 * nth 0 coins 6 +
  72057594037927936 * nth 0 coins 7.
op commitment_lowbits :
  mode -> skey -> message -> context -> random_coins -> poly =
  fun md sk m ctx coins =>
    let raw = nth poly_zero (commitment_raw md sk m ctx coins) 0 in
    mkseq
      (fun i =>
        if i = 0 then signing_entropy_token_of_coins coins
        else poly_coeff raw i)
      n.
op message_hash : pkey -> context -> message -> crh =
  fun pk ctx m => mkseq (fun i => nth 0 (encode_pkey pk ++ ctx ++ m) i) crhbytes.
op challenge_source (highbits : polyveck) (lowbits : poly) (mu : crh) :
  byte list =
  encode_poly lowbits ++ encode_polyveck highbits ++ mu.
op challenge_from_seed (md : mode) (src : byte list) : challenge =
  mkseq
    (fun i =>
      if i < mode_tau md
      then if nth 0 src i %% 2 = 0 then 1 else -1
      else 0) n.
op challenge_hash : mode -> polyveck -> poly -> crh -> challenge =
  fun md (_ : polyveck) lowbits mu =>
    challenge_from_seed md (encode_poly lowbits ++ mu).
op commitment_challenge :
  mode -> skey -> message -> context -> random_coins -> challenge =
  fun md sk m ctx coins =>
    challenge_hash md
      (response_aux_vector md sk m ctx coins)
      (commitment_lowbits md sk m ctx coins)
      (message_hash (public_key_of_secret md sk) ctx m).
op commitment_highbits :
  mode -> skey -> message -> context -> random_coins -> polyveck =
  fun md sk m ctx coins =>
    let pk = public_key_of_secret md sk in
    let ch = commitment_challenge md sk m ctx coins in
    reconstructed_highbits md
      (response_aux_vector md sk m ctx coins)
      (public_key_challenge_term md pk ch).
op response_vector :
  mode -> skey -> message -> context -> random_coins -> polyvecl =
  fun md sk m ctx coins =>
    deterministic_unit_polyvecl md 17 (response_source sk m ctx coins).
op hint_vector :
  mode -> skey -> message -> context -> random_coins -> hint_t =
  fun md sk m ctx coins =>
    deterministic_unit_polyveck md 41 (response_source sk m ctx coins).
op signature_token :
  mode -> skey -> message -> context -> random_coins -> sig_token =
  fun md sk m ctx coins =>
    ( response_vector md sk m ctx coins,
      response_aux_vector md sk m ctx coins,
      hint_vector md sk m ctx coins).

lemma deterministic_poly_wf tag src :
  poly_wf (deterministic_poly tag src).
proof. by rewrite /poly_wf /deterministic_poly size_mkseq /n. qed.

lemma deterministic_polyveck_wf md src :
  polyveck_wf md (deterministic_polyveck md src).
proof.
rewrite /polyveck_wf /deterministic_polyveck size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply deterministic_poly_wf.
qed.

lemma deterministic_unit_poly_wf tag src :
  poly_wf (deterministic_unit_poly tag src).
proof. by rewrite /poly_wf /deterministic_unit_poly size_mkseq /n. qed.

lemma deterministic_unit_poly_unit tag src :
  poly_unit (deterministic_unit_poly tag src).
proof.
rewrite /poly_unit.
split.
+ by apply deterministic_unit_poly_wf.
apply/allP=> x /mkseqP [i [_ ->]].
rewrite /deterministic_unit_poly /deterministic_unit_coeff /unit_coeff_ok.
by case: ((tag + i + nth 0 src i) %% 2 = 0).
qed.

lemma deterministic_unit_polyveck_wf md tag src :
  polyveck_wf md (deterministic_unit_polyveck md tag src).
proof.
rewrite /polyveck_wf /deterministic_unit_polyveck size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply deterministic_unit_poly_wf.
qed.

lemma deterministic_unit_polyveck_unit md tag src :
  polyveck_unit md (deterministic_unit_polyveck md tag src).
proof.
rewrite /polyveck_unit.
split.
+ by apply deterministic_unit_polyveck_wf.
apply/allP=> p /mkseqP [i [_ ->]].
by apply deterministic_unit_poly_unit.
qed.

lemma deterministic_unit_polyvecl_wf md tag src :
  polyvecl_wf md (deterministic_unit_polyvecl md tag src).
proof.
rewrite /polyvecl_wf /deterministic_unit_polyvecl size_mkseq.
split.
+ by case md.
apply/allP=> p /mkseqP [i [_ ->]].
by apply deterministic_unit_poly_wf.
qed.

lemma deterministic_unit_polyvecl_unit md tag src :
  polyvecl_unit md (deterministic_unit_polyvecl md tag src).
proof.
rewrite /polyvecl_unit.
split.
+ by apply deterministic_unit_polyvecl_wf.
apply/allP=> p /mkseqP [i [_ ->]].
by apply deterministic_unit_poly_unit.
qed.

lemma commitment_raw_wf md sk m ctx coins :
  polyveck_wf md (commitment_raw md sk m ctx coins).
proof.
by rewrite /commitment_raw; apply deterministic_polyveck_wf.
qed.

lemma commitment_highbits_wf md sk m ctx coins :
  polyveck_wf md (commitment_highbits md sk m ctx coins).
proof.
by rewrite /commitment_highbits /reconstructed_highbits /=;
   apply polyveck_add_wf.
qed.

lemma commitment_lowbits_wf md sk m ctx coins :
  poly_wf (commitment_lowbits md sk m ctx coins).
proof.
rewrite /commitment_lowbits /poly_wf.
by smt.
qed.

lemma commitment_lowbits_entropy_token md sk m ctx coins :
  nth 0 (commitment_lowbits md sk m ctx coins) 0 =
  signing_entropy_token_of_coins coins.
proof.
rewrite /commitment_lowbits /= nth_mkseq; first by smt(n_gt0).
case: (0 = 0) => z.
+ by smt.
by smt.
qed.

lemma challenge_from_seed_wf md src :
  challenge_wf (challenge_from_seed md src).
proof.
rewrite /challenge_wf.
split.
+ by rewrite /poly_wf /challenge_from_seed size_mkseq /n.
apply/allP=> x /mkseqP [i [_ ->]].
rewrite /challenge_coeff_ok /challenge_from_seed.
case: (i < mode_tau md) => //=.
by case: (nth 0 src i %% 2 = 0).
qed.

lemma challenge_from_seed_sparse md src :
  challenge_sparse md (challenge_from_seed md src).
proof.
rewrite /challenge_sparse.
split.
+ by rewrite /challenge_from_seed size_mkseq /n.
move=> i [ge0_i lt_i].
rewrite /challenge_sparse_at /challenge_from_seed nth_mkseq.
+ by split.
case: (i < mode_tau md) => h_tau /=.
+ rewrite h_tau /unit_coeff_ok.
  by case: (nth 0 src i %% 2 = 0).
by rewrite h_tau.
qed.

lemma challenge_hash_wf md w1 w0 mu :
  challenge_wf (challenge_hash md w1 w0 mu).
proof. by rewrite /challenge_hash; apply challenge_from_seed_wf. qed.

lemma challenge_hash_sparse md w1 w0 mu :
  challenge_sparse md (challenge_hash md w1 w0 mu).
proof. by rewrite /challenge_hash; apply challenge_from_seed_sparse. qed.

lemma response_vector_wf md sk m ctx coins :
  polyvecl_wf md (response_vector md sk m ctx coins).
proof.
by rewrite /response_vector; apply deterministic_unit_polyvecl_wf.
qed.

lemma response_vector_unit md sk m ctx coins :
  polyvecl_unit md (response_vector md sk m ctx coins).
proof.
by rewrite /response_vector; apply deterministic_unit_polyvecl_unit.
qed.

lemma response_aux_vector_wf md sk m ctx coins :
  polyveck_wf md (response_aux_vector md sk m ctx coins).
proof.
by rewrite /response_aux_vector; apply deterministic_unit_polyveck_wf.
qed.

lemma response_aux_vector_unit md sk m ctx coins :
  polyveck_unit md (response_aux_vector md sk m ctx coins).
proof.
by rewrite /response_aux_vector; apply deterministic_unit_polyveck_unit.
qed.

lemma signing_sample_y1_wf md sk m ctx coins :
  polyvecl_wf md (signing_sample_y1 md sk m ctx coins).
proof.
by rewrite /signing_sample_y1; apply deterministic_unit_polyvecl_wf.
qed.

lemma signing_sample_y1_unit md sk m ctx coins :
  polyvecl_unit md (signing_sample_y1 md sk m ctx coins).
proof.
by rewrite /signing_sample_y1; apply deterministic_unit_polyvecl_unit.
qed.

lemma signing_sample_y2_wf md sk m ctx coins :
  polyveck_wf md (signing_sample_y2 md sk m ctx coins).
proof.
by rewrite /signing_sample_y2; apply deterministic_unit_polyveck_wf.
qed.

lemma signing_sample_y2_unit md sk m ctx coins :
  polyveck_unit md (signing_sample_y2 md sk m ctx coins).
proof.
by rewrite /signing_sample_y2; apply deterministic_unit_polyveck_unit.
qed.

lemma hint_vector_wf md sk m ctx coins :
  polyveck_wf md (hint_vector md sk m ctx coins).
proof.
by rewrite /hint_vector; apply deterministic_unit_polyveck_wf.
qed.

lemma hint_vector_unit md sk m ctx coins :
  polyveck_unit md (hint_vector md sk m ctx coins).
proof.
by rewrite /hint_vector; apply deterministic_unit_polyveck_unit.
qed.

lemma message_hash_size pk ctx m :
  size (message_hash pk ctx m) = crhbytes.
proof. by rewrite /message_hash size_mkseq /crhbytes. qed.

lemma challenge_hash_size md w1 w0 mu :
  size (challenge_hash md w1 w0 mu) = n.
proof. by rewrite /challenge_hash /challenge_from_seed size_mkseq /n. qed.

op keygen_internal (md : mode) (sd : seed) : pkey * skey =
  let sk = secret_key_of_seed md sd in (public_key_of_secret md sk, sk).
op sign_internal :
  mode -> skey -> message -> context -> random_coins -> signature =
  fun (md : mode) (sk : skey) (m : message) (ctx : context)
      (coins : random_coins) =>
    let pk = public_key_of_secret md sk in
    let highbits = commitment_highbits md sk m ctx coins in
    let lowbits = commitment_lowbits md sk m ctx coins in
    let mu = message_hash pk ctx m in
    let ch = commitment_challenge md sk m ctx coins in
    (highbits, lowbits, mu, ch, signature_token md sk m ctx coins, 0, 0).

op verify_challenge_consistent
   (md : mode) (pk : pkey) (m : message) (ctx : context)
   (sig : signature) : bool =
  let mu = message_hash pk ctx m in
  sig_message_hash sig = mu /\
  sig_challenge sig =
    challenge_hash md
      (sig_commitment_highbits sig)
      (sig_commitment_lowbits sig)
      mu.

op verify_reconstructed_highbits
   (md : mode) (pk : pkey) (sig : signature) : polyveck =
  let pk_ch = public_key_challenge_term md pk (sig_challenge sig) in
  reconstructed_highbits md (sig_response_aux sig) pk_ch.

op verify_public_equation
   (md : mode) (pk : pkey) (sig : signature) : bool =
  sig_commitment_highbits sig =
    verify_reconstructed_highbits md pk sig.

lemma keygen_internal_valid md sd :
  valid_keypair md (keygen_internal md sd).`1 (keygen_internal md sd).`2.
proof. by rewrite /valid_keypair /keygen_internal. qed.

lemma public_key_of_keygen md sd :
  public_key_of_secret md (keygen_internal md sd).`2 =
  (keygen_internal md sd).`1.
proof. by rewrite /keygen_internal. qed.

lemma public_key_vector_seed_keygen_equation md sd :
  public_key_vector_seed md sd =
  haetae_public_key_vector_from_relation md sd
    (haetae_keygen_secret_vector md sd)
    (haetae_keygen_error_vector md sd).
proof. by rewrite /public_key_vector_seed /haetae_keygen_public_vector. qed.

lemma public_key_vector_seed_mode23_keygen_equation md sd :
  (md = Mode2 \/ md = Mode3) =>
  public_key_vector_seed md sd =
  polyveck_vk_highbits md
    (polyveck_add md
      (public_rounding_vector_seed md sd)
      (polyveck_add md
        (matrix_vec_mul md
          (haetae_keygen_a0_matrix md sd)
          (haetae_keygen_secret_vector md sd))
        (haetae_keygen_error_vector md sd))).
proof.
move=> md23.
rewrite /public_key_vector_seed /haetae_keygen_public_vector
        /haetae_public_key_vector_from_relation
        /haetae_keygen_a0_matrix /haetae_keygen_secret_vector
        /haetae_keygen_error_vector.
by case: md md23 => //=.
qed.

lemma public_key_vector_seed_mode5_keygen_equation sd :
  public_key_vector_seed Mode5 sd =
  polyveck_neg Mode5
    (polyveck_double Mode5
      (polyveck_add Mode5
        (matrix_vec_mul Mode5
          (haetae_keygen_a0_matrix Mode5 sd)
          (haetae_keygen_secret_vector Mode5 sd))
        (haetae_keygen_error_vector Mode5 sd))).
proof.
by rewrite /public_key_vector_seed /haetae_keygen_public_vector
           /haetae_public_key_vector_from_relation
           /haetae_keygen_a0_matrix /haetae_keygen_secret_vector
           /haetae_keygen_error_vector.
qed.

lemma haetae_keygen_raw_public_vector_keygen_equation md sd :
  haetae_keygen_raw_public_vector md sd =
  polyveck_add md
    (matrix_vec_mul md
      (haetae_keygen_a0_matrix md sd)
      (haetae_keygen_secret_vector md sd))
    (haetae_keygen_error_vector md sd).
proof. by rewrite /haetae_keygen_raw_public_vector. qed.

lemma haetae_reference_keygen_raw_public_vector_equation md sd :
  haetae_reference_keygen_raw_public_vector md sd =
  polyveck_add md
    (matrix_vec_mul md
      (haetae_reference_polymatkm_expand_matA md
        (haetae_keygen_rhoprime sd))
      (haetae_reference_keygen_secret_vector md sd))
    (haetae_reference_keygen_error_vector md sd).
proof.
by rewrite /haetae_reference_keygen_raw_public_vector
           /haetae_reference_keygen_a0_matrix.
qed.

lemma haetae_reference_keygen_mode23_public_vector_equation md sd :
  (md = Mode2 \/ md = Mode3) =>
  haetae_reference_keygen_public_vector md sd =
  polyveck_vk_highbits md
    (polyveck_add md
      (haetae_reference_polyveck_expand_vecA md
        (haetae_keygen_rhoprime sd))
      (polyveck_add md
        (matrix_vec_mul md
          (haetae_reference_polymatkm_expand_matA md
            (haetae_keygen_rhoprime sd))
          (haetae_reference_keygen_secret_vector md sd))
        (haetae_reference_keygen_error_vector md sd))).
proof.
move=> md23.
rewrite /haetae_reference_keygen_public_vector
        /haetae_public_key_vector_from_relation
        /haetae_reference_polyveck_expand_vecA
        /haetae_reference_polymatkm_expand_matA.
by case: md md23 => //=.
qed.

lemma haetae_reference_keygen_mode23_adjusted_error_equation md sd :
  (md = Mode2 \/ md = Mode3) =>
  haetae_reference_keygen_mode23_adjusted_error_vector md sd =
  polyveck_sub md
    (haetae_reference_keygen_error_vector md sd)
    (polyveck_vk_lowbits md
      (polyveck_add md
        (haetae_reference_polyveck_expand_vecA md
          (haetae_keygen_rhoprime sd))
        (haetae_reference_keygen_raw_public_vector md sd))).
proof.
move=> _.
by rewrite /haetae_reference_keygen_mode23_adjusted_error_vector
           /haetae_reference_keygen_mode23_rounding_lowbits
           /haetae_reference_keygen_mode23_predecompose_vector.
qed.

lemma haetae_reference_keygen_mode5_public_vector_equation sd :
  haetae_reference_keygen_public_vector Mode5 sd =
  polyveck_neg Mode5
    (polyveck_double Mode5
      (polyveck_add Mode5
        (matrix_vec_mul Mode5
          (haetae_reference_polymatkm_expand_matA Mode5
            (haetae_keygen_rhoprime sd))
          (haetae_reference_keygen_secret_vector Mode5 sd))
        (haetae_reference_keygen_error_vector Mode5 sd))).
proof.
by rewrite /haetae_reference_keygen_public_vector
           /haetae_public_key_vector_from_relation
           /haetae_reference_polymatkm_expand_matA.
qed.

lemma packed_haetae_reference_public_key_seedE md sd :
  (packed_haetae_reference_public_key md sd).`1 =
  haetae_keygen_rhoprime sd.
proof. by rewrite /packed_haetae_reference_public_key. qed.

lemma packed_haetae_reference_public_key_bodyE md sd :
  (packed_haetae_reference_public_key md sd).`2 =
  haetae_reference_keygen_public_vector md sd.
proof. by rewrite /packed_haetae_reference_public_key. qed.

lemma haetae_reference_keygen_seed_flow_wf_ok md sd :
  haetae_reference_keygen_seed_flow_wf md sd.
proof.
by rewrite /haetae_reference_keygen_seed_flow_wf
           /haetae_reference_keygen_a0_matrix
           /haetae_reference_keygen_secret_vector
           /haetae_reference_keygen_error_vector
           /haetae_reference_keygen_public_vector
           /packed_haetae_reference_public_key.
qed.

lemma packed_haetae_public_key_wf md sd :
  polyveck_wf md (packed_haetae_public_key md sd).`2.
proof.
have h := haetae_keygen_public_vector_polyq_wf md sd.
by move: h; rewrite /haetae_polyveck_polyq_coeffs_wf /packed_haetae_public_key.
qed.

lemma packed_haetae_public_key_polyq_wf md sd :
  haetae_polyveck_polyq_coeffs_wf md (packed_haetae_public_key md sd).`2.
proof.
by rewrite /packed_haetae_public_key /=;
   apply haetae_keygen_public_vector_polyq_wf.
qed.

lemma packed_haetae_public_key_unpacked_wf md sd :
  size sd = seedbytes =>
  haetae_public_key_unpacked_wf md (packed_haetae_public_key md sd).
proof.
move=> sd_sz.
by rewrite /haetae_public_key_unpacked_wf /= sd_sz packed_haetae_public_key_wf.
qed.

lemma haetae_keygen_public_key_roundtrip md sd :
  size sd = seedbytes =>
  haetae_keygen_public_key_roundtrip_ok md sd.
proof.
move=> sd_sz.
rewrite /haetae_keygen_public_key_roundtrip_ok.
apply haetae_public_key_roundtrip.
by apply packed_haetae_public_key_unpacked_wf.
qed.

lemma public_key_of_secret_packed md sk :
  public_key_of_secret md sk = packed_haetae_public_key md sk.`1.
proof.
by rewrite /public_key_of_secret /packed_haetae_public_key
           /public_key_vector_seed.
qed.

lemma keygen_public_key_packed md sd :
  (keygen_internal md sd).`1 = packed_haetae_public_key md sd.
proof.
by rewrite /keygen_internal /public_key_of_secret /secret_key_of_seed
           /packed_haetae_public_key /public_key_vector_seed.
qed.

lemma public_verification_matrix_packedE md pk :
  public_verification_matrix md pk = packed_haetae_verification_matrix md pk.
proof. by rewrite /public_verification_matrix. qed.

lemma packed_haetae_keygen_verification_matrixE md sd :
  packed_haetae_keygen_verification_matrix md sd =
  haetae_verification_matrix_from_unpacked md sd
    (haetae_keygen_public_vector md sd).
proof.
by rewrite /packed_haetae_keygen_verification_matrix
           /packed_haetae_verification_matrix
           /packed_haetae_public_key.
qed.

lemma honest_public_verification_matrix_eq_packed_keygen md sd :
  public_verification_matrix md (keygen_internal md sd).`1 =
  packed_haetae_keygen_verification_matrix md sd.
proof.
by rewrite /keygen_internal /public_key_of_secret /secret_key_of_seed
           /public_verification_matrix /packed_haetae_keygen_verification_matrix
           /packed_haetae_verification_matrix /packed_haetae_public_key
           /public_key_vector_seed.
qed.

lemma concrete_keygen_public_verification_matrix_correct md sd :
  size sd = seedbytes =>
  public_verification_matrix md (keygen_internal md sd).`1 =
  concrete_haetae_keygen_verification_matrix md sd.
proof.
move=> sd_sz.
have rt := haetae_keygen_public_key_roundtrip md sd sd_sz.
rewrite honest_public_verification_matrix_eq_packed_keygen.
rewrite /packed_haetae_keygen_verification_matrix
        /concrete_haetae_keygen_verification_matrix
        /concrete_haetae_keygen_unpacked_public_key
        /concrete_haetae_keygen_packed_public_key.
rewrite /haetae_keygen_public_key_roundtrip_ok
        /haetae_public_key_roundtrip_ok in rt.
by rewrite rt.
qed.

lemma concrete_keygen_public_verification_matrix_ref_correct md sd :
  size sd = seedbytes =>
  public_verification_matrix md (keygen_internal md sd).`1 =
  concrete_haetae_keygen_verification_matrix_ref md sd.
proof.
move=> sd_sz.
have rt := haetae_keygen_public_key_ref_roundtrip md sd sd_sz.
rewrite honest_public_verification_matrix_eq_packed_keygen.
rewrite /packed_haetae_keygen_verification_matrix
        /concrete_haetae_keygen_verification_matrix_ref
        /concrete_haetae_keygen_unpacked_public_key_ref
        /concrete_haetae_keygen_packed_public_key_ref
        /haetae_unpack_public_key_bytes_ref
        /haetae_pack_public_key_bytes_ref.
by rewrite rt.
qed.

lemma concrete_reference_keygen_public_verification_matrix_ref_correct md sd :
  packed_haetae_verification_matrix md
    (packed_haetae_reference_public_key md sd) =
  concrete_haetae_reference_keygen_verification_matrix_ref md sd.
proof.
have rt := haetae_reference_keygen_public_key_ref_roundtrip md sd.
rewrite /concrete_haetae_reference_keygen_verification_matrix_ref
        /concrete_haetae_reference_keygen_unpacked_public_key_ref
        /concrete_haetae_reference_keygen_packed_public_key_ref.
by rewrite rt.
qed.

lemma concrete_keygen_public_verification_matrix_size md sd :
  size (concrete_haetae_keygen_verification_matrix md sd) = mode_k md.
proof.
by rewrite /concrete_haetae_keygen_verification_matrix
           /packed_haetae_verification_matrix
           /haetae_verification_matrix_from_unpacked size_mkseq; case md.
qed.

lemma concrete_keygen_public_verification_matrix_ref_size md sd :
  size (concrete_haetae_keygen_verification_matrix_ref md sd) = mode_k md.
proof.
by rewrite /concrete_haetae_keygen_verification_matrix_ref
           /packed_haetae_verification_matrix
           /haetae_verification_matrix_from_unpacked size_mkseq; case md.
qed.

lemma concrete_reference_keygen_public_verification_matrix_ref_size md sd :
  size (concrete_haetae_reference_keygen_verification_matrix_ref md sd) =
  mode_k md.
proof.
by rewrite /concrete_haetae_reference_keygen_verification_matrix_ref
           /packed_haetae_verification_matrix
           /haetae_verification_matrix_from_unpacked size_mkseq; case md.
qed.

lemma concrete_keygen_public_verification_matrix_rows_wf md sd :
  all (polyvecl_wf md) (concrete_haetae_keygen_verification_matrix md sd).
proof.
rewrite /concrete_haetae_keygen_verification_matrix
        /packed_haetae_verification_matrix
        /haetae_verification_matrix_from_unpacked.
apply/allP=> row /mkseqP [i [i_rng ->]].
rewrite /polyvecl_wf size_mkseq.
split.
+ by smt(mode_l_gt0).
apply/allP=> p /mkseqP [j [_ ->]].
case: (j = 0) => j0; rewrite j0 /=.
+ have col_wf :=
    haetae_verification_column_from_unpacked_wf md
      (concrete_haetae_keygen_unpacked_public_key md sd).`1
      (concrete_haetae_keygen_unpacked_public_key md sd).`2.
  smt(polyveck_wf_nth).
by apply poly_double_wf.
qed.

lemma concrete_keygen_public_verification_matrix_ref_rows_wf md sd :
  all (polyvecl_wf md)
    (concrete_haetae_keygen_verification_matrix_ref md sd).
proof.
rewrite /concrete_haetae_keygen_verification_matrix_ref
        /packed_haetae_verification_matrix
        /haetae_verification_matrix_from_unpacked.
apply/allP=> row /mkseqP [i [i_rng ->]].
rewrite /polyvecl_wf size_mkseq.
split.
+ by smt(mode_l_gt0).
apply/allP=> p /mkseqP [j [_ ->]].
case: (j = 0) => j0; rewrite j0 /=.
+ have col_wf :=
    haetae_verification_column_from_unpacked_wf md
      (concrete_haetae_keygen_unpacked_public_key_ref md sd).`1
      (concrete_haetae_keygen_unpacked_public_key_ref md sd).`2.
  smt(polyveck_wf_nth).
by apply poly_double_wf.
qed.

lemma concrete_reference_keygen_public_verification_matrix_ref_rows_wf md sd :
  all (polyvecl_wf md)
    (concrete_haetae_reference_keygen_verification_matrix_ref md sd).
proof.
rewrite /concrete_haetae_reference_keygen_verification_matrix_ref
        /packed_haetae_verification_matrix
        /haetae_verification_matrix_from_unpacked.
apply/allP=> row /mkseqP [i [i_rng ->]].
rewrite /polyvecl_wf size_mkseq.
split.
+ by smt(mode_l_gt0).
apply/allP=> p /mkseqP [j [_ ->]].
case: (j = 0) => j0; rewrite j0 /=.
+ have col_wf :=
    haetae_verification_column_from_unpacked_wf md
      (concrete_haetae_reference_keygen_unpacked_public_key_ref md sd).`1
      (concrete_haetae_reference_keygen_unpacked_public_key_ref md sd).`2.
  smt(polyveck_wf_nth).
by apply poly_double_wf.
qed.

lemma valid_signature_sign_internal md sk m ctx coins :
  valid_signature md (sign_internal md sk m ctx coins).
proof.
rewrite /valid_signature /sign_internal /signature_token /=.
rewrite commitment_highbits_wf commitment_lowbits_wf /crh_wf message_hash_size
        /commitment_challenge challenge_hash_wf response_vector_wf.
by rewrite response_aux_vector_wf hint_vector_wf.
qed.

lemma verify_challenge_consistent_sign_internal md sk m ctx coins :
  verify_challenge_consistent md (public_key_of_secret md sk) m ctx
    (sign_internal md sk m ctx coins).
proof.
by rewrite /verify_challenge_consistent /sign_internal
           /commitment_challenge /challenge_hash /=.
qed.

op coeff_norm_sq (x : coeff) : int = x * x.
op poly_norm_sq (p : poly) : int =
  if poly_unit p then size p
  else if p = poly_zero then 0
  else sumz (map coeff_norm_sq p).
op polyvecl_norm_sq (md : mode) (xs : polyvecl) : int =
  if polyvecl_unit md xs then mode_l md * n
  else if xs = polyvecl_zero md then 0
  else sumz (map poly_norm_sq xs).
op polyveck_norm_sq (md : mode) (xs : polyveck) : int =
  if polyveck_unit md xs then mode_k md * n
  else if xs = polyveck_zero md then 0
  else sumz (map poly_norm_sq xs).
op signature_response_norm_sq (md : mode) (sig : signature) : int =
  polyvecl_norm_sq md (sig_response sig) +
  polyveck_norm_sq md (sig_response_aux sig).
op signature_verify_norm_sq (md : mode) (sig : signature) : int =
  signature_response_norm_sq md sig +
  polyveck_norm_sq md (sig_hint sig).

op secret_norm_sq (sk : skey) : int = sk.`2.
op response_norm_sq (md : mode) (sig : signature) : int =
  signature_response_norm_sq md sig.
op verify_norm_sq (md : mode) (sig : signature) : int =
  signature_verify_norm_sq md sig.

op secret_norm_ok (md : mode) (sk : skey) : bool =
  0 <= secret_norm_sq sk /\ secret_norm_sq sk <= mode_b0sq md.
op response_norm_ok (md : mode) (sig : signature) : bool =
  0 <= response_norm_sq md sig /\ response_norm_sq md sig <= mode_b1sq md.
op verify_norm_ok (md : mode) (sig : signature) : bool =
  0 <= verify_norm_sq md sig /\ verify_norm_sq md sig <= mode_b2sq md.

op verify_internal :
  mode -> pkey -> message -> context -> signature -> bool =
  fun (md : mode) (pk : pkey) (m : message) (ctx : context)
      (sig : signature) =>
    valid_signature md sig /\
    verify_challenge_consistent md pk m ctx sig /\
    verify_public_equation md pk sig /\
    verify_norm_ok md sig.

lemma secret_norm_ok_current md sd :
  secret_norm_ok md (secret_key_of_seed md sd).
proof. by rewrite /secret_norm_ok /secret_norm_sq /secret_key_of_seed; case md. qed.

lemma response_norm_ok_current md sk m ctx coins :
  response_norm_ok md (sign_internal md sk m ctx coins).
proof.
rewrite /response_norm_ok /response_norm_sq /signature_response_norm_sq
        /sign_internal /signature_token /sig_response /sig_response_aux
        /sig_token_value /polyvecl_norm_sq /polyveck_norm_sq
        /response_vector /response_aux_vector.
have hresp :
  polyvecl_unit md
    (deterministic_unit_polyvecl md 17 (response_source sk m ctx coins)).
+ by apply deterministic_unit_polyvecl_unit.
have haux :
  polyveck_unit md
    (deterministic_unit_polyveck md 29 (response_source sk m ctx coins)).
+ by apply deterministic_unit_polyveck_unit.
rewrite hresp haux.
clear hresp haux.
by case md.
qed.

lemma verify_norm_ok_current md sk m ctx coins :
  verify_norm_ok md (sign_internal md sk m ctx coins).
proof.
rewrite /verify_norm_ok /verify_norm_sq /signature_verify_norm_sq
        /signature_response_norm_sq /sign_internal /signature_token
        /sig_response /sig_response_aux /sig_hint /sig_token_value
        /polyvecl_norm_sq /polyveck_norm_sq
        /response_vector /response_aux_vector /hint_vector.
have hresp :
  polyvecl_unit md
    (deterministic_unit_polyvecl md 17 (response_source sk m ctx coins)).
+ by apply deterministic_unit_polyvecl_unit.
have haux :
  polyveck_unit md
    (deterministic_unit_polyveck md 29 (response_source sk m ctx coins)).
+ by apply deterministic_unit_polyveck_unit.
have hhint :
  polyveck_unit md
    (deterministic_unit_polyveck md 41 (response_source sk m ctx coins)).
+ by apply deterministic_unit_polyveck_unit.
rewrite hresp haux hhint.
clear hresp haux hhint.
by case md.
qed.

lemma verify_internal_sign_internal md sk m ctx coins :
  verify_internal md (public_key_of_secret md sk) m ctx
    (sign_internal md sk m ctx coins).
proof.
rewrite /verify_internal.
split.
+ by apply valid_signature_sign_internal.
split.
+ by apply verify_challenge_consistent_sign_internal.
split.
+ rewrite /verify_public_equation /verify_reconstructed_highbits
           /sign_internal /commitment_highbits
           /commitment_challenge /=.
  by rewrite /signature_token /sig_response_aux /sig_token_value.
by apply verify_norm_ok_current.
qed.

end HAETAE_Algebra.
