require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import BArray8192.

(* Coefficient indices count signed 32-bit cells, not bytes.  The pure norm
   is an integer; only the implementation's accumulated result is modular. *)
op hyperball_coeff_square (p : BArray8192.t) (i : int) : int =
  let x = W32.to_sint (BArray8192.get32 p i) in x * x.

op hyperball_prefix_sqnorm (p : BArray8192.t) (n : int) : int =
  foldl (fun total i => total + hyperball_coeff_square p i) 0 (iota_ 0 n).

op hyperball_sqnorm (a : BArray8192.t) (na : int)
    (b : BArray8192.t) (nb : int) : int =
  hyperball_prefix_sqnorm a na + hyperball_prefix_sqnorm b nb.

op hyperball_coeff_bound (p : BArray8192.t) (n bound : int) : bool =
  forall i, 0 <= i < n =>
    -bound <= W32.to_sint (BArray8192.get32 p i) <= bound.

lemma hyperball_prefix_sqnorm0 p : hyperball_prefix_sqnorm p 0 = 0.
proof. by rewrite /hyperball_prefix_sqnorm iota0. qed.

lemma hyperball_prefix_sqnormS p n : 0 <= n =>
  hyperball_prefix_sqnorm p (n + 1) =
    hyperball_prefix_sqnorm p n + hyperball_coeff_square p n.
proof.
move=> hn; by rewrite /hyperball_prefix_sqnorm iotaSr 1:hn foldl_rcons.
qed.

lemma hyperball_coeff_square_bounds p i :
  0 <= hyperball_coeff_square p i <= 4611686018427387904.
proof.
have /= hx := W32.to_sint_cmp (BArray8192.get32 p i).
rewrite /hyperball_coeff_square; smt().
qed.

lemma hyperball_prefix_sqnorm_nonnegative p n : 0 <= n =>
  0 <= hyperball_prefix_sqnorm p n.
proof.
move: n; apply intind.
+ by rewrite /= hyperball_prefix_sqnorm0.
move=> n hn ih.
rewrite /= in ih; rewrite /=.
rewrite hyperball_prefix_sqnormS 1:hn.
have h := hyperball_coeff_square_bounds p n; smt().
qed.

lemma hyperball_sqnorm_nonnegative a na b nb :
  0 <= na => 0 <= nb => 0 <= hyperball_sqnorm a na b nb.
proof.
move=> ha hb.
have hna := hyperball_prefix_sqnorm_nonnegative a na ha.
have hnb := hyperball_prefix_sqnorm_nonnegative b nb hb.
rewrite /hyperball_sqnorm; smt().
qed.

lemma hyperball_prefix_sqnorm_bound p n bound :
  0 <= n => 0 <= bound => hyperball_coeff_bound p n bound =>
  hyperball_prefix_sqnorm p n <= n * (bound * bound).
proof.
move: n; apply intind.
+ rewrite /= hyperball_prefix_sqnorm0; smt().
move=> n hn ih.
rewrite /= in ih; rewrite /=.
move=> hb hcoeff.
have hprev : hyperball_coeff_bound p n bound by
  move=> i hi; apply hcoeff; smt().
have hs := ih hb hprev.
have hx := hcoeff n _; first smt().
rewrite hyperball_prefix_sqnormS 1:hn /hyperball_coeff_square.
smt().
qed.

lemma hyperball_sqnorm_bound a na b nb bound :
  0 <= na => 0 <= nb => 0 <= bound =>
  hyperball_coeff_bound a na bound => hyperball_coeff_bound b nb bound =>
  hyperball_sqnorm a na b nb <= (na + nb) * (bound * bound).
proof.
move=> ha hb hbound hca hcb.
have hna := hyperball_prefix_sqnorm_bound a na bound ha hbound hca.
have hnb := hyperball_prefix_sqnorm_bound b nb bound hb hbound hcb.
rewrite /hyperball_sqnorm; smt().
qed.

lemma hyperball_sqnorm_26bit_no_overflow a na b nb :
  0 <= na => 0 <= nb => na + nb <= 2816 =>
  hyperball_coeff_bound a na 67108864 => hyperball_coeff_bound b nb 67108864 =>
  0 <= hyperball_sqnorm a na b nb < W64.modulus.
proof.
move=> ha hb hcount hca hcb.
have hzero := hyperball_sqnorm_nonnegative a na b nb ha hb.
have hmax := hyperball_sqnorm_bound a na b nb 67108864 ha hb _ hca hcb;
  first trivial.
rewrite /=; smt().
qed.

lemma hyperball_norm_word_le a na b nb (bound : W64.t) :
  (W64.of_int (hyperball_sqnorm a na b nb) \ule bound) =
    (hyperball_sqnorm a na b nb %% W64.modulus <= W64.to_uint bound).
proof. by rewrite W64.uleE W64.of_uintK. qed.

lemma hyperball_norm_word_le_exact a na b nb (bound : W64.t) :
  0 <= na => 0 <= nb => hyperball_sqnorm a na b nb < W64.modulus =>
  (W64.of_int (hyperball_sqnorm a na b nb) \ule bound) =
    (hyperball_sqnorm a na b nb <= W64.to_uint bound).
proof.
move=> ha hb hfit.
have hzero := hyperball_sqnorm_nonnegative a na b nb ha hb.
have hsmall : 0 <= hyperball_sqnorm a na b nb < `|W64.modulus|.
+ rewrite /=; rewrite /= in hfit; by split.
by rewrite hyperball_norm_word_le (modz_small _ _ hsmall).
qed.

lemma hyperball_norm_word_le_26bit a na b nb (bound : W64.t) :
  0 <= na => 0 <= nb => na + nb <= 2816 =>
  hyperball_coeff_bound a na 67108864 => hyperball_coeff_bound b nb 67108864 =>
  (W64.of_int (hyperball_sqnorm a na b nb) \ule bound) =
    (hyperball_sqnorm a na b nb <= W64.to_uint bound).
proof.
move=> ha hb hn hca hcb.
have [_ hfit] := hyperball_sqnorm_26bit_no_overflow a na b nb ha hb hn hca hcb.
exact (hyperball_norm_word_le_exact a na b nb bound ha hb hfit).
qed.
