require import AllCore Distr DInterval DList IntDiv List Real StdOrder.
require import HAETAE_Params HAETAE_Algebra.

theory HAETAE_Distributions.

import HAETAE_Algebra.
import HAETAE_Params.
import RealOrder.

type signing_randomness_source = int.

op dbyte : byte distr = dinter 0 255.
op dseed : seed distr = dlist dbyte seedbytes.
op dcrh : crh distr = dlist dbyte crhbytes.
op signing_entropy_token_cardinality : int = 288230376151711744.
op signing_entropy_token_in_range (x : int) : bool =
  0 <= x /\ x < signing_entropy_token_cardinality.
op signing_randomness_byte_ok (b : byte) : bool = 0 <= b /\ b < 256.
op signing_entropy_token_to_coins (x : int) : random_coins =
  [ x %% 256;
    (x %/ 256) %% 256;
    (x %/ 65536) %% 256;
    (x %/ 16777216) %% 256;
    (x %/ 4294967296) %% 256;
    (x %/ 1099511627776) %% 256;
    (x %/ 281474976710656) %% 256;
    x %/ 72057594037927936 ] ++
  nseq (seedbytes - 8) 0.
op signing_randomness_domain (coins : random_coins) : bool =
  size coins = seedbytes /\
  all signing_randomness_byte_ok coins /\
  signing_entropy_token_in_range (signing_entropy_token_of_coins coins).
op dsigning_entropy_token : int distr =
  dinter 0 (signing_entropy_token_cardinality - 1).
op dsigning_randomness_source : signing_randomness_source distr =
  dsigning_entropy_token.
op signing_randomness_source_valid (src : signing_randomness_source) : bool =
  signing_entropy_token_in_range src.
op signing_randomness_from_source (src : signing_randomness_source) :
  random_coins =
  signing_entropy_token_to_coins src.
op dsigning_randomness : random_coins distr =
  dmap dsigning_randomness_source signing_randomness_from_source.
op drandom_coins : random_coins distr = dsigning_randomness.
op signing_randomness_point_bound : real =
  1%r / (signing_entropy_token_cardinality)%r.
op signing_randomness_token_spread (d : random_coins distr) : bool =
  forall token,
    mu d (fun coins => signing_entropy_token_of_coins coins = token) <=
    signing_randomness_point_bound.
op signing_randomness_distribution_ok (d : random_coins distr) : bool =
  is_lossless d /\
  (forall coins, coins \in d => signing_randomness_domain coins) /\
  signing_randomness_token_spread d.
op dcoeff : coeff distr = dinter 0 (q - 1).
op dpoly : poly distr = dlist dcoeff n.
op dpolyveck (md : mode) : polyveck distr = dlist dpoly (mode_k md).
op dpolyvecl (md : mode) : polyvecl distr = dlist dpoly (mode_l md).
op dmatrix (md : mode) : matrix distr = dlist (dpolyvecl md) (mode_k md).

(* This is the structural prefix-sparse challenge carrier distribution over a
   byte-list seed. It is checked against the local challenge-shape predicate,
   but still needs a paper-faithful sampler/correspondence proof before claiming
   equality with the HAETAE specification distribution. *)
op dchallenge (md : mode) : challenge distr =
  dmap dcrh (challenge_from_seed md).

type signing_sample_pair = polyvecl * polyveck.

op signing_sample_pair_y1 (s : signing_sample_pair) : polyvecl = s.`1.
op signing_sample_pair_y2 (s : signing_sample_pair) : polyveck = s.`2.

op signing_sample_pair_wf (md : mode) (s : signing_sample_pair) : bool =
  polyvecl_wf md (signing_sample_pair_y1 s) /\
  polyveck_wf md (signing_sample_pair_y2 s).

op signing_sample_pair_unit (md : mode) (s : signing_sample_pair) : bool =
  polyvecl_unit md (signing_sample_pair_y1 s) /\
  polyveck_unit md (signing_sample_pair_y2 s).

op signing_sample_bound (md : mode) : int = mode_ln md.

op coeff_bounded_by (b : int) (x : coeff) : bool =
  -b <= x /\ x <= b.

op poly_bounded_by (b : int) (p : poly) : bool =
  poly_wf p /\
  forall i, 0 <= i < n =>
    coeff_bounded_by b (poly_coeff p i).

op polyvecl_bounded_by (md : mode) (b : int) (xs : polyvecl) : bool =
  polyvecl_wf md xs /\
  forall row, 0 <= row < mode_l md =>
    poly_bounded_by b (nth poly_zero xs row).

op polyveck_bounded_by (md : mode) (b : int) (xs : polyveck) : bool =
  polyveck_wf md xs /\
  forall row, 0 <= row < mode_k md =>
    poly_bounded_by b (nth poly_zero xs row).

op signing_sample_pair_bounded (md : mode) (s : signing_sample_pair) : bool =
  polyvecl_bounded_by md (signing_sample_bound md)
    (signing_sample_pair_y1 s) /\
  polyveck_bounded_by md (signing_sample_bound md)
    (signing_sample_pair_y2 s).

op signing_sample_pair_sample_ok (md : mode) (s : signing_sample_pair) : bool =
  signing_sample_pair_wf md s /\
  signing_sample_pair_bounded md s.

op signing_sample_pair_of_coins
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) : signing_sample_pair =
  (signing_sample_y1 md sk m ctx coins,
   signing_sample_y2 md sk m ctx coins).

op dstructural_signing_sample_pair
   (md : mode) (sk : skey) (m : message) (ctx : context)
   (coins : random_coins) : signing_sample_pair distr =
  dunit (signing_sample_pair_of_coins md sk m ctx coins).

op dsigning_unit_coeff : coeff distr = duniform [-1; 1].
op dsigning_unit_poly : poly distr = dlist dsigning_unit_coeff n.
op dsigning_unit_polyvecl (md : mode) : polyvecl distr =
  dlist dsigning_unit_poly (mode_l md).
op dsigning_unit_polyveck (md : mode) : polyveck distr =
  dlist dsigning_unit_poly (mode_k md).

op signing_bounded_coeff_cardinality (md : mode) : int =
  2 * signing_sample_bound md + 1.
op signing_bounded_coeff_point_bound (md : mode) : real =
  1%r / (signing_bounded_coeff_cardinality md)%r.
op dsigning_bounded_coeff (md : mode) : coeff distr =
  dinter (-(signing_sample_bound md)) (signing_sample_bound md).
op dsigning_bounded_poly (md : mode) : poly distr =
  dlist (dsigning_bounded_coeff md) n.
op dsigning_bounded_polyvecl (md : mode) : polyvecl distr =
  dlist (dsigning_bounded_poly md) (mode_l md).
op dsigning_bounded_polyveck (md : mode) : polyveck distr =
  dlist (dsigning_bounded_poly md) (mode_k md).

(* Entropy-bearing checked signing-sample source. This is the first
   non-deterministic sampler instance for the attempt-state boundary; the
   paper's hyperball sampler still has to replace this bounded-unit source. *)
op dbounded_unit_signing_sample_pair (md : mode) :
   signing_sample_pair distr =
  dlet (dsigning_unit_polyvecl md)
    (fun y1 =>
      dmap (dsigning_unit_polyveck md)
        (fun y2 => (y1, y2))).

(* Paper-shaped bounded carrier for the future HAETAE hyperball sampler. This
   checks dimensions, coefficient bounds, and point-bound facts for a product
   bounded source; it still has to be replaced by the exact hyperball/sphere
   sampler and rejection loop correspondence. *)
op dchecked_hyperball_signing_sample_pair (md : mode) :
   signing_sample_pair distr =
  dlet (dsigning_bounded_polyvecl md)
    (fun y1 =>
      dmap (dsigning_bounded_polyveck md)
        (fun y2 => (y1, y2))).

op hyperball_coeff_ok (md : mode) (c : coeff) : bool =
  coeff_bounded_by (signing_sample_bound md) c.
op hyperball_poly_ok (md : mode) (p : poly) : bool =
  poly_bounded_by (signing_sample_bound md) p.
op hyperball_polyvecl_ok (md : mode) (y1 : polyvecl) : bool =
  polyvecl_bounded_by md (signing_sample_bound md) y1.
op hyperball_polyveck_ok (md : mode) (y2 : polyveck) : bool =
  polyveck_bounded_by md (signing_sample_bound md) y2.
op hyperball_sample_ok (md : mode) (s : signing_sample_pair) : bool =
  hyperball_polyvecl_ok md (signing_sample_pair_y1 s) /\
  hyperball_polyveck_ok md (signing_sample_pair_y2 s).

op dhyperball_coeff (md : mode) : coeff distr =
  dsigning_bounded_coeff md.
op dhyperball_poly (md : mode) : poly distr =
  dsigning_bounded_poly md.
op dhyperball_polyvecl (md : mode) : polyvecl distr =
  dsigning_bounded_polyvecl md.
op dhyperball_polyveck (md : mode) : polyveck distr =
  dsigning_bounded_polyveck md.

op hyperball_coeff_point_bound (md : mode) : real =
  signing_bounded_coeff_point_bound md.
op hyperball_poly_point_bound (md : mode) : real =
  hyperball_coeff_point_bound md ^ n.
op hyperball_polyvecl_point_bound (md : mode) : real =
  hyperball_poly_point_bound md ^ (mode_l md).
op hyperball_polyveck_point_bound (md : mode) : real =
  hyperball_poly_point_bound md ^ (mode_k md).
op hyperball_sample_pair_point_bound (md : mode) : real =
  hyperball_polyvecl_point_bound md *
  hyperball_polyveck_point_bound md.

(* Exact sampler interface for the next HAETAE replacement step. The current
   compiled implementation is the checked bounded carrier above, presented as a
   product sampler so point-probability bounds can be exposed explicitly. The
   paper-faithful sphere/hyperball law still has to replace the component
   distributions behind this interface. *)
op dexact_hyperball_signing_sample_pair (md : mode) :
   signing_sample_pair distr =
  (dhyperball_polyvecl md) `*` (dhyperball_polyveck md).

op signing_sample_pair_distribution_ok
   (md : mode) (d : signing_sample_pair distr) : bool =
  is_lossless d /\
  (forall s, s \in d =>
     signing_sample_pair_sample_ok md s).

lemma byte_distribution_lossless : is_lossless dbyte.
proof. by rewrite /dbyte; apply dinter_ll. qed.

lemma seed_distribution_lossless : is_lossless dseed.
proof.
rewrite /dseed.
by apply dlist_ll; apply byte_distribution_lossless.
qed.

lemma crh_distribution_lossless : is_lossless dcrh.
proof.
rewrite /dcrh.
by apply dlist_ll; apply byte_distribution_lossless.
qed.

lemma signing_entropy_token_cardinality_positive :
  0 < signing_entropy_token_cardinality.
proof. by rewrite /signing_entropy_token_cardinality. qed.

lemma signing_entropy_token_distribution_lossless :
  is_lossless dsigning_entropy_token.
proof.
rewrite /dsigning_entropy_token.
apply dinter_ll.
by rewrite /signing_entropy_token_cardinality.
qed.

lemma signing_randomness_source_distribution_lossless :
  is_lossless dsigning_randomness_source.
proof.
by rewrite /dsigning_randomness_source;
   apply signing_entropy_token_distribution_lossless.
qed.

lemma signing_coin_distribution_lossless : is_lossless drandom_coins.
proof.
rewrite /drandom_coins /dsigning_randomness.
by apply dmap_ll; apply signing_randomness_source_distribution_lossless.
qed.

lemma signing_entropy_token_to_coins_tokenK x :
  signing_entropy_token_of_coins (signing_entropy_token_to_coins x) = x.
proof.
rewrite /signing_entropy_token_of_coins
        /signing_entropy_token_to_coins.
rewrite /=.
smt(divz_eq divz_mul).
qed.

lemma signing_randomness_from_source_tokenK src :
  signing_entropy_token_of_coins (signing_randomness_from_source src) = src.
proof.
by rewrite /signing_randomness_from_source
           signing_entropy_token_to_coins_tokenK.
qed.

lemma signing_entropy_token_to_coins_size x :
  size (signing_entropy_token_to_coins x) = seedbytes.
proof.
rewrite /signing_entropy_token_to_coins /seedbytes.
have hsize : size (nseq (32 - 8) 0) = max (32 - 8) 0 by
  exact size_nseq.
change (8 + size (nseq (32 - 8) 0) = 32).
rewrite hsize.
rewrite /max.
trivial.
qed.

lemma signing_entropy_token_to_coins_byte_domain x :
  signing_entropy_token_in_range x =>
  all signing_randomness_byte_ok (signing_entropy_token_to_coins x).
proof.
rewrite /signing_entropy_token_in_range
        /signing_entropy_token_cardinality
        /signing_entropy_token_to_coins
        /signing_randomness_byte_ok /=.
move=> xrange.
rewrite /seedbytes /=.
smt(modz_ge0 ltz_pmod divz_ge0 ltz_divLR all_nseq).
qed.

lemma signing_entropy_token_to_coins_domain x :
  signing_entropy_token_in_range x =>
  signing_randomness_domain (signing_entropy_token_to_coins x).
proof.
move=> xrange.
rewrite /signing_randomness_domain signing_entropy_token_to_coins_size
        (signing_entropy_token_to_coins_tokenK x).
split=> //.
split.
+ by apply signing_entropy_token_to_coins_byte_domain.
by apply xrange.
qed.

lemma signing_randomness_from_source_domain src :
  signing_randomness_source_valid src =>
  signing_randomness_domain (signing_randomness_from_source src).
proof.
by rewrite /signing_randomness_source_valid
           /signing_randomness_from_source;
   apply signing_entropy_token_to_coins_domain.
qed.

lemma signing_entropy_token_distribution_point_bound x :
  mu dsigning_entropy_token (pred1 x) <=
  signing_randomness_point_bound.
proof.
rewrite /signing_randomness_point_bound.
rewrite /dsigning_entropy_token dinter1E /pred1
        /signing_entropy_token_cardinality.
case: (0 <= x <= 288230376151711744 - 1).
+ by move=> _; rewrite RField.div1r.
by move=> _; apply divr_ge0; [trivial | trivial].
qed.

lemma signing_randomness_source_distribution_point_bound src :
  mu dsigning_randomness_source (pred1 src) <=
  signing_randomness_point_bound.
proof.
by rewrite /dsigning_randomness_source;
   apply signing_entropy_token_distribution_point_bound.
qed.

lemma signing_coin_distribution_token_point_bound token :
  mu drandom_coins
    (fun coins => signing_entropy_token_of_coins coins = token) <=
  signing_randomness_point_bound.
proof.
rewrite /drandom_coins /dsigning_randomness dmapE.
apply (ler_trans (mu dsigning_entropy_token (pred1 token))).
+ apply mu_le => x _ token_eq.
  rewrite /pred1 /=.
  rewrite -token_eq.
  by rewrite (signing_entropy_token_to_coins_tokenK x).
by apply signing_entropy_token_distribution_point_bound.
qed.

lemma signing_coin_distribution_token_spread :
  signing_randomness_token_spread drandom_coins.
proof.
rewrite /signing_randomness_token_spread.
by apply signing_coin_distribution_token_point_bound.
qed.

lemma signing_coin_distribution_domain coins :
  coins \in drandom_coins =>
  signing_randomness_domain coins.
proof.
rewrite /drandom_coins /dsigning_randomness
        /dsigning_randomness_source /signing_randomness_from_source.
rewrite supp_dmap.
move=> [src [src_supp ->]].
apply signing_entropy_token_to_coins_domain.
move: src_supp.
rewrite /dsigning_entropy_token supp_dinter
        /signing_entropy_token_in_range
        /signing_entropy_token_cardinality.
smt.
qed.

lemma signing_coin_distribution_domain_full :
  mu drandom_coins signing_randomness_domain = 1%r.
proof.
apply eq1_mu.
+ by apply signing_coin_distribution_lossless.
by apply signing_coin_distribution_domain.
qed.

lemma signing_coin_distribution_ok :
  signing_randomness_distribution_ok drandom_coins.
proof.
rewrite /signing_randomness_distribution_ok.
split.
+ by apply signing_coin_distribution_lossless.
split.
+ by apply signing_coin_distribution_domain.
by apply signing_coin_distribution_token_spread.
qed.

lemma coeff_distribution_lossless : is_lossless dcoeff.
proof. by rewrite /dcoeff; apply dinter_ll. qed.

lemma poly_distribution_lossless : is_lossless dpoly.
proof.
rewrite /dpoly.
by apply dlist_ll; apply coeff_distribution_lossless.
qed.

lemma polyveck_distribution_lossless md : is_lossless (dpolyveck md).
proof.
rewrite /dpolyveck.
by apply dlist_ll; apply poly_distribution_lossless.
qed.

lemma polyvecl_distribution_lossless md : is_lossless (dpolyvecl md).
proof.
rewrite /dpolyvecl.
by apply dlist_ll; apply poly_distribution_lossless.
qed.

lemma matrix_distribution_lossless md : is_lossless (dmatrix md).
proof.
rewrite /dmatrix.
by apply dlist_ll; apply polyvecl_distribution_lossless.
qed.

lemma challenge_distribution_lossless md : is_lossless (dchallenge md).
proof.
rewrite /dchallenge.
by apply dmap_ll; apply crh_distribution_lossless.
qed.

lemma signing_sample_pair_of_coins_wf md sk m ctx coins :
  signing_sample_pair_wf md
    (signing_sample_pair_of_coins md sk m ctx coins).
proof.
rewrite /signing_sample_pair_wf /signing_sample_pair_of_coins
        /signing_sample_pair_y1 /signing_sample_pair_y2 /=.
split.
+ by apply signing_sample_y1_wf.
by apply signing_sample_y2_wf.
qed.

lemma signing_sample_pair_of_coins_unit md sk m ctx coins :
  signing_sample_pair_unit md
    (signing_sample_pair_of_coins md sk m ctx coins).
proof.
rewrite /signing_sample_pair_unit /signing_sample_pair_of_coins
        /signing_sample_pair_y1 /signing_sample_pair_y2 /=.
split.
+ by apply signing_sample_y1_unit.
by apply signing_sample_y2_unit.
qed.

lemma signing_sample_bound_gt0 md :
  0 < signing_sample_bound md.
proof. by rewrite /signing_sample_bound; apply mode_ln_gt0. qed.

lemma unit_coeff_bounded_by_signing_sample_bound md c :
  unit_coeff_ok c =>
  coeff_bounded_by (signing_sample_bound md) c.
proof.
rewrite /unit_coeff_ok /coeff_bounded_by /signing_sample_bound.
by case md; smt().
qed.

lemma poly_unit_bounded_by_signing_sample_bound md p :
  poly_unit p =>
  poly_bounded_by (signing_sample_bound md) p.
proof.
rewrite /poly_unit /poly_bounded_by => -[p_wf p_all].
split=> // i i_rng.
move: p_all; rewrite allP => p_all.
apply unit_coeff_bounded_by_signing_sample_bound.
apply p_all.
rewrite /poly_coeff.
by apply mem_nth; smt().
qed.

lemma polyvecl_unit_bounded_by_signing_sample_bound md y1 :
  polyvecl_unit md y1 =>
  polyvecl_bounded_by md (signing_sample_bound md) y1.
proof.
rewrite /polyvecl_unit /polyvecl_bounded_by => -[y1_wf y1_all].
split=> // row row_rng.
move: y1_all; rewrite allP => y1_all.
apply poly_unit_bounded_by_signing_sample_bound.
apply y1_all.
by apply mem_nth; smt().
qed.

lemma polyveck_unit_bounded_by_signing_sample_bound md y2 :
  polyveck_unit md y2 =>
  polyveck_bounded_by md (signing_sample_bound md) y2.
proof.
rewrite /polyveck_unit /polyveck_bounded_by => -[y2_wf y2_all].
split=> // row row_rng.
move: y2_all; rewrite allP => y2_all.
apply poly_unit_bounded_by_signing_sample_bound.
apply y2_all.
by apply mem_nth; smt().
qed.

lemma signing_sample_pair_unit_bounded md s :
  signing_sample_pair_unit md s =>
  signing_sample_pair_bounded md s.
proof.
rewrite /signing_sample_pair_unit /signing_sample_pair_bounded.
move=> [y1_unit y2_unit].
split.
+ by apply polyvecl_unit_bounded_by_signing_sample_bound.
by apply polyveck_unit_bounded_by_signing_sample_bound.
qed.

lemma signing_sample_pair_of_coins_sample_ok md sk m ctx coins :
  signing_sample_pair_sample_ok md
    (signing_sample_pair_of_coins md sk m ctx coins).
proof.
rewrite /signing_sample_pair_sample_ok.
split.
+ by apply signing_sample_pair_of_coins_wf.
apply signing_sample_pair_unit_bounded.
by apply signing_sample_pair_of_coins_unit.
qed.

lemma structural_signing_sample_pair_lossless md sk m ctx coins :
  is_lossless
    (dstructural_signing_sample_pair md sk m ctx coins).
proof.
by rewrite /dstructural_signing_sample_pair; apply dunit_ll.
qed.

lemma structural_signing_sample_pair_support md sk m ctx coins s :
  s \in dstructural_signing_sample_pair md sk m ctx coins =>
  signing_sample_pair_wf md s /\ signing_sample_pair_unit md s.
proof.
rewrite /dstructural_signing_sample_pair supp_dunit.
move=> ->.
split.
+ by apply signing_sample_pair_of_coins_wf.
by apply signing_sample_pair_of_coins_unit.
qed.

lemma structural_signing_sample_pair_sample_ok md sk m ctx coins s :
  s \in dstructural_signing_sample_pair md sk m ctx coins =>
  signing_sample_pair_sample_ok md s.
proof.
rewrite /dstructural_signing_sample_pair supp_dunit.
move=> ->.
by apply signing_sample_pair_of_coins_sample_ok.
qed.

lemma structural_signing_sample_pair_distribution_ok md sk m ctx coins :
  signing_sample_pair_distribution_ok md
    (dstructural_signing_sample_pair md sk m ctx coins).
proof.
rewrite /signing_sample_pair_distribution_ok.
split.
+ by apply structural_signing_sample_pair_lossless.
by move=> s; apply structural_signing_sample_pair_sample_ok.
qed.

lemma signing_unit_coeff_lossless :
  is_lossless dsigning_unit_coeff.
proof.
rewrite /dsigning_unit_coeff.
by apply duniform_ll.
qed.

lemma signing_unit_coeff_support c :
  c \in dsigning_unit_coeff =>
  unit_coeff_ok c.
proof.
rewrite /dsigning_unit_coeff supp_duniform /= /unit_coeff_ok.
by smt().
qed.

lemma signing_bounded_coeff_cardinality_positive md :
  0 < signing_bounded_coeff_cardinality md.
proof.
rewrite /signing_bounded_coeff_cardinality.
by smt(signing_sample_bound_gt0).
qed.

lemma signing_bounded_coeff_lossless md :
  is_lossless (dsigning_bounded_coeff md).
proof.
rewrite /dsigning_bounded_coeff.
apply dinter_ll.
by smt(signing_sample_bound_gt0).
qed.

lemma signing_bounded_coeff_support md c :
  c \in dsigning_bounded_coeff md =>
  coeff_bounded_by (signing_sample_bound md) c.
proof.
by rewrite /dsigning_bounded_coeff supp_dinter /coeff_bounded_by.
qed.

lemma signing_bounded_coeff_supportP md c :
  c \in dsigning_bounded_coeff md <=>
  coeff_bounded_by (signing_sample_bound md) c.
proof.
by rewrite /dsigning_bounded_coeff supp_dinter /coeff_bounded_by.
qed.

lemma signing_bounded_coeff_point_bound md c :
  mu (dsigning_bounded_coeff md) (pred1 c) <=
  signing_bounded_coeff_point_bound md.
proof.
rewrite /dsigning_bounded_coeff /signing_bounded_coeff_point_bound
        /signing_bounded_coeff_cardinality /signing_sample_bound
        dinter1E /pred1.
case md; rewrite /mode_ln /=.
+ case: (-8192 <= c <= 8192) => _.
  + by trivial.
  by smt().
+ case: (-8192 <= c <= 8192) => _.
  + by trivial.
  by smt().
case: (-8192 <= c <= 8192) => _.
+ by trivial.
by smt().
qed.

lemma signing_bounded_coeff_point_bound_nonnegative md :
  0%r <= signing_bounded_coeff_point_bound md.
proof.
rewrite /signing_bounded_coeff_point_bound.
apply divr_ge0.
+ by trivial.
by smt(signing_bounded_coeff_cardinality_positive).
qed.

lemma dlist_size_point_bound ['a] (d : 'a distr) bd xs :
  0%r <= bd =>
  (forall x, mu d (pred1 x) <= bd) =>
  mu (dlist d (size xs)) (pred1 xs) <= bd ^ (size xs).
proof.
move=> bd_ge0 point_bound.
rewrite dlist1E 1:size_ge0 /=.
elim xs=> [|x xs ih].
+ by rewrite StdBigop.Bigreal.BRM.big_nil /= RField.expr0.
rewrite StdBigop.Bigreal.BRM.big_cons /predT /=.
rewrite (_ : 1 + size xs = size xs + 1) 1:/#.
rewrite RField.exprS 1:size_ge0.
apply ler_pmul.
+ by apply ge0_mu.
+ apply (StdBigop.Bigreal.BRM.big_ind (fun z => 0%r <= z)).
  + by move=> a b; apply mulr_ge0.
  + by trivial.
  by move=> z _; apply ge0_mu.
+ by apply point_bound.
by apply ih.
qed.

lemma dlist_point_bound ['a] (d : 'a distr) len bd xs :
  0 <= len =>
  0%r <= bd =>
  (forall x, mu d (pred1 x) <= bd) =>
  mu (dlist d len) (pred1 xs) <= bd ^ len.
proof.
move=> len_ge0 bd_ge0 point_bound.
case: (len = size xs) => lenE.
+ rewrite lenE.
  by apply dlist_size_point_bound.
rewrite dlist1E // lenE.
by apply expr_ge0.
qed.

lemma hyperball_coeff_point_bound_nonnegative md :
  0%r <= hyperball_coeff_point_bound md.
proof.
by rewrite /hyperball_coeff_point_bound;
   apply signing_bounded_coeff_point_bound_nonnegative.
qed.

lemma hyperball_coeff_point_boundE md c :
  mu (dhyperball_coeff md) (pred1 c) <=
  hyperball_coeff_point_bound md.
proof.
by rewrite /dhyperball_coeff /hyperball_coeff_point_bound;
   apply signing_bounded_coeff_point_bound.
qed.

lemma signing_unit_poly_lossless :
  is_lossless dsigning_unit_poly.
proof.
rewrite /dsigning_unit_poly.
by apply dlist_ll; apply signing_unit_coeff_lossless.
qed.

lemma signing_unit_poly_support p :
  p \in dsigning_unit_poly =>
  poly_unit p.
proof.
rewrite /dsigning_unit_poly supp_dlist; first by smt(n_gt0).
move=> [p_sz p_all].
rewrite /poly_unit /poly_wf p_sz /=.
apply/allP => c c_mem.
move: p_all; rewrite allP => p_all.
by apply signing_unit_coeff_support; apply p_all.
qed.

lemma signing_bounded_poly_lossless md :
  is_lossless (dsigning_bounded_poly md).
proof.
rewrite /dsigning_bounded_poly.
by apply dlist_ll; apply signing_bounded_coeff_lossless.
qed.

lemma signing_bounded_poly_support md p :
  p \in dsigning_bounded_poly md =>
  poly_bounded_by (signing_sample_bound md) p.
proof.
rewrite /dsigning_bounded_poly supp_dlist; first by smt(n_gt0).
move=> [p_sz p_all].
rewrite /poly_bounded_by /poly_wf p_sz /=.
move: p_all; rewrite allP => p_all.
move=> i i_rng.
apply signing_bounded_coeff_support.
apply p_all.
rewrite /poly_coeff.
by apply mem_nth; smt().
qed.

lemma signing_bounded_poly_supportP md p :
  p \in dsigning_bounded_poly md <=>
  poly_bounded_by (signing_sample_bound md) p.
proof.
rewrite /dsigning_bounded_poly supp_dlist; first by smt(n_gt0).
rewrite /poly_bounded_by /poly_wf.
split.
+ move=> [p_sz p_all]; split=> //.
  move: p_all; rewrite allP => p_all.
  move=> i i_rng.
  apply signing_bounded_coeff_support.
  apply p_all.
  rewrite /poly_coeff.
  by apply mem_nth; smt().
move=> [p_sz p_bound].
split=> //.
rewrite allP => c c_mem.
rewrite signing_bounded_coeff_supportP.
by smt(nthP).
qed.

lemma hyperball_poly_point_bound_nonnegative md :
  0%r <= hyperball_poly_point_bound md.
proof.
rewrite /hyperball_poly_point_bound.
by apply expr_ge0; apply hyperball_coeff_point_bound_nonnegative.
qed.

lemma hyperball_poly_lossless md :
  is_lossless (dhyperball_poly md).
proof.
by rewrite /dhyperball_poly; apply signing_bounded_poly_lossless.
qed.

lemma hyperball_poly_support md p :
  p \in dhyperball_poly md =>
  hyperball_poly_ok md p.
proof.
by rewrite /dhyperball_poly /hyperball_poly_ok;
   apply signing_bounded_poly_support.
qed.

lemma hyperball_poly_supportP md p :
  p \in dhyperball_poly md <=> hyperball_poly_ok md p.
proof.
by rewrite /dhyperball_poly /hyperball_poly_ok
           signing_bounded_poly_supportP.
qed.

lemma hyperball_poly_point_boundE md p :
  mu (dhyperball_poly md) (pred1 p) <=
  hyperball_poly_point_bound md.
proof.
rewrite /dhyperball_poly /dsigning_bounded_poly
        /hyperball_poly_point_bound.
apply dlist_point_bound.
+ by smt(n_gt0).
+ by apply hyperball_coeff_point_bound_nonnegative.
by move=> c; apply hyperball_coeff_point_boundE.
qed.

lemma signing_unit_polyvecl_lossless md :
  is_lossless (dsigning_unit_polyvecl md).
proof.
rewrite /dsigning_unit_polyvecl.
by apply dlist_ll; apply signing_unit_poly_lossless.
qed.

lemma signing_unit_polyveck_lossless md :
  is_lossless (dsigning_unit_polyveck md).
proof.
rewrite /dsigning_unit_polyveck.
by apply dlist_ll; apply signing_unit_poly_lossless.
qed.

lemma signing_bounded_polyvecl_lossless md :
  is_lossless (dsigning_bounded_polyvecl md).
proof.
rewrite /dsigning_bounded_polyvecl.
by apply dlist_ll; apply signing_bounded_poly_lossless.
qed.

lemma signing_bounded_polyveck_lossless md :
  is_lossless (dsigning_bounded_polyveck md).
proof.
rewrite /dsigning_bounded_polyveck.
by apply dlist_ll; apply signing_bounded_poly_lossless.
qed.

lemma signing_unit_polyvecl_support md y1 :
  y1 \in dsigning_unit_polyvecl md =>
  polyvecl_unit md y1.
proof.
rewrite /dsigning_unit_polyvecl supp_dlist; first by smt(mode_l_gt0).
move=> [y1_sz y1_all].
rewrite /polyvecl_unit /polyvecl_wf.
split.
+ split=> //.
  apply/allP => p p_mem.
  move: y1_all; rewrite allP => y1_all.
  have p_supp : p \in dsigning_unit_poly by apply y1_all.
  move: (signing_unit_poly_support p p_supp).
  by rewrite /poly_unit => -[p_wf _].
apply/allP => p p_mem.
move: y1_all; rewrite allP => y1_all.
by apply signing_unit_poly_support; apply y1_all.
qed.

lemma signing_unit_polyveck_support md y2 :
  y2 \in dsigning_unit_polyveck md =>
  polyveck_unit md y2.
proof.
rewrite /dsigning_unit_polyveck supp_dlist; first by smt(mode_k_gt0).
move=> [y2_sz y2_all].
rewrite /polyveck_unit /polyveck_wf.
split.
+ split=> //.
  apply/allP => p p_mem.
  move: y2_all; rewrite allP => y2_all.
  have p_supp : p \in dsigning_unit_poly by apply y2_all.
  move: (signing_unit_poly_support p p_supp).
  by rewrite /poly_unit => -[p_wf _].
apply/allP => p p_mem.
move: y2_all; rewrite allP => y2_all.
by apply signing_unit_poly_support; apply y2_all.
qed.

lemma signing_bounded_polyvecl_support md y1 :
  y1 \in dsigning_bounded_polyvecl md =>
  polyvecl_bounded_by md (signing_sample_bound md) y1.
proof.
rewrite /dsigning_bounded_polyvecl supp_dlist; first by smt(mode_l_gt0).
move=> [y1_sz y1_all].
rewrite /polyvecl_bounded_by /polyvecl_wf.
split.
+ split=> //.
  apply/allP => p p_mem.
  move: y1_all; rewrite allP => y1_all.
  have p_supp : p \in dsigning_bounded_poly md by apply y1_all.
  move: (signing_bounded_poly_support md p p_supp).
  by rewrite /poly_bounded_by => -[p_wf _].
move=> row row_rng.
move: y1_all; rewrite allP => y1_all.
apply signing_bounded_poly_support.
apply y1_all.
by apply mem_nth; smt().
qed.

lemma signing_bounded_polyvecl_supportP md y1 :
  y1 \in dsigning_bounded_polyvecl md <=>
  polyvecl_bounded_by md (signing_sample_bound md) y1.
proof.
rewrite /dsigning_bounded_polyvecl supp_dlist; first by smt(mode_l_gt0).
rewrite /polyvecl_bounded_by /polyvecl_wf.
split.
+ move=> [y1_sz y1_all].
  split.
  + split=> //.
    rewrite allP => p p_mem.
    move: y1_all; rewrite allP => y1_all.
    have p_supp : p \in dsigning_bounded_poly md by apply y1_all.
    move: (signing_bounded_poly_support md p p_supp).
    by rewrite /poly_bounded_by => -[p_wf _].
  move=> row row_rng.
  move: y1_all; rewrite allP => y1_all.
  apply signing_bounded_poly_support.
  apply y1_all.
  by apply mem_nth; smt().
move=> [[y1_sz y1_allwf] y1_bound].
split=> //.
rewrite allP => p p_mem.
rewrite signing_bounded_poly_supportP.
by smt(nthP).
qed.

lemma signing_bounded_polyveck_support md y2 :
  y2 \in dsigning_bounded_polyveck md =>
  polyveck_bounded_by md (signing_sample_bound md) y2.
proof.
rewrite /dsigning_bounded_polyveck supp_dlist; first by smt(mode_k_gt0).
move=> [y2_sz y2_all].
rewrite /polyveck_bounded_by /polyveck_wf.
split.
+ split=> //.
  apply/allP => p p_mem.
  move: y2_all; rewrite allP => y2_all.
  have p_supp : p \in dsigning_bounded_poly md by apply y2_all.
  move: (signing_bounded_poly_support md p p_supp).
  by rewrite /poly_bounded_by => -[p_wf _].
move=> row row_rng.
move: y2_all; rewrite allP => y2_all.
apply signing_bounded_poly_support.
apply y2_all.
by apply mem_nth; smt().
qed.

lemma signing_bounded_polyveck_supportP md y2 :
  y2 \in dsigning_bounded_polyveck md <=>
  polyveck_bounded_by md (signing_sample_bound md) y2.
proof.
rewrite /dsigning_bounded_polyveck supp_dlist; first by smt(mode_k_gt0).
rewrite /polyveck_bounded_by /polyveck_wf.
split.
+ move=> [y2_sz y2_all].
  split.
  + split=> //.
    rewrite allP => p p_mem.
    move: y2_all; rewrite allP => y2_all.
    have p_supp : p \in dsigning_bounded_poly md by apply y2_all.
    move: (signing_bounded_poly_support md p p_supp).
    by rewrite /poly_bounded_by => -[p_wf _].
  move=> row row_rng.
  move: y2_all; rewrite allP => y2_all.
  apply signing_bounded_poly_support.
  apply y2_all.
  by apply mem_nth; smt().
move=> [[y2_sz y2_allwf] y2_bound].
split=> //.
rewrite allP => p p_mem.
rewrite signing_bounded_poly_supportP.
by smt(nthP).
qed.

lemma hyperball_polyvecl_point_bound_nonnegative md :
  0%r <= hyperball_polyvecl_point_bound md.
proof.
rewrite /hyperball_polyvecl_point_bound.
by apply expr_ge0; apply hyperball_poly_point_bound_nonnegative.
qed.

lemma hyperball_polyveck_point_bound_nonnegative md :
  0%r <= hyperball_polyveck_point_bound md.
proof.
rewrite /hyperball_polyveck_point_bound.
by apply expr_ge0; apply hyperball_poly_point_bound_nonnegative.
qed.

lemma hyperball_sample_pair_point_bound_nonnegative md :
  0%r <= hyperball_sample_pair_point_bound md.
proof.
rewrite /hyperball_sample_pair_point_bound.
by apply mulr_ge0;
   [apply hyperball_polyvecl_point_bound_nonnegative
   | apply hyperball_polyveck_point_bound_nonnegative].
qed.

lemma hyperball_polyvecl_lossless md :
  is_lossless (dhyperball_polyvecl md).
proof.
by rewrite /dhyperball_polyvecl; apply signing_bounded_polyvecl_lossless.
qed.

lemma hyperball_polyveck_lossless md :
  is_lossless (dhyperball_polyveck md).
proof.
by rewrite /dhyperball_polyveck; apply signing_bounded_polyveck_lossless.
qed.

lemma hyperball_polyvecl_support md y1 :
  y1 \in dhyperball_polyvecl md =>
  hyperball_polyvecl_ok md y1.
proof.
by rewrite /dhyperball_polyvecl /hyperball_polyvecl_ok;
   apply signing_bounded_polyvecl_support.
qed.

lemma hyperball_polyvecl_supportP md y1 :
  y1 \in dhyperball_polyvecl md <=> hyperball_polyvecl_ok md y1.
proof.
by rewrite /dhyperball_polyvecl /hyperball_polyvecl_ok
           signing_bounded_polyvecl_supportP.
qed.

lemma hyperball_polyveck_support md y2 :
  y2 \in dhyperball_polyveck md =>
  hyperball_polyveck_ok md y2.
proof.
by rewrite /dhyperball_polyveck /hyperball_polyveck_ok;
   apply signing_bounded_polyveck_support.
qed.

lemma hyperball_polyveck_supportP md y2 :
  y2 \in dhyperball_polyveck md <=> hyperball_polyveck_ok md y2.
proof.
by rewrite /dhyperball_polyveck /hyperball_polyveck_ok
           signing_bounded_polyveck_supportP.
qed.

lemma hyperball_polyvecl_point_boundE md y1 :
  mu (dhyperball_polyvecl md) (pred1 y1) <=
  hyperball_polyvecl_point_bound md.
proof.
rewrite /dhyperball_polyvecl /dsigning_bounded_polyvecl
        /hyperball_polyvecl_point_bound.
apply dlist_point_bound.
+ by smt(mode_l_gt0).
+ by apply hyperball_poly_point_bound_nonnegative.
by move=> p; apply hyperball_poly_point_boundE.
qed.

lemma hyperball_polyveck_point_boundE md y2 :
  mu (dhyperball_polyveck md) (pred1 y2) <=
  hyperball_polyveck_point_bound md.
proof.
rewrite /dhyperball_polyveck /dsigning_bounded_polyveck
        /hyperball_polyveck_point_bound.
apply dlist_point_bound.
+ by smt(mode_k_gt0).
+ by apply hyperball_poly_point_bound_nonnegative.
by move=> p; apply hyperball_poly_point_boundE.
qed.

lemma bounded_unit_signing_sample_pair_lossless md :
  is_lossless (dbounded_unit_signing_sample_pair md).
proof.
rewrite /dbounded_unit_signing_sample_pair.
apply dlet_ll.
+ by apply signing_unit_polyvecl_lossless.
move=> y1 _.
by apply dmap_ll; apply signing_unit_polyveck_lossless.
qed.

lemma bounded_unit_signing_sample_pair_support md s :
  s \in dbounded_unit_signing_sample_pair md =>
  signing_sample_pair_wf md s /\ signing_sample_pair_unit md s.
proof.
rewrite /dbounded_unit_signing_sample_pair supp_dlet.
move=> [y1 [y1_supp]].
rewrite supp_dmap.
move=> [y2 [y2_supp ->]].
have y1_unit : polyvecl_unit md y1
  by apply signing_unit_polyvecl_support.
have y2_unit : polyveck_unit md y2
  by apply signing_unit_polyveck_support.
rewrite /signing_sample_pair_wf /signing_sample_pair_unit
        /signing_sample_pair_y1 /signing_sample_pair_y2 /=.
split.
+ split.
  + by move: y1_unit; rewrite /polyvecl_unit => -[h _].
  by move: y2_unit; rewrite /polyveck_unit => -[h _].
by split.
qed.

lemma bounded_unit_signing_sample_pair_sample_ok md s :
  s \in dbounded_unit_signing_sample_pair md =>
  signing_sample_pair_sample_ok md s.
proof.
move=> hs.
move: (bounded_unit_signing_sample_pair_support md s hs)
  => [s_wf s_unit].
rewrite /signing_sample_pair_sample_ok.
split=> //.
by apply signing_sample_pair_unit_bounded.
qed.

lemma bounded_unit_signing_sample_pair_distribution_ok md :
  signing_sample_pair_distribution_ok md
    (dbounded_unit_signing_sample_pair md).
proof.
rewrite /signing_sample_pair_distribution_ok.
split.
+ by apply bounded_unit_signing_sample_pair_lossless.
by move=> s; apply bounded_unit_signing_sample_pair_sample_ok.
qed.

lemma checked_hyperball_signing_sample_pair_lossless md :
  is_lossless (dchecked_hyperball_signing_sample_pair md).
proof.
rewrite /dchecked_hyperball_signing_sample_pair.
apply dlet_ll.
+ by apply signing_bounded_polyvecl_lossless.
move=> y1 _.
by apply dmap_ll; apply signing_bounded_polyveck_lossless.
qed.

lemma checked_hyperball_signing_sample_pair_support md s :
  s \in dchecked_hyperball_signing_sample_pair md =>
  signing_sample_pair_sample_ok md s.
proof.
rewrite /dchecked_hyperball_signing_sample_pair supp_dlet.
move=> [y1 [y1_supp]].
rewrite supp_dmap.
move=> [y2 [y2_supp ->]].
have y1_bounded : polyvecl_bounded_by md (signing_sample_bound md) y1
  by apply signing_bounded_polyvecl_support.
have y2_bounded : polyveck_bounded_by md (signing_sample_bound md) y2
  by apply signing_bounded_polyveck_support.
rewrite /signing_sample_pair_sample_ok /signing_sample_pair_wf
        /signing_sample_pair_bounded
        /signing_sample_pair_y1 /signing_sample_pair_y2 /=.
split.
+ split.
  + by move: y1_bounded; rewrite /polyvecl_bounded_by => -[h _].
  by move: y2_bounded; rewrite /polyveck_bounded_by => -[h _].
by split.
qed.

lemma checked_hyperball_signing_sample_pair_distribution_ok md :
  signing_sample_pair_distribution_ok md
    (dchecked_hyperball_signing_sample_pair md).
proof.
rewrite /signing_sample_pair_distribution_ok.
split.
+ by apply checked_hyperball_signing_sample_pair_lossless.
by move=> s; apply checked_hyperball_signing_sample_pair_support.
qed.

lemma hyperball_sample_ok_sample_ok md s :
  hyperball_sample_ok md s =>
  signing_sample_pair_sample_ok md s.
proof.
rewrite /hyperball_sample_ok /signing_sample_pair_sample_ok
        /signing_sample_pair_wf /signing_sample_pair_bounded
        /hyperball_polyvecl_ok /hyperball_polyveck_ok.
move=> [y1_ok y2_ok].
split.
+ split.
  + by move: y1_ok; rewrite /polyvecl_bounded_by => -[h _].
  by move: y2_ok; rewrite /polyveck_bounded_by => -[h _].
by split.
qed.

lemma exact_hyperball_signing_sample_pair_lossless md :
  is_lossless (dexact_hyperball_signing_sample_pair md).
proof.
rewrite /dexact_hyperball_signing_sample_pair.
rewrite dprod_ll.
split.
+ by apply hyperball_polyvecl_lossless.
by apply hyperball_polyveck_lossless.
qed.

lemma exact_hyperball_signing_sample_pair_support md s :
  s \in dexact_hyperball_signing_sample_pair md =>
  hyperball_sample_ok md s.
proof.
case: s => y1 y2.
rewrite /dexact_hyperball_signing_sample_pair supp_dprod /=.
move=> [y1_supp y2_supp].
rewrite /hyperball_sample_ok /signing_sample_pair_y1
        /signing_sample_pair_y2 /=.
split.
+ by apply hyperball_polyvecl_support.
by apply hyperball_polyveck_support.
qed.

lemma exact_hyperball_signing_sample_pair_supportP md s :
  s \in dexact_hyperball_signing_sample_pair md <=>
  hyperball_sample_ok md s.
proof.
case: s => y1 y2.
rewrite /dexact_hyperball_signing_sample_pair supp_dprod /hyperball_sample_ok
        /signing_sample_pair_y1 /signing_sample_pair_y2 /=.
by rewrite hyperball_polyvecl_supportP hyperball_polyveck_supportP.
qed.

lemma exact_hyperball_signing_sample_pair_sample_ok md s :
  s \in dexact_hyperball_signing_sample_pair md =>
  signing_sample_pair_sample_ok md s.
proof.
move=> hs.
apply hyperball_sample_ok_sample_ok.
by apply exact_hyperball_signing_sample_pair_support.
qed.

lemma exact_hyperball_signing_sample_pair_distribution_ok md :
  signing_sample_pair_distribution_ok md
    (dexact_hyperball_signing_sample_pair md).
proof.
rewrite /signing_sample_pair_distribution_ok.
split.
+ by apply exact_hyperball_signing_sample_pair_lossless.
by move=> s; apply exact_hyperball_signing_sample_pair_sample_ok.
qed.

lemma exact_hyperball_signing_sample_pair_point_bound md s :
  mu (dexact_hyperball_signing_sample_pair md) (pred1 s) <=
  hyperball_sample_pair_point_bound md.
proof.
case: s => y1 y2.
rewrite /dexact_hyperball_signing_sample_pair
        /hyperball_sample_pair_point_bound dprod1E /=.
apply ler_pmul.
+ by apply ge0_mu.
+ by apply ge0_mu.
+ by apply hyperball_polyvecl_point_boundE.
by apply hyperball_polyveck_point_boundE.
qed.

lemma exact_hyperball_signing_sample_pair_checkedE md :
  dexact_hyperball_signing_sample_pair md =
  dchecked_hyperball_signing_sample_pair md.
proof.
rewrite /dexact_hyperball_signing_sample_pair
        /dchecked_hyperball_signing_sample_pair
        /dhyperball_polyvecl /dhyperball_polyveck.
rewrite dprod_dlet.
apply eq_dlet => // y1.
by rewrite /dmap /(\o).
qed.

end HAETAE_Distributions.
