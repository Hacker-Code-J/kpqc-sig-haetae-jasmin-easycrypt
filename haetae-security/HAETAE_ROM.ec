require import AllCore Distr List PROM.
require import HAETAE_Params HAETAE_Algebra HAETAE_Distributions.

theory HAETAE_ROM.

import HAETAE_Algebra.
import HAETAE_Distributions.
import HAETAE_Params.

type ro_query =
  [ MessageHashQuery of (pkey * context * message)
  | ChallengeHashQuery of (mode * polyveck * poly * crh)
  | MatrixExpandQuery of (mode * seed)
  | SamplerExpandQuery of random_coins ].
type ro_output = crh * challenge * matrix * random_coins.

op message_hash_query (pk : pkey) (ctx : context) (m : message) : ro_query =
  MessageHashQuery (pk, ctx, m).
op challenge_hash_query
   (md : mode) (w1 : polyveck) (w0 : poly) (mu : crh) : ro_query =
  ChallengeHashQuery (md, w1, w0, mu).
op matrix_expand_query (md : mode) (sd : seed) : ro_query =
  MatrixExpandQuery (md, sd).
op sampler_expand_query (coins : random_coins) : ro_query =
  SamplerExpandQuery coins.

op ro_crh_zero : crh = nseq crhbytes 0.
op ro_challenge_zero : challenge = poly_zero.
op ro_matrix_zero : matrix = [].
op ro_random_coins_zero : random_coins = nseq seedbytes 0.
op ro_output_zero : ro_output =
  (ro_crh_zero, ro_challenge_zero, ro_matrix_zero, ro_random_coins_zero).

op ro_output_to_crh (y : ro_output) : crh = y.`1.
op ro_output_to_challenge (y : ro_output) : challenge = y.`2.
op ro_output_to_matrix (y : ro_output) : matrix = y.`3.
op ro_output_to_random_coins (y : ro_output) : random_coins = y.`4.

op ro_output_of_crh (mu : crh) : ro_output =
  (mu, ro_challenge_zero, ro_matrix_zero, ro_random_coins_zero).
op ro_output_of_challenge (ch : challenge) : ro_output =
  (ro_crh_zero, ch, ro_matrix_zero, ro_random_coins_zero).
op ro_output_of_matrix (a : matrix) : ro_output =
  (ro_crh_zero, ro_challenge_zero, a, ro_random_coins_zero).
op ro_output_of_random_coins (coins : random_coins) : ro_output =
  (ro_crh_zero, ro_challenge_zero, ro_matrix_zero, coins).

op dmatrix_for_query (x : mode * seed) : matrix distr = dmatrix x.`1.

op dro_output (q : ro_query) : ro_output distr =
  with q = MessageHashQuery _ => dmap dcrh ro_output_of_crh
  with q = ChallengeHashQuery x =>
    dmap (dchallenge x.`1) ro_output_of_challenge
  with q = MatrixExpandQuery x =>
    dmap (dmatrix_for_query x) ro_output_of_matrix
  with q = SamplerExpandQuery _ =>
    dmap drandom_coins ro_output_of_random_coins.

lemma matrix_query_distribution_lossless x :
  is_lossless (dmatrix_for_query x).
proof.
rewrite /dmatrix_for_query.
case x => md sd /=.
by apply matrix_distribution_lossless.
qed.

lemma ro_output_distribution_lossless q :
  is_lossless (dro_output q).
proof.
rewrite /dro_output.
case q => /=.
+ by apply dmap_ll; apply crh_distribution_lossless.
+ move=> x.
  by apply dmap_ll; apply challenge_distribution_lossless.
+ move=> x.
  by apply dmap_ll; apply matrix_query_distribution_lossless.
+ by apply dmap_ll; apply signing_coin_distribution_lossless.
qed.

clone import FullRO as HAETAE_RO with
  type in_t <- ro_query,
  type out_t <- ro_output,
  op dout <- dro_output.

module type Oracle = {
  include FRO [init, get, set, rem, sample, queried, allKnown]
}.

module type POracle = {
  include FRO [get, set, rem, sample, queried, allKnown]
}.

op ro_message_hash (y : ro_output) : crh = ro_output_to_crh y.
op ro_challenge_hash (y : ro_output) : challenge = ro_output_to_challenge y.
op ro_matrix (y : ro_output) : matrix = ro_output_to_matrix y.
op ro_signing_coins (y : ro_output) : random_coins =
  ro_output_to_random_coins y.

lemma sampler_expand_query_dro_output_ro_signing_coins
    seed_coins (p : random_coins -> bool) :
  mu (dro_output (sampler_expand_query seed_coins))
     (fun y => p (ro_signing_coins y)) =
  mu drandom_coins p.
proof.
rewrite /dro_output /sampler_expand_query /ro_signing_coins
        /ro_output_to_random_coins /ro_output_of_random_coins /=.
rewrite dmapE.
by apply mu_eq => coins; rewrite /(\o) /=.
qed.

end HAETAE_ROM.
