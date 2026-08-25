require import AllCore Binomial Distr FMap List PROM Real StdOrder.

require import Mode2ChallengeROMAdapterPostFreeze
               HAETAE_Algebra
               HAETAE_Params
               HAETAE_ROM.

theory Mode2ChallengeGatedROMPostFreeze.

import HAETAE_Algebra.
import HAETAE_Params.
import HAETAE_ROM.
import Mode2ChallengeROMAdapterPostFreeze.

(* This is the post-freeze lazy-ROM adapter that only swaps the fresh output
   law for Mode-2 challenge queries.  All other queries keep the frozen
   HAETAE_ROM.dro_output semantics verbatim.  It intentionally stops at the
   memoizing FullRO surface; counted/programmed ROM integrations remain later. *)

op is_mode2_challenge_query (q : HAETAE_ROM.ro_query) : bool =
  with q = MessageHashQuery _ => false
  with q = ChallengeHashQuery x => x.`1 = Mode2
  with q = MatrixExpandQuery _ => false
  with q = SamplerExpandQuery _ => false.

op dro_output (q : HAETAE_ROM.ro_query) : HAETAE_ROM.ro_output distr =
  if is_mode2_challenge_query q
  then dmode2_fresh_challenge_query_output
  else HAETAE_ROM.dro_output q.

lemma is_mode2_challenge_queryE md w1 w0 muh :
  is_mode2_challenge_query
    (HAETAE_ROM.challenge_hash_query md w1 w0 muh) =
  (md = Mode2).
proof.
rewrite /is_mode2_challenge_query /HAETAE_ROM.challenge_hash_query /=.
trivial.
qed.

lemma is_mode2_challenge_query_message pk ctx m :
  ! is_mode2_challenge_query (HAETAE_ROM.message_hash_query pk ctx m).
proof.
rewrite /is_mode2_challenge_query /HAETAE_ROM.message_hash_query /=.
trivial.
qed.

lemma is_mode2_challenge_query_matrix md sd :
  ! is_mode2_challenge_query (HAETAE_ROM.matrix_expand_query md sd).
proof.
rewrite /is_mode2_challenge_query /HAETAE_ROM.matrix_expand_query /=.
trivial.
qed.

lemma is_mode2_challenge_query_sampler coins :
  ! is_mode2_challenge_query (HAETAE_ROM.sampler_expand_query coins).
proof.
rewrite /is_mode2_challenge_query /HAETAE_ROM.sampler_expand_query /=.
trivial.
qed.

lemma gated_dro_output_mode2E w1 w0 muh :
  dro_output (HAETAE_ROM.challenge_hash_query Mode2 w1 w0 muh) =
  dmode2_fresh_challenge_query_output.
proof.
rewrite /dro_output is_mode2_challenge_queryE.
trivial.
qed.

lemma gated_dro_output_nonmode2E md w1 w0 muh :
  md <> Mode2 =>
  dro_output (HAETAE_ROM.challenge_hash_query md w1 w0 muh) =
  HAETAE_ROM.dro_output
    (HAETAE_ROM.challenge_hash_query md w1 w0 muh).
proof.
move=> hmd.
rewrite /dro_output is_mode2_challenge_queryE.
by rewrite hmd.
qed.

lemma gated_dro_output_messageE pk ctx m :
  dro_output (HAETAE_ROM.message_hash_query pk ctx m) =
  HAETAE_ROM.dro_output (HAETAE_ROM.message_hash_query pk ctx m).
proof.
rewrite /dro_output is_mode2_challenge_query_message.
trivial.
qed.

lemma gated_dro_output_matrixE md sd :
  dro_output (HAETAE_ROM.matrix_expand_query md sd) =
  HAETAE_ROM.dro_output (HAETAE_ROM.matrix_expand_query md sd).
proof.
rewrite /dro_output is_mode2_challenge_query_matrix.
trivial.
qed.

lemma gated_dro_output_samplerE coins :
  dro_output (HAETAE_ROM.sampler_expand_query coins) =
  HAETAE_ROM.dro_output (HAETAE_ROM.sampler_expand_query coins).
proof.
rewrite /dro_output is_mode2_challenge_query_sampler.
trivial.
qed.

lemma gated_dro_output_fallback q :
  ! is_mode2_challenge_query q =>
  dro_output q = HAETAE_ROM.dro_output q.
proof.
move=> hq.
rewrite /dro_output hq.
trivial.
qed.

lemma gated_dro_output_lossless q :
  is_lossless (dro_output q).
proof.
rewrite /dro_output.
case: (is_mode2_challenge_query q) => hq /=.
+ exact dmode2_fresh_challenge_query_output_lossless.
+ exact (HAETAE_ROM.ro_output_distribution_lossless q).
qed.

lemma gated_dro_output_mode2_challenge_pr
    w1 w0 muh (P : challenge -> bool) :
  mu (dro_output (HAETAE_ROM.challenge_hash_query Mode2 w1 w0 muh))
     (fun y => P (HAETAE_ROM.ro_challenge_hash y)) =
  mu dmode2_carrier_challenge P.
proof.
rewrite gated_dro_output_mode2E.
exact (dmode2_fresh_challenge_query_output_challenge_pr P).
qed.

lemma gated_dro_output_mode2_point_256_58 w1 w0 muh ch :
  mu (dro_output (HAETAE_ROM.challenge_hash_query Mode2 w1 w0 muh))
     (fun y => HAETAE_ROM.ro_challenge_hash y = ch) =
  if valid_mode2_carrier_challenge ch
  then 1%r / (bin 256 58)%r
  else 0%r.
proof.
rewrite gated_dro_output_mode2E.
exact (dmode2_fresh_challenge_query_output_point_256_58 ch).
qed.

clone import FullRO as Mode2ChallengeGatedRO with
  type in_t <- HAETAE_ROM.ro_query,
  type out_t <- HAETAE_ROM.ro_output,
  op dout <- dro_output.

module type Mode2Oracle = {
  include FRO [init, get, set, rem, sample, queried, allKnown]
}.

module type Mode2POracle = {
  include FRO [get, set, rem, sample, queried, allKnown]
}.

lemma mode2_gated_rom_get_lossless :
  phoare[Mode2ChallengeGatedRO.FRO.get : true ==> true] = 1%r.
proof.
proc.
wp.
rnd.
by auto => />; smt(gated_dro_output_lossless).
qed.

lemma mode2_gated_rom_fresh_get_sets_known q m0 :
  hoare[Mode2ChallengeGatedRO.FRO.get :
    arg = q /\
    Mode2ChallengeGatedRO.FRO.m = m0 /\
    m0.[q] = None ==>
    Mode2ChallengeGatedRO.FRO.m = m0.[q <- (res, Known)] /\
    Mode2ChallengeGatedRO.FRO.m.[q] = Some (res, Known)].
proof.
proc.
wp.
rnd.
by auto => />; smt(get_set_sameE domE).
qed.

lemma mode2_gated_rom_mode2_fresh_get_eq
    w1 w0 muh (P : HAETAE_ROM.ro_output -> bool) :
  phoare[Mode2ChallengeGatedRO.FRO.get :
    arg = HAETAE_ROM.challenge_hash_query Mode2 w1 w0 muh /\
    HAETAE_ROM.challenge_hash_query Mode2 w1 w0 muh
      \notin Mode2ChallengeGatedRO.FRO.m
    ==> P res] =
  (mu dmode2_fresh_challenge_query_output P).
proof.
proc.
wp.
rnd.
auto => /> &hr _.
qed.

lemma mode2_gated_rom_mode2_fresh_get_challenge_eq
    w1 w0 muh (P : challenge -> bool) :
  phoare[Mode2ChallengeGatedRO.FRO.get :
    arg = HAETAE_ROM.challenge_hash_query Mode2 w1 w0 muh /\
    HAETAE_ROM.challenge_hash_query Mode2 w1 w0 muh
      \notin Mode2ChallengeGatedRO.FRO.m
    ==> P (HAETAE_ROM.ro_challenge_hash res)] =
  (mu dmode2_carrier_challenge P).
proof.
proc.
wp.
rnd.
auto => /> &hr _.
by rewrite gated_dro_output_mode2E
           dmode2_fresh_challenge_query_output_challenge_pr.
qed.

lemma mode2_gated_rom_mode2_fresh_get_point_256_58 w1 w0 muh ch :
  phoare[Mode2ChallengeGatedRO.FRO.get :
    arg = HAETAE_ROM.challenge_hash_query Mode2 w1 w0 muh /\
    HAETAE_ROM.challenge_hash_query Mode2 w1 w0 muh
      \notin Mode2ChallengeGatedRO.FRO.m
    ==> HAETAE_ROM.ro_challenge_hash res = ch] =
  (if valid_mode2_carrier_challenge ch
   then 1%r / (bin 256 58)%r
   else 0%r).
proof.
proc.
wp.
rnd.
auto => /> &hr _.
by rewrite gated_dro_output_mode2E
           dmode2_fresh_challenge_query_output_point_256_58.
qed.

lemma mode2_gated_rom_set_programs q y m0 :
  hoare[Mode2ChallengeGatedRO.FRO.set :
    arg = (q, y) /\
    Mode2ChallengeGatedRO.FRO.m = m0 ==>
    Mode2ChallengeGatedRO.FRO.m = m0.[q <- (y, Known)] /\
    Mode2ChallengeGatedRO.FRO.m.[q] = Some (y, Known)].
proof.
proc.
auto => />.
by rewrite get_set_sameE.
qed.

(* FullRO.FRO.get performs a dummy draw before inspecting its map, even on a
   cache hit.  This theorem states the sound observable memoization property:
   the stored value is returned and promoted to Known; it does not claim that
   the discarded draw is absent. *)
lemma mode2_gated_rom_memoized_get_returns_cached q y f m0 :
  hoare[Mode2ChallengeGatedRO.FRO.get :
    arg = q /\
    Mode2ChallengeGatedRO.FRO.m = m0 /\
    m0.[q] = Some (y, f) ==>
    res = y /\
    Mode2ChallengeGatedRO.FRO.m = m0.[q <- (y, Known)] /\
    Mode2ChallengeGatedRO.FRO.m.[q] = Some (y, Known)].
proof.
proc.
wp.
rnd.
by auto => />; smt(get_set_sameE domE).
qed.

end Mode2ChallengeGatedROMPostFreeze.
