require import AllCore Binomial Distr FSet List Real StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import VerifyChallengeM23SubsetBinomialPostFreeze
               VerifyChallengeM23UniformFlatSamplerPostFreeze
               VerifyChallengeM23UniformSamplerBridgePostFreeze
               VerifyChallengeM23UniformRoundsPostFreeze
               VerifyChallengeM23XofRandomnessBoundaryPostFreeze
               VerifyActualChallengeAlgebraBridgePostFreeze
               Mode2VerifyPrepareNorm
               HAETAE_Algebra
               HAETAE_Params
               HAETAE_ROM.

theory Mode2ChallengeROMAdapterPostFreeze.

import HAETAE_Params.
import HAETAE_Algebra.
import HAETAE_ROM.

(* Post-freeze ROM adapter for the concrete Mode-2 challenge carrier.  This
   exposes the actual 0/1 weight-58 carrier induced by the 58-round reservoir
   support law without mutating the frozen dchallenge abstraction.  It does
   not replace HAETAE_ROM.dro_output or identify deterministic SHAKE bytes
   with random-oracle bytes. *)

op mode2_challenge_words : int = 256.
op mode2_tau : int = 58.

op valid_mode2_support (s : int fset) : bool =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.valid_subset
    mode2_challenge_words mode2_tau s.

op reservoir_rounds : int -> int fset distr =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.reservoir_rounds.

op support_prefix =
  VerifyChallengeM23UniformSamplerBridgePostFreeze.support_prefix.

op challenge_of_barray =
  VerifyActualChallengeAlgebraBridgePostFreeze.challenge_of_barray.

op mode2_challenge_of_support
    (s : int fset) : challenge =
  mkseq (fun i => if i \in s then 1 else 0) mode2_challenge_words.

op mode2_challenge_support
    (ch : challenge) : int fset =
  FSet.filter
    (fun i => nth 0 ch i = 1)
    (FSet.rangeset 0 mode2_challenge_words).

op valid_mode2_carrier_challenge
    (ch : challenge) : bool =
  exists s,
    valid_mode2_support s /\
    ch = mode2_challenge_of_support s.

op dmode2_carrier_challenge : challenge distr =
  dmap (reservoir_rounds mode2_tau) mode2_challenge_of_support.

(* Mode-2-only fresh ChallengeHashQuery output law.  It deliberately has no
   generic mode argument, so it cannot be used as a drop-in law for other
   parameter sets.  Oracle memoization and programming remain a later game
   adapter. *)
op dmode2_fresh_challenge_query_output : HAETAE_ROM.ro_output distr =
  dmap dmode2_carrier_challenge HAETAE_ROM.ro_output_of_challenge.

lemma reservoir_rounds_support_256_58 s :
  s \in reservoir_rounds 58 <=> valid_mode2_support s.
proof.
rewrite /reservoir_rounds /valid_mode2_support.
exact (VerifyChallengeM23UniformRoundsPostFreeze.reservoir_rounds_final_support s).
qed.

lemma mode2_challenge_of_support_size s :
  size (mode2_challenge_of_support s) = HAETAE_Params.n.
proof.
rewrite /mode2_challenge_of_support /mode2_challenge_words size_mkseq.
by rewrite /HAETAE_Params.n.
qed.

lemma mode2_challenge_of_support_wf s :
  HAETAE_Algebra.challenge_wf (mode2_challenge_of_support s).
proof.
rewrite /HAETAE_Algebra.challenge_wf.
split.
+ rewrite /HAETAE_Algebra.poly_wf mode2_challenge_of_support_size.
   trivial.
+ apply/List.allP => x hx.
   move: hx => /mkseqP [i [hi ->]].
   rewrite /HAETAE_Algebra.challenge_coeff_ok
           /mode2_challenge_of_support /=.
   case (i \in s); smt().
qed.

lemma mode2_challenge_of_support_all_01 s :
  all (fun x => 0 <= x <= 1) (mode2_challenge_of_support s).
proof.
apply/List.allP => x hx.
move: hx => /mkseqP [i [_ ->]].
rewrite /mode2_challenge_of_support /=.
case (i \in s); smt().
qed.

lemma mode2_challenge_support_mem ch i :
  i \in mode2_challenge_support ch <=>
  0 <= i < mode2_challenge_words /\ nth 0 ch i = 1.
proof.
rewrite /mode2_challenge_support FSet.in_filter FSet.mem_rangeset.
smt().
qed.

lemma mode2_challenge_supportK s :
  valid_mode2_support s =>
  mode2_challenge_support (mode2_challenge_of_support s) = s.
proof.
move=> hsvalid.
move: hsvalid => [hsub _].
apply/FSet.fsetP => i.
rewrite mode2_challenge_support_mem.
split.
+ move=> [hi hmem].
   rewrite /mode2_challenge_of_support nth_mkseq 1:hi in hmem.
   case (i \in s).
   + trivial.
   + smt().
+ move=> his.
   have hi : 0 <= i < mode2_challenge_words.
   + move: (hsub i his).
     rewrite FSet.mem_rangeset.
     smt().
   split; first exact hi.
   rewrite /mode2_challenge_of_support nth_mkseq 1:hi.
   smt().
qed.

lemma canonical_challenge_of_barrayE cp :
  Mode2VerifyPrepareNorm.canonical_challenge cp =>
  challenge_of_barray cp =
  mode2_challenge_of_support
    (support_prefix cp mode2_challenge_words).
proof.
move=> hcanonical.
apply/(eq_from_nth 0).
+ rewrite /challenge_of_barray
          VerifyActualChallengeAlgebraBridgePostFreeze.challenge_of_barray_size
          mode2_challenge_of_support_size.
  trivial.
+ move=> i hi.
  have hi' : 0 <= i < mode2_challenge_words.
  + move: hi.
    rewrite /challenge_of_barray
            VerifyActualChallengeAlgebraBridgePostFreeze.challenge_of_barray_size
            /HAETAE_Params.n /mode2_challenge_words.
    trivial.
  rewrite /challenge_of_barray
          (VerifyActualChallengeAlgebraBridgePostFreeze.challenge_of_barray_coeff
             cp i hi')
          /mode2_challenge_of_support nth_mkseq 1:hi'.
  have hcanonical_i := hcanonical i hi'.
  move: hcanonical_i => [hrange _].
  case (BArray1024.get32 cp i = W32.one) => hone.
  + rewrite hone W32.to_uint1 /=.
    smt().
  + rewrite ifF 1:/#.
    have hnotone_uint : W32.to_uint (BArray1024.get32 cp i) <> 1.
    + apply/negP => heq.
      apply hone.
      apply W32.to_uint_eq.
      by rewrite W32.to_uint1 heq.
    smt().
qed.

lemma mode2_challenge_of_support_properties s :
  valid_mode2_support s =>
  HAETAE_Algebra.challenge_wf (mode2_challenge_of_support s) /\
  mode2_challenge_support (mode2_challenge_of_support s) = s /\
  FSet.card (mode2_challenge_support (mode2_challenge_of_support s)) = 58.
proof.
move=> hsvalid.
have hsK := mode2_challenge_supportK s hsvalid.
split.
+ exact (mode2_challenge_of_support_wf s).
split.
+ exact hsK.
move: hsvalid => [_ hcard].
by rewrite hsK hcard.
qed.

lemma dmode2_carrier_challenge_support ch :
  ch \in dmode2_carrier_challenge <=> valid_mode2_carrier_challenge ch.
proof.
rewrite /dmode2_carrier_challenge /valid_mode2_carrier_challenge.
rewrite supp_dmap.
split.
+ move=> [s [hsupp ->]].
   exists s.
   split.
   + by move: hsupp; rewrite reservoir_rounds_support_256_58.
   + trivial.
+ move=> [s [hsvalid ->]].
   exists s.
   split.
   + by rewrite reservoir_rounds_support_256_58.
   + trivial.
qed.

lemma valid_mode2_carrier_challenge_wf ch :
  valid_mode2_carrier_challenge ch =>
  HAETAE_Algebra.challenge_wf ch.
proof.
move=> [s [_ ->]].
exact (mode2_challenge_of_support_wf s).
qed.

lemma valid_mode2_carrier_challenge_all_01 ch :
  valid_mode2_carrier_challenge ch =>
  all (fun x => 0 <= x <= 1) ch.
proof.
move=> [s [_ ->]].
exact (mode2_challenge_of_support_all_01 s).
qed.

lemma valid_mode2_carrier_challenge_support_valid ch :
  valid_mode2_carrier_challenge ch =>
  valid_mode2_support (mode2_challenge_support ch).
proof.
move=> [s [hsvalid ->]].
by rewrite mode2_challenge_supportK 1:hsvalid.
qed.

lemma valid_mode2_carrier_challenge_support_card ch :
  valid_mode2_carrier_challenge ch =>
  FSet.card (mode2_challenge_support ch) = 58.
proof.
move=> [s [hsvalid ->]].
have hsK := mode2_challenge_supportK s hsvalid.
move: hsvalid => [_ hcard].
by rewrite hsK hcard.
qed.

lemma mode2_challenge_of_support_point_256_58 s :
  valid_mode2_support s =>
  mu1 dmode2_carrier_challenge (mode2_challenge_of_support s) =
  1%r / (bin 256 58)%r.
proof.
move=> hsvalid.
rewrite /dmode2_carrier_challenge dmap1E.
have -> :
    mu (reservoir_rounds 58)
       (fun t =>
          mode2_challenge_of_support t = mode2_challenge_of_support s) =
    mu (reservoir_rounds 58) (pred1 s).
+ apply mu_eq_support => t ht /=.
   have htvalid : valid_mode2_support t.
   + by move: ht; rewrite reservoir_rounds_support_256_58.
   apply/eq_iff.
   split.
   + move=> heq.
     have hsupp_eq := congr1 mode2_challenge_support _ _ heq.
     rewrite (mode2_challenge_supportK t htvalid)
             (mode2_challenge_supportK s hsvalid) in hsupp_eq.
     exact hsupp_eq.
   + by move=> ->.
rewrite VerifyChallengeM23SubsetBinomialPostFreeze.reservoir_rounds_final_point_256_58.
rewrite /valid_mode2_support /mode2_challenge_words /mode2_tau in hsvalid.
smt().
qed.

lemma valid_mode2_carrier_challenge_point_256_58 ch :
  valid_mode2_carrier_challenge ch =>
  mu1 dmode2_carrier_challenge ch =
  1%r / (bin 256 58)%r.
proof.
move=> [s [hsvalid ->]].
exact (mode2_challenge_of_support_point_256_58 s hsvalid).
qed.

lemma dmode2_carrier_challenge_point_256_58 ch :
  mu1 dmode2_carrier_challenge ch =
  if valid_mode2_carrier_challenge ch
  then 1%r / (bin 256 58)%r
  else 0%r.
proof.
case (valid_mode2_carrier_challenge ch) => hvalid.
+ exact (valid_mode2_carrier_challenge_point_256_58 ch hvalid).
+ apply/supportPn.
  rewrite dmode2_carrier_challenge_support.
  exact hvalid.
qed.

lemma dmode2_carrier_challenge_lossless :
  is_lossless dmode2_carrier_challenge.
proof.
rewrite /dmode2_carrier_challenge.
apply dmap_ll.
have hnonneg : 0 <= 58 by trivial.
exact (VerifyChallengeM23UniformRoundsPostFreeze.reservoir_rounds_lossless
        58 hnonneg).
qed.

lemma flat_mode2_carrier_challenge_pr &m P :
  Pr[VerifyChallengeM23UniformFlatSamplerPostFreeze.FlatMode2RejectionSampler.sample() @ &m :
       P (mode2_challenge_of_support (support_prefix res.`1 res.`2))] =
  mu dmode2_carrier_challenge P.
proof.
rewrite
  (VerifyChallengeM23UniformFlatSamplerPostFreeze.flat_support_pr
     &m (fun s => P (mode2_challenge_of_support s))).
rewrite /dmode2_carrier_challenge dmapE.
by apply mu_eq => s /=.
qed.

lemma parametric_xof_carrier_challenge_pr &m dbyte P :
  VerifyChallengeM23XofRandomnessBoundaryPostFreeze.xof_byte_distribution_ok
    dbyte =>
  Pr[VerifyChallengeM23XofRandomnessBoundaryPostFreeze.ParametricXofByteSampler.sample(dbyte) @ &m :
       P (mode2_challenge_of_support (support_prefix res.`1 res.`2))] =
  mu dmode2_carrier_challenge P.
proof.
move=> hbyte.
rewrite
  (VerifyChallengeM23XofRandomnessBoundaryPostFreeze.parametric_xof_flat_support_pr
     &m &m dbyte
     (fun s => P (mode2_challenge_of_support s))
     hbyte).
exact (flat_mode2_carrier_challenge_pr &m P).
qed.

lemma dmode2_fresh_challenge_query_output_lossless :
  is_lossless dmode2_fresh_challenge_query_output.
proof.
rewrite /dmode2_fresh_challenge_query_output.
by apply dmap_ll; apply dmode2_carrier_challenge_lossless.
qed.

lemma dmode2_fresh_challenge_query_output_challenge_pr P :
  mu dmode2_fresh_challenge_query_output
     (fun y => P (HAETAE_ROM.ro_challenge_hash y)) =
  mu dmode2_carrier_challenge P.
proof.
rewrite /dmode2_fresh_challenge_query_output
        /HAETAE_ROM.ro_challenge_hash
        /HAETAE_ROM.ro_output_to_challenge
        /HAETAE_ROM.ro_output_of_challenge
        dmapE.
by apply mu_eq => ch /=.
qed.

lemma dmode2_fresh_challenge_query_output_point_256_58 ch :
  mu dmode2_fresh_challenge_query_output
     (fun y => HAETAE_ROM.ro_challenge_hash y = ch) =
  if valid_mode2_carrier_challenge ch
  then 1%r / (bin 256 58)%r
  else 0%r.
proof.
rewrite (dmode2_fresh_challenge_query_output_challenge_pr (pred1 ch)).
exact (dmode2_carrier_challenge_point_256_58 ch).
qed.

end Mode2ChallengeROMAdapterPostFreeze.
