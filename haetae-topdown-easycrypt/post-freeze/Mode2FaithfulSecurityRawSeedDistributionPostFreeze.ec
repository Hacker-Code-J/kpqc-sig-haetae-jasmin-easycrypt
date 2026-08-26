require import AllCore Distr DInterval DList List.

from Jasmin require import JModel_x86.

require import BArray32.
require import HAETAE_Params HAETAE_Algebra HAETAE_Distributions.
require import KeygenSeedXofSpec.
require import Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.

theory Mode2FaithfulSecurityRawSeedDistributionPostFreeze.

import HAETAE_Params.
import HAETAE_Algebra.
import HAETAE_Distributions.

(* This file only relates the security-side seed distribution [dseed] to one
   explicit raw [BArray32.t] encoding and the already-fixed
   [raw_security_seed] bridge.  It does not lift the result to checked
   sources, retry loops, full key generation, or any public-key law. *)

op raw_seed_of_security_seed (sd : seed) : BArray32.t =
  BArray32.init (fun i => W8.of_int (nth 0 sd i)).

op draw_raw_seed : BArray32.t distr =
  dmap dseed raw_seed_of_security_seed.

lemma raw_security_seed_roundtrip sd :
  sd \in dseed =>
  Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed
    (raw_seed_of_security_seed sd) = sd.
proof.
move=> hsd.
have [hsize hbytes] :
    size sd = seedbytes /\ all (support dbyte) sd.
+ move: hsd.
  rewrite /dseed supp_dlist 1:/#.
  trivial.
apply/(eq_from_nth 0).
+ rewrite
    Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed_size
    hsize.
  trivial.
move=> i.
rewrite
  Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed_size
  => hi.
have hib : nth 0 sd i \in dbyte.
+ move: hbytes; rewrite allP => hbytes.
  apply hbytes.
  by rewrite mem_nth hsize.
move: hib.
rewrite /dbyte supp_dinter => hib.
rewrite
  /Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed
  /KeygenSeedXofSpec.seed_input_bytes
  nth_mkseq 1:/#.
rewrite /raw_seed_of_security_seed.
simplify.
rewrite BArray32.initiE 1:/#.
apply W8.to_uintK_small.
smt().
qed.

lemma draw_raw_seed_lossless :
  is_lossless draw_raw_seed.
proof.
rewrite /draw_raw_seed.
by apply dmap_ll; apply seed_distribution_lossless.
qed.

lemma draw_raw_seed_pushforward_dseed :
  dmap draw_raw_seed
    Mode2FaithfulSecurityExpandVecASeedBridgePostFreeze.raw_security_seed =
  dseed.
proof.
rewrite /draw_raw_seed dmap_comp.
apply dmap_id_eq_in.
move=> sd hsd.
rewrite /(\o).
exact (raw_security_seed_roundtrip sd hsd).
qed.

end Mode2FaithfulSecurityRawSeedDistributionPostFreeze.
