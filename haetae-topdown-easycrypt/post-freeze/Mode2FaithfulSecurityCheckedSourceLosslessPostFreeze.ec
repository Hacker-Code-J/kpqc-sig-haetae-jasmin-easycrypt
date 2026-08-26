require import AllCore.

from Jasmin require import JModel_x86.

require import BArray32 BArray128.
require import KeygenMode2ParentSpec.
require import TargetKeygenM23FinalizeComposition.
require import Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze.

theory Mode2FaithfulSecurityCheckedSourceLosslessPostFreeze.

(* This file only lifts the checked first-attempt sampler-progress certificate
   through the stateful checked public-key source.  It does not claim retry
   termination, full HAETAE.kg losslessness, input-distribution fidelity, or
   any property of the real key-generation loop beyond this conditional path. *)

lemma checked_mode2_public_key_source_sample_progress_ll
    (seedbuf0 : BArray128.t) (raw_seed0 : BArray32.t)
    mat_limit vec_limit eta_limit :
  phoare
    [Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
       .CheckedMode2PublicKeySource.sample :
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.seedbuf_in = seedbuf0 /\
      Mode2FaithfulSecurityCheckedPublicKeySourcePostFreeze
        .CheckedMode2PublicKeySource.raw_seed_in = raw_seed0 /\
      KeygenMode2ParentSpec.mode2_sampler_prefix_progress
        raw_seed0 mat_limit vec_limit eta_limit
      ==> true] = 1%r.
proof.
proc.
wp.
call
  (TargetKeygenM23FinalizeComposition
    .checked_mode2_parent_m23_finalize_progress_ll
    seedbuf0 raw_seed0 mat_limit vec_limit eta_limit).
auto => />.
qed.

end Mode2FaithfulSecurityCheckedSourceLosslessPostFreeze.
