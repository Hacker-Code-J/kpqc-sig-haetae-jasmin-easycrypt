require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import SignMuHashTarget VerifyMuHashTarget.
require import ExtractedMuHashPrefix ExactMuTopControl.
require import RegionLocalMuEquivalence.

theory RegionLocalMuTop.

module Sign = SignMuHashTarget.M.
module Verify = VerifyMuHashTarget.M.
module SignTop = ExtractedMuHashPrefix.SignRawMuTop.

op mode2_vkbytes : int = ExtractedMuHashPrefix.mode2_vkbytes.

lemma sign_wrapper_verify_generated_raw_mu_prefix_regionwise
    (sign_mem verify_mem : global_mem_t)
    (sk0 : BArray2752.t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [SignTop.run ~ Verify.__verify_hash_mu :
    Glob.mem{1} = sign_mem /\ Glob.mem{2} = verify_mem /\
    skp{1} = sk0 /\ vkp{2} = base /\
    vklen{2} = W64.of_int mode2_vkbytes /\
    preaddr{1} = prep{2} /\ prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\ mlen{1} = mlen{2} /\
    ExactMuTopControl.raw_prelen prelen{2} /\
    ExtractedMuHashPrefix.sk_memory_prefix sk0 verify_mem base /\
    ExactMuTopControl.valid_region prep{2} prelen{2} /\
    ExactMuTopControl.valid_region mp{2} mlen{2} /\
    RegionLocalMuEquivalence.region_eq
      sign_mem verify_mem prep{2} prelen{2} /\
    RegionLocalMuEquivalence.region_eq
      sign_mem verify_mem mp{2} mlen{2}
    ==>
    ExtractedMuHashPrefix.mu32_prefix res{1} res{2}].
proof.
move=> hbase.
transitivity ExtractedMuHashPrefix.VerifyRawMuTop.run
  (Glob.mem{1} = sign_mem /\ Glob.mem{2} = verify_mem /\
   skp{1} = sk0 /\ vkp{2} = base /\
   preaddr{1} = prep{2} /\ prelen{1} = prelen{2} /\
   maddr{1} = mp{2} /\ mlen{1} = mlen{2} /\
   ExtractedMuHashPrefix.sk_memory_prefix sk0 verify_mem base /\
   ExactMuTopControl.valid_region prep{2} prelen{2} /\
   ExactMuTopControl.valid_region mp{2} mlen{2} /\
   RegionLocalMuEquivalence.region_eq
     sign_mem verify_mem prep{2} prelen{2} /\
   RegionLocalMuEquivalence.region_eq
     sign_mem verify_mem mp{2} mlen{2}
   ==>
   ExtractedMuHashPrefix.mu32_prefix res{1} res{2})
  (={mup, vkp, prep, prelen, mp, mlen, Glob.mem} /\
   vklen{2} = W64.of_int mode2_vkbytes /\
   ExactMuTopControl.raw_prelen prelen{2}
   ==>
   ={res, Glob.mem}).
+ move=> &1 &2 />.
  move=> hvk hpa hpl hma hml hlo hhi hpref hpre hmsg hpre_eq hmsg_eq.
  exists Glob.mem{2}
    (mup{2}, vkp{2}, prep{2}, prelen{2}, mp{2}, mlen{2}).
  auto.
+ move=> &1 &m &2 hprefix [hres _].
  rewrite -hres.
  exact hprefix.
+ apply (RegionLocalMuEquivalence.sign_verify_raw_mu_top_wrappers_prefix_regionwise
          sign_mem verify_mem sk0 base hbase).
+ symmetry.
  conseq ExactMuTopControl.verify_hash_mu_raw_refines_raw_top; auto.
  move=> &1 &2 />; auto.
  smt().
qed.

lemma sign_verify_generated_raw_mu_prefix_regionwise
    (sign_mem verify_mem : global_mem_t)
    (sk0 : BArray2752.t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [Sign._sf_mu_rawpre ~ Verify.__verify_hash_mu :
    Glob.mem{1} = sign_mem /\ Glob.mem{2} = verify_mem /\
    skp{1} = sk0 /\ vkp{2} = base /\
    vkbytes{1} = W64.of_int mode2_vkbytes /\
    vklen{2} = W64.of_int mode2_vkbytes /\
    preaddr{1} = prep{2} /\ prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\ mlen{1} = mlen{2} /\
    ExactMuTopControl.raw_prelen prelen{2} /\
    ExtractedMuHashPrefix.sk_memory_prefix sk0 verify_mem base /\
    ExactMuTopControl.valid_region prep{2} prelen{2} /\
    ExactMuTopControl.valid_region mp{2} mlen{2} /\
    RegionLocalMuEquivalence.region_eq
      sign_mem verify_mem prep{2} prelen{2} /\
    RegionLocalMuEquivalence.region_eq
      sign_mem verify_mem mp{2} mlen{2}
    ==>
    ExtractedMuHashPrefix.mu32_prefix res{1} res{2}].
proof.
move=> hbase.
transitivity SignTop.run
  (={mup, skp, preaddr, prelen, maddr, mlen, Glob.mem} /\
   vkbytes{1} = W64.of_int mode2_vkbytes
   ==>
   ={res, Glob.mem})
  (Glob.mem{1} = sign_mem /\ Glob.mem{2} = verify_mem /\
   skp{1} = sk0 /\ vkp{2} = base /\
   vklen{2} = W64.of_int mode2_vkbytes /\
   preaddr{1} = prep{2} /\ prelen{1} = prelen{2} /\
   maddr{1} = mp{2} /\ mlen{1} = mlen{2} /\
   ExactMuTopControl.raw_prelen prelen{2} /\
   ExtractedMuHashPrefix.sk_memory_prefix sk0 verify_mem base /\
   ExactMuTopControl.valid_region prep{2} prelen{2} /\
   ExactMuTopControl.valid_region mp{2} mlen{2} /\
   RegionLocalMuEquivalence.region_eq
     sign_mem verify_mem prep{2} prelen{2} /\
   RegionLocalMuEquivalence.region_eq
     sign_mem verify_mem mp{2} mlen{2}
   ==>
   ExtractedMuHashPrefix.mu32_prefix res{1} res{2}).
+ move=> &1 &2 />.
  move=> hsm hvm hsk hbase0 hvkb hvkl hpa hpl hma hml hraw hpref
          hmsg_eq.
  exists Glob.mem{1}
    (mup{1}, skp{1}, preaddr{1}, prelen{1}, maddr{1}, mlen{1}).
  auto.
+ move=> &1 &m &2 [hres _] hprefix.
  rewrite hres.
  exact hprefix.
+ conseq ExactMuTopControl.sf_mu_rawpre_refines_raw_top.
+ move=> &1 &2 />; auto.
+ auto.
+ apply (sign_wrapper_verify_generated_raw_mu_prefix_regionwise
          sign_mem verify_mem sk0 base hbase).
qed.

end RegionLocalMuTop.
