require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import SignMuHashTarget VerifyMuHashTarget.
require import ExtractedMuHashPrefix.

theory ExactMuTopControl.

module Sign = SignMuHashTarget.M.
module Verify = VerifyMuHashTarget.M.

module SignWrap = ExtractedMuHashPrefix.SignRawMuTop.
module VerifyWrap = ExtractedMuHashPrefix.VerifyRawMuTop.

op mode2_vkbytes : int = ExtractedMuHashPrefix.mode2_vkbytes.

op raw_prelen (prelen : W64.t) : bool =
  0 <= W64.to_uint prelen /\ W64.to_uint prelen < 2 ^ 63.

op valid_region (base len : W64.t) : bool =
  W64.to_uint base + W64.to_uint len <= W64.modulus.

lemma raw_prelen_shr63_zero prelen :
  raw_prelen prelen =>
  prelen `>>` (W8.of_int 63) = W64.zero.
proof.
rewrite /raw_prelen => hraw.
apply W64.to_uint_eq.
rewrite W64.shr_div_le 1:/# W64.to_uint0 /=.
smt().
qed.

lemma raw_prelen_branch_guard prelen :
  raw_prelen prelen =>
  (protect_64 ((protect_64 prelen init_msf) `>>` (W8.of_int 63)) init_msf) =
  W64.zero.
proof.
by rewrite /protect_64; apply raw_prelen_shr63_zero.
qed.

lemma raw_prelen_zero : raw_prelen W64.zero.
proof.
by rewrite /raw_prelen W64.to_uint0 /=.
qed.

lemma sf_mu_rawpre_refines_raw_top :
  equiv [Sign._sf_mu_rawpre ~ SignWrap.run :
    ={Glob.mem, mup, skp, preaddr, prelen, maddr, mlen} /\
    vkbytes{1} = W64.of_int mode2_vkbytes
    ==>
    ={res, Glob.mem}].
proof.
proc.
inline ExtractedMuHashPrefix.SignRawMuCore.run
       ExtractedMuHashPrefix.SignFinalSqueeze.run.
wp.
call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
+ proc; sim.
wp.
call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
+ proc; sim.
wp.
call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
+ proc; sim.
wp.
call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
+ proc; sim.
call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
+ proc; sim.
call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
+ proc; sim.
wp.
call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
+ proc; sim.
auto => />; rewrite /protect_ptr.
qed.

lemma verify_hash_mu_raw_refines_raw_top :
  equiv [Verify.__verify_hash_mu ~ VerifyWrap.run :
    ={Glob.mem, mup, vkp, prep, prelen, mp, mlen} /\
    vklen{1} = W64.of_int mode2_vkbytes /\
    raw_prelen prelen{1}
    ==>
    res{1} = res{2}].
proof.
proc.
inline ExtractedMuHashPrefix.VerifyRawMuCore.run
       ExtractedMuHashPrefix.VerifyFinalSqueeze.run.
rcondt{1} 18.
+ move=> &1.
   auto => />.
   rewrite /protect_64.
   call (_: true).
   auto.
   wp.
   call (_: true).
   auto => />.
   auto => />.
   move=> hnonneg hhigh.
   apply W64.to_uint_eq.
   rewrite W64.shr_div_le 1:/# W64.to_uint0 /=.
   smt().
+ wp.
   call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
   + proc; sim.
   wp.
   call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
   + proc; sim.
   call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
   + proc; sim.
   call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
   + proc; sim.
   wp.
   call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
   + proc; sim.
   wp.
   call (_: ={arg, Glob.mem} ==> ={res, Glob.mem}).
   + proc; sim.
   auto => />; rewrite /protect_64.
qed.

lemma sign_wrapper_verify_exact_raw_mu_prefix
    (sk0 : BArray2752.t) (mem0 : global_mem_t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [SignWrap.run ~ Verify.__verify_hash_mu :
    ={Glob.mem} /\
    skp{1} = sk0 /\
    Glob.mem{2} = mem0 /\
    vkp{2} = base /\
    vklen{2} = W64.of_int mode2_vkbytes /\
    preaddr{1} = prep{2} /\
    prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\
    mlen{1} = mlen{2} /\
    raw_prelen prelen{2} /\
    valid_region prep{2} prelen{2} /\
    valid_region mp{2} mlen{2} /\
    ExtractedMuHashPrefix.sk_memory_prefix sk0 mem0 base
    ==>
    ExtractedMuHashPrefix.mu32_prefix res{1} res{2}].
proof.
move=> hbase.
transitivity VerifyWrap.run
  (={Glob.mem} /\
   skp{1} = sk0 /\ Glob.mem{2} = mem0 /\ vkp{2} = base /\
   preaddr{1} = prep{2} /\ prelen{1} = prelen{2} /\
   maddr{1} = mp{2} /\ mlen{1} = mlen{2} /\
   ExtractedMuHashPrefix.sk_memory_prefix sk0 mem0 base
   ==>
   ExtractedMuHashPrefix.mu32_prefix res{1} res{2})
  (={mup, vkp, prep, prelen, mp, mlen, Glob.mem} /\
   vklen{2} = W64.of_int mode2_vkbytes /\
   raw_prelen prelen{2}
   ==>
   ={res, Glob.mem}).
+ move=> &1 &2 />.
  move=> hvk hpa hpl hma hml hlo hhi hpre hmsg hpref.
  exists (Glob.mem){2}
    (mup{2}, vkp{2}, prep{2}, prelen{2}, mp{2}, mlen{2}).
  auto.
+ move=> &1 &m &2 hprefix [hres _].
  rewrite -hres.
  exact hprefix.
+ apply (ExtractedMuHashPrefix.sign_verify_raw_mu_top_wrappers_prefix
          sk0 mem0 base hbase).
+ symmetry.
  conseq verify_hash_mu_raw_refines_raw_top; auto.
  move=> &1 &2 />; auto.
  smt().
qed.

lemma sign_verify_generated_raw_mu_prefix
    (sk0 : BArray2752.t) (mem0 : global_mem_t) (base : W64.t) :
  W64.to_uint base + mode2_vkbytes < W64.modulus =>
  equiv [Sign._sf_mu_rawpre ~ Verify.__verify_hash_mu :
    ={Glob.mem} /\
    skp{1} = sk0 /\
    Glob.mem{2} = mem0 /\
    vkp{2} = base /\
    vkbytes{1} = W64.of_int mode2_vkbytes /\
    vklen{2} = W64.of_int mode2_vkbytes /\
    preaddr{1} = prep{2} /\
    prelen{1} = prelen{2} /\
    maddr{1} = mp{2} /\
    mlen{1} = mlen{2} /\
    raw_prelen prelen{2} /\
    valid_region prep{2} prelen{2} /\
    valid_region mp{2} mlen{2} /\
    ExtractedMuHashPrefix.sk_memory_prefix sk0 mem0 base
    ==>
    ExtractedMuHashPrefix.mu32_prefix res{1} res{2}].
proof.
move=> hbase.
transitivity SignWrap.run
  (={mup, skp, preaddr, prelen, maddr, mlen, Glob.mem} /\
   vkbytes{1} = W64.of_int mode2_vkbytes
   ==>
   ={res, Glob.mem})
  (={Glob.mem} /\
   skp{1} = sk0 /\ Glob.mem{2} = mem0 /\ vkp{2} = base /\
   vklen{2} = W64.of_int mode2_vkbytes /\
   preaddr{1} = prep{2} /\ prelen{1} = prelen{2} /\
   maddr{1} = mp{2} /\ mlen{1} = mlen{2} /\
   raw_prelen prelen{2} /\
   valid_region prep{2} prelen{2} /\
   valid_region mp{2} mlen{2} /\
   ExtractedMuHashPrefix.sk_memory_prefix sk0 mem0 base
   ==>
   ExtractedMuHashPrefix.mu32_prefix res{1} res{2}).
+ move=> &1 &2 />.
  move=> hvkb hvkl hpa hpl hma hml hlo hhi hpre hmsg hpref.
  exists (Glob.mem){2}
    (mup{1}, skp{1}, preaddr{1}, prelen{1}, maddr{1}, mlen{1}).
  auto.
+ move=> &1 &m &2 [hres _] hprefix.
  rewrite hres.
  exact hprefix.
+ conseq sf_mu_rawpre_refines_raw_top.
+ move=> &1 &2 />.
   auto.
+ auto.
+ apply (sign_wrapper_verify_exact_raw_mu_prefix sk0 mem0 base hbase).
qed.

end ExactMuTopControl.
