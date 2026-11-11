require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import BArray32 HyperballNormSpec HyperballScaleSpec
  CheckedAcceptanceCorrectness CheckedProductionBridge.
import SLH64 HyperballScaleSpec.

lemma hpc_values_safe_bit (l t : int) (bound0 : W64.t) :
  hoare [HPH._polyfixveclk_scale_and_check_values :
    lcount=W64.of_int l /\ total=W64.of_int t /\ bound=bound0 /\ hb_scale_bounds l t ==>
    (res.`3=W64.zero \/ res.`3=W64.one) /\
    (res.`3=W64.one => hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0)].
proof. proc; call (hca_scale_and_check_safe_bit l t bound0); auto. qed.

lemma hpc_values_ll : islossless HPH._polyfixveclk_scale_and_check_values.
proof. proc; call hca_scale_and_check_ll; auto. qed.

lemma hpc_values_total (l t : int) (bound0 : W64.t) :
  phoare [HPH._polyfixveclk_scale_and_check_values :
    lcount=W64.of_int l /\ total=W64.of_int t /\ bound=bound0 /\ hb_scale_bounds l t ==>
    (res.`3=W64.zero \/ res.`3=W64.one) /\
    (res.`3=W64.one => hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0)] = 1%r.
proof. by conseq hpc_values_ll (hpc_values_safe_bit l t bound0). qed.

lemma hpc_signer_values_safe_bit (l t : int) (bound0 : W64.t) :
  hoare [HPS._sf_scale_and_check :
    lcount=W64.of_int l /\ total=W64.of_int t /\ bound=bound0 /\ hb_scale_bounds l t ==>
    (res.`3=W64.zero \/ res.`3=W64.one) /\
    (res.`3=W64.one => hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0)].
proof.
  by conseq hardened_signer_wrapper_equiv (hpc_values_safe_bit l t bound0) => /#.
qed.

lemma hpc_signer_values_ll : islossless HPS._sf_scale_and_check.
proof. by conseq hardened_signer_wrapper_equiv hpc_values_ll => /#. qed.

lemma hpc_signer_values_total (l t : int) (bound0 : W64.t) :
  phoare [HPS._sf_scale_and_check :
    lcount=W64.of_int l /\ total=W64.of_int t /\ bound=bound0 /\ hb_scale_bounds l t ==>
    (res.`3=W64.zero \/ res.`3=W64.one) /\
    (res.`3=W64.one => hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0)] = 1%r.
proof. by conseq hardened_signer_wrapper_equiv (hpc_values_total l t bound0) => /#. qed.

lemma hpc_phase_check_safe_bit (l t : int) (bound0 : W64.t) :
  hoare [HPP._hb_checked_scale_and_check_values :
    lcount=W64.of_int l /\ total=W64.of_int t /\ bound=bound0 /\ hb_scale_bounds l t ==>
    (res.`3=W64.zero \/ res.`3=W64.one) /\
    (res.`3=W64.one => hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0)].
proof.
  by conseq hardened_phase_check_equiv (hca_scale_and_check_safe_bit l t bound0) => /#.
qed.

lemma hpc_phase_check_ll : islossless HPP._hb_checked_scale_and_check_values.
proof. by conseq hardened_phase_check_equiv hca_scale_and_check_ll => /#. qed.

lemma hpc_phase_state_safe_bit (state0 : BArray32.t) (l t : int) (bound0 : W64.t) :
  hoare [HPP._polyfixveclk_scale_and_check :
    statep=state0 /\ BArray32.get64 state0 0=W64.of_int l /\
    BArray32.get64 state0 1=W64.of_int t /\ BArray32.get64 state0 2=bound0 /\
    hb_scale_bounds l t ==>
    (BArray32.get64 res.`3 3=W64.zero \/ BArray32.get64 res.`3 3=W64.one) /\
    (BArray32.get64 res.`3 3=W64.one =>
      hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0)].
proof.
  proc; wp; call (hpc_phase_check_safe_bit l t bound0).
  auto => />; rewrite /protect_ptr BArray32.get_set64E 1..2:// /=; smt().
qed.

lemma hpc_phase_state_ll : islossless HPP._polyfixveclk_scale_and_check.
proof. proc; wp; call hpc_phase_check_ll; auto. qed.

lemma hpc_phase_state_total (state0 : BArray32.t) (l t : int) (bound0 : W64.t) :
  phoare [HPP._polyfixveclk_scale_and_check :
    statep=state0 /\ BArray32.get64 state0 0=W64.of_int l /\
    BArray32.get64 state0 1=W64.of_int t /\ BArray32.get64 state0 2=bound0 /\
    hb_scale_bounds l t ==>
    (BArray32.get64 res.`3 3=W64.zero \/ BArray32.get64 res.`3 3=W64.one) /\
    (BArray32.get64 res.`3 3=W64.one =>
      hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0)] = 1%r.
proof. by conseq hpc_phase_state_ll (hpc_phase_state_safe_bit state0 l t bound0). qed.

lemma hpc_phase_export_safe_bit (state0 : BArray32.t) (l t : int) (bound0 : W64.t) :
  hoare [HPP.polyfixveclk_scale_and_check_jazz :
    statep=state0 /\ BArray32.get64 state0 0=W64.of_int l /\
    BArray32.get64 state0 1=W64.of_int t /\ BArray32.get64 state0 2=bound0 /\
    hb_scale_bounds l t ==>
    (BArray32.get64 res.`3 3=W64.zero \/ BArray32.get64 res.`3 3=W64.one) /\
    (BArray32.get64 res.`3 3=W64.one =>
      hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0)].
proof.
  proc; call (hpc_phase_state_safe_bit state0 l t bound0).
  auto => />; rewrite /protect_ptr; smt().
qed.

lemma hpc_phase_export_ll : islossless HPP.polyfixveclk_scale_and_check_jazz.
proof. proc; call hpc_phase_state_ll; auto. qed.

lemma hpc_phase_export_total (state0 : BArray32.t) (l t : int) (bound0 : W64.t) :
  phoare [HPP.polyfixveclk_scale_and_check_jazz :
    statep=state0 /\ BArray32.get64 state0 0=W64.of_int l /\
    BArray32.get64 state0 1=W64.of_int t /\ BArray32.get64 state0 2=bound0 /\
    hb_scale_bounds l t ==>
    (BArray32.get64 res.`3 3=W64.zero \/ BArray32.get64 res.`3 3=W64.one) /\
    (BArray32.get64 res.`3 3=W64.one =>
      hyperball_sqnorm res.`1 l res.`2 (t-l)<=W64.to_uint bound0)] = 1%r.
proof. by conseq hpc_phase_export_ll (hpc_phase_export_safe_bit state0 l t bound0). qed.

lemma hpc_shift8 (x : int) :
  W64.of_int x `<<` W8.of_int 8 = W64.of_int (256*x).
proof.
  rewrite /(`<<`) W8.of_uintK /= W64.shlMP 1:// /=; congr; ring.
qed.

lemma hpc_count_bounds l k : 0<=l<=8 => 0<=k<=8 =>
  hb_scale_bounds (256*l) (256*(l+k)).
proof. rewrite /hb_scale_bounds; smt(). qed.

(* The retry loop is a partial-correctness claim. Earlier sampling and
   fixed-point calls may return arbitrary values; every returning iteration
   still passes through the checked integer-norm guard. *)
lemma hpc_standalone_full_safe (l k : int) (bound0 : W64.t) :
  hoare [HPH._hyperball_full :
    lcount=W64.of_int l /\ kcount=W64.of_int k /\ bound_const=bound0 /\
    0<=l<=8 /\ 0<=k<=8 ==>
    hyperball_sqnorm res.`1 (256*l) res.`2 (256*k)<=W64.to_uint bound0].
proof.
  proc; wp; call (_ : true ==> true); first by conseq.
  while (lcount=W64.of_int l /\ kcount=W64.of_int k /\ bound_const=bound0 /\
    0<=l<=8 /\ 0<=k<=8 /\ (accepted=W64.zero \/ accepted=W64.one) /\
    (accepted=W64.one => hyperball_sqnorm y1p (256*l) y2p (256*k)<=W64.to_uint bound0)).
  + wp; call (hpc_values_safe_bit (256*l) (256*(l+k)) bound0).
    wp; call (_ : true ==> true); first by conseq.
    wp; call (_ : true ==> true); first by conseq.
    wp; call (_ : true ==> true); first by conseq.
    while (lcount=W64.of_int l /\ kcount=W64.of_int k /\ bound_const=bound0 /\
      total=W64.of_int (l+k) /\ 0<=l<=8 /\ 0<=k<=8).
    - wp; call (_ : true ==> true); first by conseq.
      by auto.
    wp; call (_ : true ==> true); first by conseq.
    wp; call (_ : true ==> true); first by conseq.
    auto => />; rewrite ?W64.of_intD' ?hpc_shift8.
    smt(hpc_count_bounds).
  auto => />; smt(W64.to_uint_eq W64.to_uint0 W64.to_uint1).
qed.

lemma hpc_signer_full_safe (l k : int) (bound0 : W64.t) :
  hoare [HPS._sf_hyperball_full :
    lcount=W64.of_int l /\ kcount=W64.of_int k /\ bound_const=bound0 /\
    0<=l<=8 /\ 0<=k<=8 ==>
    hyperball_sqnorm res.`1 (256*l) res.`2 (256*k)<=W64.to_uint bound0].
proof.
  proc; wp; call (_ : true ==> true); first by conseq.
  while (lcount=W64.of_int l /\ kcount=W64.of_int k /\ bound_const=bound0 /\
    0<=l<=8 /\ 0<=k<=8 /\ (accepted=W64.zero \/ accepted=W64.one) /\
    (accepted=W64.one => hyperball_sqnorm y1p (256*l) y2p (256*k)<=W64.to_uint bound0)).
  + wp; call (hpc_signer_values_safe_bit (256*l) (256*(l+k)) bound0).
    wp; call (_ : true ==> true); first by conseq.
    wp; call (_ : true ==> true); first by conseq.
    wp; call (_ : true ==> true); first by conseq.
    while (lcount=W64.of_int l /\ kcount=W64.of_int k /\ bound_const=bound0 /\
      total=W64.of_int (l+k) /\ 0<=l<=8 /\ 0<=k<=8).
    - wp; call (_ : true ==> true); first by conseq.
      by auto.
    wp; call (_ : true ==> true); first by conseq.
    wp; call (_ : true ==> true); first by conseq.
    auto => />; rewrite ?W64.of_intD' ?hpc_shift8.
    smt(hpc_count_bounds).
  auto => />; smt(W64.to_uint_eq W64.to_uint0 W64.to_uint1).
qed.

lemma hpc_standalone_mode2_safe :
  hoare [HPH.polyfixveclk_sample_hyperball_mode2_jazz : true ==>
    hyperball_sqnorm res.`1 1024 res.`2 512<=6505809026482176].
proof.
  proc; call (hpc_standalone_full_safe 4 2 (W64.of_int 6505809026482176)).
  auto => />; rewrite /protect_64 /protect_ptr W64.of_uintK /=; smt().
qed.

lemma hpc_standalone_mode3_safe :
  hoare [HPH.polyfixveclk_sample_hyperball_mode3_jazz : true ==>
    hyperball_sqnorm res.`1 1536 res.`2 768<=22510896139993088].
proof.
  proc; call (hpc_standalone_full_safe 6 3 (W64.of_int 22510896139993088)).
  auto => />; rewrite /protect_64 /protect_ptr W64.of_uintK /=; smt().
qed.

lemma hpc_standalone_mode5_safe :
  hoare [HPH.polyfixveclk_sample_hyperball_mode5_jazz : true ==>
    hyperball_sqnorm res.`1 1792 res.`2 1024<=33503371683954688].
proof.
  proc; call (hpc_standalone_full_safe 7 4 (W64.of_int 33503371683954688)).
  auto => />; rewrite /protect_64 /protect_ptr W64.of_uintK /=; smt().
qed.

lemma hpc_signer_mode2_safe :
  hoare [HPS._sf_hyperball_mode2 : true ==>
    hyperball_sqnorm res.`1 1024 res.`2 512<=6505809026482176].
proof.
  proc; call (hpc_signer_full_safe 4 2 (W64.of_int 6505809026482176)).
  auto => />; rewrite /protect_64 /protect_ptr W64.of_uintK /=; smt().
qed.

lemma hpc_signer_mode3_safe :
  hoare [HPS._sf_hyperball_mode3 : true ==>
    hyperball_sqnorm res.`1 1536 res.`2 768<=22510896139993088].
proof.
  proc; call (hpc_signer_full_safe 6 3 (W64.of_int 22510896139993088)).
  auto => />; rewrite /protect_64 /protect_ptr W64.of_uintK /=; smt().
qed.

lemma hpc_signer_mode5_safe :
  hoare [HPS._sf_hyperball_mode5 : true ==>
    hyperball_sqnorm res.`1 1792 res.`2 1024<=33503371683954688].
proof.
  proc; call (hpc_signer_full_safe 7 4 (W64.of_int 33503371683954688)).
  auto => />; rewrite /protect_64 /protect_ptr W64.of_uintK /=; smt().
qed.
