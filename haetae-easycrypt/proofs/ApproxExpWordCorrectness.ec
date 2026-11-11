require import AllCore IntDiv List Real StdOrder.
from Jasmin require import JModel_x86.
require import ApproxExpSpec ReferenceConstants SamplerConstants FixedPointSpec
  FixedPointCorrectness SamplerTarget SigningSamplerBridge.
require import SigmaExpInputBounds.
import RField RealOrder.

lemma ae_coefficients_provenance : ae_coefficients = reference_exp_coefficients.
proof. by rewrite /ae_coefficients. qed.

lemma ae_coefficient_facts :
  size ae_coefficients = 11 /\ size ae_tail = 10 /\
  ae_leading = 55868746 /\ 0 <= ae_leading <= ae_bound /\
  all ae_coefficient_ok ae_tail.
proof.
  by rewrite /ae_tail /ae_leading /ae_coefficients /reference_exp_coefficients
    /ae_coefficient_ok /ae_scale /ae_bound /=.
qed.

lemma ae_domain_bounds x : ae_domain x =>
  0 <= x <= ae_scale /\ x < W64.modulus.
proof. rewrite /ae_domain /ae_scale; smt(). qed.

lemma ae_ceil_remainder a x :
  0 <= ae_scale * ae_ceil a x - a*x <= ae_scale-1.
proof.
  have hd := divz_eq (a*x+ae_scale-1) ae_scale.
  have hr := modz_cmp (a*x+ae_scale-1) ae_scale _; first by rewrite /ae_scale.
  rewrite /ae_ceil /ae_scale in hd.
  rewrite /ae_scale in hr.
  rewrite /ae_ceil /ae_scale; smt().
qed.

lemma ae_ceil_old_form a x :
  ae_ceil a x = (a*x) %/ ae_scale + b2i ((a*x) %% ae_scale <> 0).
proof.
  have hd := divz_eq (a*x) ae_scale.
  have hr := modz_cmp (a*x) ae_scale _; first by rewrite /ae_scale.
  have hc := ae_ceil_remainder a x.
  rewrite /ae_scale in hd.
  rewrite /ae_scale in hr.
  rewrite /ae_scale in hc.
  rewrite /ae_scale /b2i.
  case ((a*x) %% 281474976710656 <> 0); smt().
qed.

lemma ae_ceil_bound a x : ae_domain x => -ae_bound <= a <= ae_bound =>
  -(2*ae_scale+4) <= ae_ceil a x <= 2*ae_scale+5.
proof.
  move=> hx ha.
  have he := ae_ceil_remainder a x.
  have hx0 : 0 <= x by move: hx; rewrite /ae_domain; smt().
  have hprodlo : -ae_bound*x <= a*x by smt().
  have hprodhi : a*x <= ae_bound*x by smt().
  move: hx ha he hprodlo hprodhi.
  rewrite /ae_domain /ae_scale /ae_bound; smt().
qed.

lemma ae_step_bound a x c : ae_domain x => -ae_bound <= a <= ae_bound =>
  ae_coefficient_ok c => -ae_bound <= ae_ceil a x+c <= ae_bound.
proof.
  move=> hx ha hc.
  have hq := ae_ceil_bound a x hx ha.
  move: hc hq; rewrite /ae_coefficient_ok /ae_bound /ae_scale; smt().
qed.

lemma ae_integer_fold_nil x a : ae_integer_fold x a [] = a.
proof. by rewrite /ae_integer_fold. qed.
lemma ae_integer_fold_cons x a c cs :
  ae_integer_fold x a (c::cs) = ae_integer_fold x (ae_ceil a x+c) cs.
proof. by rewrite /ae_integer_fold. qed.
lemma ae_real_fold_nil z r : ae_real_fold z r [] = r.
proof. by rewrite /ae_real_fold. qed.
lemma ae_real_fold_cons z r c cs :
  ae_real_fold z r (c::cs) = ae_real_fold z (r*z+c%r) cs.
proof. by rewrite /ae_real_fold. qed.
lemma ae_word_fold_nil mul x r : ae_word_fold mul x r [] = r.
proof. by rewrite /ae_word_fold. qed.
lemma ae_word_fold_cons mul x r c cs :
  ae_word_fold mul x r (c::cs) = ae_word_fold mul x (mul r x+W64.of_int c) cs.
proof. by rewrite /ae_word_fold. qed.

lemma ae_integer_fold_bound x cs :
  forall a, ae_domain x => -ae_bound <= a <= ae_bound =>
  all ae_coefficient_ok cs => -ae_bound <= ae_integer_fold x a cs <= ae_bound.
proof.
  elim: cs => [|c cs ih] a hx ha hcs.
  + by rewrite ae_integer_fold_nil.
  have [hc ht] : ae_coefficient_ok c /\ all ae_coefficient_ok cs by move: hcs; rewrite /=.
  rewrite ae_integer_fold_cons.
  exact (ih (ae_ceil a x+c) hx (ae_step_bound a x c hx ha hc) ht).
qed.

lemma ae_integer_bound x : ae_domain x => -ae_bound <= ae_integer x <= ae_bound.
proof.
  move=> hx.
  have [_ [_ [hhead [hh hc]]]] := ae_coefficient_facts.
  rewrite /ae_integer; apply ae_integer_fold_bound => //; smt().
qed.

lemma ae_intermediate_bounds x k : ae_domain x =>
  -ae_bound <= ae_integer_fold x ae_leading (take k ae_tail) <= ae_bound /\
  -ae_bound <= ae_ceil (ae_integer_fold x ae_leading (take k ae_tail)) x <= ae_bound.
proof.
  move=> hx.
  have [_ [_ [hhead [hh hc]]]] := ae_coefficient_facts.
  have ht : all ae_coefficient_ok (take k ae_tail).
  + apply List.allP => c hmem.
    have hm := mem_take k ae_tail c hmem.
    move: hc; rewrite List.allP => hc; exact (hc c hm).
  have ha := ae_integer_fold_bound x (take k ae_tail) ae_leading hx _ ht; first smt().
  have hq := ae_ceil_bound (ae_integer_fold x ae_leading (take k ae_tail)) x hx ha.
  move: ha hq; rewrite /ae_scale /ae_bound; smt().
qed.

lemma ae_smulh_bridge a x : ae_domain x => -ae_bound <= a <= ae_bound =>
  smulh48_word (W64.of_int a) (W64.of_int x) = W64.of_int (ae_ceil a x).
proof.
  move=> hx ha.
  have [hxrange hxmod] := ae_domain_bounds x hx.
  have hafit : W64.min_sint <= a <= W64.max_sint by move: ha; rewrite /ae_bound; smt().
  by rewrite smulh48_word_is_ceil /smulh48_ceil /= W64.to_sintK_small 1:hafit
    W64.to_uintK_small 1:/# -ae_ceil_old_form.
qed.

lemma ae_word_integer_fold x cs :
  forall a, ae_domain x => -ae_bound <= a <= ae_bound => all ae_coefficient_ok cs =>
  ae_word_fold smulh48_word (W64.of_int x) (W64.of_int a) cs =
    W64.of_int (ae_integer_fold x a cs).
proof.
  elim: cs => [|c cs ih] a hx ha hcs.
  + by rewrite ae_word_fold_nil ae_integer_fold_nil.
  have [hc ht] : ae_coefficient_ok c /\ all ae_coefficient_ok cs by move: hcs; rewrite /=.
  rewrite ae_word_fold_cons ae_integer_fold_cons ae_smulh_bridge 1:hx 1:ha -W64.of_intD.
  exact (ih (ae_ceil a x+c) hx (ae_step_bound a x c hx ha hc) ht).
qed.

lemma ae_reference_horner mul x :
  reference_approx_exp mul x = ae_word_fold mul x (W64.of_int ae_leading) ae_tail.
proof.
  rewrite /reference_approx_exp /ae_word_fold /ae_leading /ae_tail
    /ae_coefficients /reference_exp_coefficients /=.
  by rewrite !W64.of_intN' /=.
qed.

lemma ae_approx_exp_word x : ae_domain x =>
  approx_exp_word (W64.of_int x) = W64.of_int (ae_integer x).
proof.
  move=> hx.
  have [_ [_ [hhead [hh hc]]]] := ae_coefficient_facts.
  rewrite approx_exp_matches_reference ae_reference_horner /ae_integer.
  apply ae_word_integer_fold => //; smt().
qed.

lemma ae_ceil_nonnegative a x : 0 <= a => 0 <= x => 0 <= ae_ceil a x.
proof.
  move=> ha hx; rewrite /ae_ceil /ae_scale divz_ge0 //; smt().
qed.

lemma ae_ceil_lower a x b : 0 <= x <= ae_scale => 0 <= b => -b <= a =>
  -b <= ae_ceil a x.
proof.
  move=> hx hb ha.
  have he := ae_ceil_remainder a x.
  have h1 : -b*x <= a*x by smt().
  have h2 : -b*ae_scale <= -b*x by smt().
  move: he h1 h2; rewrite /ae_scale; smt().
qed.

lemma ae_pair_nonnegative a x b c :
  ae_domain x => 0 <= a => 0 <= b => b <= c =>
  0 <= ae_ceil (ae_ceil a x-b) x+c.
proof.
  move=> hx ha hb hbc.
  have [hxr _] := ae_domain_bounds x hx.
  have hq0 := ae_ceil_nonnegative a x ha _; first smt().
  have hq1 := ae_ceil_lower (ae_ceil a x-b) x b hxr hb _; first smt().
  smt().
qed.

lemma ae_integer_nonnegative x : ae_domain x => 0 <= ae_integer x.
proof.
  move=> hx.
  pose r0 := 55868746.
  pose r2 := ae_ceil (ae_ceil r0 x-743564434) x+6953427278.
  pose r4 := ae_ceil (ae_ceil r2 x-55833338892) x+390932311155.
  pose r6 := ae_ceil (ae_ceil r4 x-2345623661771) x+11728123872951.
  pose r8 := ae_ceil (ae_ceil r6 x-46912496106200) x+140737488354861.
  pose r10 := ae_ceil (ae_ceil r8 x-281474976710650) x+281474976710657.
  have h0 : 0 <= r0 by rewrite /r0.
  have h2 : 0 <= r2 by apply (ae_pair_nonnegative r0 x 743564434 6953427278 hx h0); trivial.
  have h4 : 0 <= r4 by apply (ae_pair_nonnegative r2 x 55833338892 390932311155 hx h2); trivial.
  have h6 : 0 <= r6 by apply (ae_pair_nonnegative r4 x 2345623661771 11728123872951 hx h4); trivial.
  have h8 : 0 <= r8 by apply (ae_pair_nonnegative r6 x 46912496106200 140737488354861 hx h6); trivial.
  have h10 : 0 <= r10 by apply (ae_pair_nonnegative r8 x 281474976710650 281474976710657 hx h8); trivial.
  rewrite /ae_integer /ae_integer_fold /ae_leading /ae_tail /ae_coefficients
    /reference_exp_coefficients /=.
  exact h10.
qed.

lemma ae_integer_unsigned x : ae_domain x =>
  W64.to_uint (W64.of_int (ae_integer x)) = ae_integer x.
proof.
  move=> hx.
  have h0 := ae_integer_nonnegative x hx.
  have h1 := ae_integer_bound x hx.
  apply W64.to_uintK_small; move: h1; rewrite /ae_bound; smt().
qed.

lemma ae_real_domain x : ae_domain x =>
  0%r <= x%r/ae_scale%r /\ 3%r*(x%r/ae_scale%r) <= 2%r.
proof.
  rewrite /ae_domain; move=> [h0 h3].
  have h0r : 0%r <= x%r by rewrite le_fromint.
  have h3r : 3%r*x%r <= 2%r*ae_scale%r.
  + by rewrite -!fromintM le_fromint.
  have he : ae_scale%r*(x%r/ae_scale%r) = x%r by rewrite /ae_scale; field; smt().
  move: h3r he; rewrite /ae_scale; smt().
qed.

lemma ae_real_scaled_error (s a x q : real) :
  0%r < s => 0%r <= s*q-a*x <= s-1%r =>
  0%r <= q-a*(x/s) <= 1%r.
proof.
  move=> hs he.
  have hmul : s*(q-a*(x/s)) = s*q-a*x by field; smt().
  smt().
qed.

lemma ae_ceil_real_error a x :
  0%r <= (ae_ceil a x)%r-a%r*(x%r/ae_scale%r) <= 1%r.
proof.
  have [h0 h1] := ae_ceil_remainder a x.
  have h0r : 0%r <= (ae_scale*ae_ceil a x-a*x)%r by rewrite le_fromint.
  have h1r : (ae_scale*ae_ceil a x-a*x)%r <= (ae_scale-1)%r by rewrite le_fromint.
  rewrite !fromintB !fromintM /= in h0r.
  rewrite !fromintB !fromintM /= in h1r.
  apply ae_real_scaled_error; first by rewrite /ae_scale.
  smt().
qed.

lemma ae_real_rounding_step (z a r q c : real) :
  0%r <= z => 3%r*z <= 2%r =>
  0%r <= a-r <= 3%r => 0%r <= q-a*z <= 1%r =>
  0%r <= (q+c)-(r*z+c) <= 3%r.
proof. smt(). qed.

lemma ae_horner_rounding3 x cs : forall a r,
  ae_domain x => 0%r <= a%r-r <= 3%r =>
  0%r <= (ae_integer_fold x a cs)%r - ae_real_fold (x%r/ae_scale%r) r cs <= 3%r.
proof.
  elim: cs => [|c cs ih] a r hx he.
  + by rewrite ae_integer_fold_nil ae_real_fold_nil.
  have [hz0 hz3] := ae_real_domain x hx.
  have hceil := ae_ceil_real_error a x.
  have hnext := ae_real_rounding_step (x%r/ae_scale%r) a%r r (ae_ceil a x)%r c%r
    hz0 hz3 he hceil.
  rewrite -fromintD in hnext.
  rewrite ae_integer_fold_cons ae_real_fold_cons.
  exact (ih (ae_ceil a x+c) (r*(x%r/ae_scale%r)+c%r) hx hnext).
qed.

lemma ae_real_divided_error (s a r : real) : 0%r < s => 0%r <= a-r <= 3%r =>
  0%r <= a/s-r/s <= 3%r/s.
proof.
  move=> hs he.
  have h0 : s*(a/s-r/s) = a-r by field; smt().
  have h1 : s*(3%r/s) = 3%r by field; smt().
  smt().
qed.

lemma ae_rounding_error3 x : ae_domain x =>
  0%r <= (ae_integer x)%r/ae_scale%r - ae_polynomial (x%r/ae_scale%r) <= 3%r/ae_scale%r.
proof.
  move=> hx.
  have h := ae_horner_rounding3 x ae_tail ae_leading ae_leading%r hx _; first smt().
  rewrite /ae_integer /ae_polynomial.
  apply ae_real_divided_error; first by rewrite /ae_scale.
  exact h.
qed.

lemma ae_rounding_error10 x : ae_domain x =>
  0%r <= (ae_integer x)%r/ae_scale%r - ae_polynomial (x%r/ae_scale%r) <= 10%r/ae_scale%r.
proof.
  move=> hx; have h := ae_rounding_error3 x hx.
  rewrite /ae_scale in h.
  rewrite /ae_scale; smt().
qed.

lemma ae_approx_exp_unsigned (w : W64.t) : ae_domain (W64.to_uint w) =>
  W64.to_uint (approx_exp_word w) = ae_integer (W64.to_uint w).
proof.
  move=> hx.
  have h := ae_approx_exp_word (W64.to_uint w) hx.
  rewrite W64.to_uintK in h.
  by rewrite h ae_integer_unsigned.
qed.

lemma ae_approx_exp_word_rounding3 (w : W64.t) : ae_domain (W64.to_uint w) =>
  0%r <= (W64.to_uint (approx_exp_word w))%r/ae_scale%r -
    ae_polynomial ((W64.to_uint w)%r/ae_scale%r) <= 3%r/ae_scale%r.
proof. move=> hx; rewrite ae_approx_exp_unsigned 1:hx; exact (ae_rounding_error3 _ hx). qed.

lemma ae_internal_correct (w : W64.t) :
  hoare [SamplerTarget.M._approx_exp : x=w /\ ae_domain (W64.to_uint w) ==>
    W64.to_uint res = ae_integer (W64.to_uint w) /\
    0%r <= (W64.to_uint res)%r/ae_scale%r -
      ae_polynomial ((W64.to_uint w)%r/ae_scale%r) <= 3%r/ae_scale%r].
proof.
  have hi := ae_approx_exp_unsigned w.
  have he := ae_rounding_error3 (W64.to_uint w).
  conseq (approx_exp_correct w) => />; smt().
qed.

lemma ae_internal_total (w : W64.t) :
  phoare [SamplerTarget.M._approx_exp : x=w /\ ae_domain (W64.to_uint w) ==>
    W64.to_uint res = ae_integer (W64.to_uint w) /\
    0%r <= (W64.to_uint res)%r/ae_scale%r -
      ae_polynomial ((W64.to_uint w)%r/ae_scale%r) <= 3%r/ae_scale%r] = 1%r.
proof. by conseq approx_exp_lossless (ae_internal_correct w). qed.

lemma ae_jazz_correct (w : W64.t) :
  hoare [SamplerTarget.M.approx_exp_jazz : x=w /\ ae_domain (W64.to_uint w) ==>
    W64.to_uint res = ae_integer (W64.to_uint w) /\
    0%r <= (W64.to_uint res)%r/ae_scale%r -
      ae_polynomial ((W64.to_uint w)%r/ae_scale%r) <= 3%r/ae_scale%r].
proof.
  have hi := ae_approx_exp_unsigned w.
  have he := ae_rounding_error3 (W64.to_uint w).
  conseq (approx_exp_jazz_correct w) => />; smt().
qed.

lemma ae_jazz_total (w : W64.t) :
  phoare [SamplerTarget.M.approx_exp_jazz : x=w /\ ae_domain (W64.to_uint w) ==>
    W64.to_uint res = ae_integer (W64.to_uint w) /\
    0%r <= (W64.to_uint res)%r/ae_scale%r -
      ae_polynomial ((W64.to_uint w)%r/ae_scale%r) <= 3%r/ae_scale%r] = 1%r.
proof. by conseq approx_exp_jazz_lossless (ae_jazz_correct w). qed.

lemma ae_signer_correct (w : W64.t) :
  hoare [SigningSamplerBridge.Signer._approx_exp : x=w /\ ae_domain (W64.to_uint w) ==>
    W64.to_uint res = ae_integer (W64.to_uint w) /\
    0%r <= (W64.to_uint res)%r/ae_scale%r -
      ae_polynomial ((W64.to_uint w)%r/ae_scale%r) <= 3%r/ae_scale%r].
proof. by conseq SigningSamplerBridge.signer_approx_exp_equiv (ae_internal_correct w) => /#. qed.

lemma ae_signer_total (w : W64.t) :
  phoare [SigningSamplerBridge.Signer._approx_exp : x=w /\ ae_domain (W64.to_uint w) ==>
    W64.to_uint res = ae_integer (W64.to_uint w) /\
    0%r <= (W64.to_uint res)%r/ae_scale%r -
      ae_polynomial ((W64.to_uint w)%r/ae_scale%r) <= 3%r/ae_scale%r] = 1%r.
proof. by conseq SigningSamplerBridge.signer_approx_exp_equiv (ae_internal_total w) => /#. qed.

lemma ae_sigma_domain (p : BArray26.t) : ae_domain (W64.to_uint (sigma_exp_argument p)).
proof.
  have h0 := sigma_exp_argument_bound p.
  have h3 := sigma_exp_argument_two_thirds p.
  rewrite /ae_domain /ae_scale; smt().
qed.

(* No input-range or intermediate-fit premise remains for the exact argument
   supplied by sigma76 on an arbitrary 26-byte input. *)
lemma ae_sigma_approx_exp_total (p : BArray26.t) :
  phoare [SigningSamplerBridge.Signer._approx_exp : x=sigma_exp_argument p ==>
    W64.to_uint res = ae_integer (W64.to_uint (sigma_exp_argument p)) /\
    0%r <= (W64.to_uint res)%r/ae_scale%r -
      ae_polynomial ((W64.to_uint (sigma_exp_argument p))%r/ae_scale%r) <= 3%r/ae_scale%r] = 1%r.
proof.
  have hd := ae_sigma_domain p.
  by conseq (ae_signer_total (sigma_exp_argument p)) => />.
qed.

(* Every Horner prefix and its next rounded multiplication fit signed64.
   The executable word prefix also decodes to that same integer. *)
lemma ae_intermediate_signed64 x k : ae_domain x =>
  let r = ae_integer_fold x ae_leading (take k ae_tail) in
  W64.min_sint <= r <= W64.max_sint /\
  W64.min_sint <= ae_ceil r x <= W64.max_sint /\
  W64.to_sint (ae_word_fold smulh48_word (W64.of_int x)
    (W64.of_int ae_leading) (take k ae_tail)) = r.
proof.
  move=> hx /=.
  have [hb hq] := ae_intermediate_bounds x k hx.
  have [hf hqf] :
      W64.min_sint <= ae_integer_fold x ae_leading (take k ae_tail) <= W64.max_sint /\
      W64.min_sint <= ae_ceil (ae_integer_fold x ae_leading (take k ae_tail)) x <= W64.max_sint
    by move: hb hq; rewrite /ae_bound; smt().
  have [_ [_ [hhead [hh hc]]]] := ae_coefficient_facts.
  have ht : all ae_coefficient_ok (take k ae_tail).
  + apply List.allP => c hmem.
    have hm := mem_take k ae_tail c hmem.
    move: hc; rewrite List.allP => hc; exact (hc c hm).
  have hleading : -ae_bound <= ae_leading <= ae_bound by smt().
  rewrite (ae_word_integer_fold x (take k ae_tail) ae_leading hx hleading ht)
    W64.to_sintK_small 1:hf.
  smt().
qed.
