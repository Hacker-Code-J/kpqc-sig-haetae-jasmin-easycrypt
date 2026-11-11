require import AllCore IntDiv List Real RealExp Distr DList DProd Finite StdRing StdOrder.
from Jasmin require import JModel_x86.
require import GaussianUniformBytes GaussianPayloadSpec HyperballIidPayloadSpec
  HyperballIidSquareLaw GaussianRenyiSpec GaussianRenyiMoment
  HyperballRenyiPayload HyperballRenyiProduct HyperballRenyiBatch.
import RField RealOrder.

lemma hrbb_signs_finite : is_finite (support (gbc_bytes 32)).
proof.
  rewrite /gbc_bytes; apply hrt_finite_dlist; last trivial.
  rewrite /W8.dword; exact finite_duniform.
qed.

lemma hrbb_block_support (p q : int distr) n : 0<=n =>
  (forall code, code \in p => code \in q) =>
  forall block, block \in hrj_blockd p n => block \in hrj_blockd q n.
proof.
  move=> hn hs; rewrite /hrj_blockd.
  apply hrt_support_product.
  + exact (hrt_support_dlist p q n hn hs).
  by move=> signs hsigns.
qed.

lemma hrbb_source_support (p q : int distr) mode : hip_mode mode =>
  (forall code, code \in p => code \in q) =>
  forall input, input \in hrj_source p mode => input \in hrj_source q mode.
proof.
  move=> hm hs; have [hn _] := hrj_mode_budget mode hm.
  have hs257 := hrbb_block_support p q 257 _ hs; first trivial.
  have hs256 := hrbb_block_support p q 256 _ hs; first trivial.
  have htail := hrt_support_dlist (hrj_blockd p 256) (hrj_blockd q 256)
    (hip_polys mode-2) _ hs256; first smt().
  rewrite /hrj_source; apply hrt_support_product; first exact hs257.
  exact (hrt_support_product _ _ _ _ hs257 htail).
qed.

lemma hrbb_block_renyi order (p q : int distr) n :
  is_lossless p => is_lossless q =>
  is_finite (support p) => is_finite (support q) =>
  (forall code, code \in p => code \in q) => 2<=order => 0<=n =>
  grn_renyi order (hrj_blockd p n) (hrj_blockd q n) = (grn_renyi order p q)^n.
proof.
  move=> hp hq hfp hfq hs ho hn.
  have hlp := dlist_ll p n hp; have hlq := dlist_ll q n hq.
  have hfn_p := hrt_finite_dlist p n hfp hn.
  have hfn_q := hrt_finite_dlist q n hfq hn.
  have hsn := hrt_support_dlist p q n hn hs.
  rewrite /hrj_blockd (hrt_shared_noise order (dlist p n) (dlist q n) (gbc_bytes 32)
    hlp hlq (gbc_bytes_ll 32) hfn_p hfn_q hrbb_signs_finite hsn ho).
  exact (hrt_renyi_dlist order p q n hp hq hfp hfq hs ho hn).
qed.

(* Both 257th payloads remain in the tensor product, including their raw
   squares. The independent sign bytes contribute exactly a factor one. *)
lemma hrbb_source_renyi order (p q : int distr) mode :
  is_lossless p => is_lossless q =>
  is_finite (support p) => is_finite (support q) =>
  (forall code, code \in p => code \in q) => hip_mode mode => 2<=order =>
  grn_renyi order (hrj_source p mode) (hrj_source q mode) =
    (grn_renyi order p q)^(hip_total mode).
proof.
  move=> hp hq hfp hfq hs hm ho.
  have [hcount [_ hbudget]] := hrj_mode_budget mode hm.
  have hn : 0<=hip_polys mode-2 by smt().
  have lp : forall n, is_lossless (hrj_blockd p n) by move=> n; exact (hrj_block_ll p n hp).
  have lq : forall n, is_lossless (hrj_blockd q n) by move=> n; exact (hrj_block_ll q n hq).
  have fp : forall n, 0<=n => is_finite (support (hrj_blockd p n)) by
    move=> n; exact (hrj_block_finite p n hfp).
  have fq : forall n, 0<=n => is_finite (support (hrj_blockd q n)) by
    move=> n; exact (hrj_block_finite q n hfq).
  have hs257 := hrbb_block_support p q 257 _ hs; first trivial.
  have hs256 := hrbb_block_support p q 256 _ hs; first trivial.
  have fp257 := fp 257 _; first trivial.
  have fq257 := fq 257 _; first trivial.
  have fp256 := fp 256 _; first trivial.
  have fq256 := fq 256 _; first trivial.
  pose tp := dlist (hrj_blockd p 256) (hip_polys mode-2).
  pose tq := dlist (hrj_blockd q 256) (hip_polys mode-2).
  have ltp : is_lossless tp by exact (dlist_ll _ _ (lp 256)).
  have ltq : is_lossless tq by exact (dlist_ll _ _ (lq 256)).
  have ftp : is_finite (support tp) by exact (hrt_finite_dlist _ _ fp256 hn).
  have ftq : is_finite (support tq) by exact (hrt_finite_dlist _ _ fq256 hn).
  have hst : forall input, input \in tp => input \in tq by exact (hrt_support_dlist _ _ _ hn hs256).
  have lip : is_lossless (hrj_blockd p 257 `*` tp) by rewrite dprod_ll (lp 257) ltp.
  have liq : is_lossless (hrj_blockd q 257 `*` tq) by rewrite dprod_ll (lq 257) ltq.
  have fip := finite_dprod (hrj_blockd p 257) tp fp257 ftp.
  have fiq := finite_dprod (hrj_blockd q 257) tq fq257 ftq.
  have hsi := hrt_support_product (hrj_blockd p 257) (hrj_blockd q 257) tp tq hs257 hst.
  rewrite /hrj_source -/tp -/tq
    (hrt_renyi_product order (hrj_blockd p 257) (hrj_blockd q 257)
      (hrj_blockd p 257 `*` tp) (hrj_blockd q 257 `*` tq)
      (lp 257) (lq 257) lip liq fp257 fq257 fip fiq hs257 hsi ho)
    (hrt_renyi_product order (hrj_blockd p 257) (hrj_blockd q 257) tp tq
      (lp 257) (lq 257) ltp ltq fp257 fq257 ftp ftq hs257 hst ho)
    /tp /tq
    (hrt_renyi_dlist order (hrj_blockd p 256) (hrj_blockd q 256) (hip_polys mode-2)
      (lp 256) (lq 256) fp256 fq256 hs256 ho hn)
    (hrbb_block_renyi order p q 257 hp hq hfp hfq hs ho _) 1://
    (hrbb_block_renyi order p q 256 hp hq hfp hfq hs ho _) 1://.
  rewrite -exprM -(exprD_nneg (grn_renyi order p q) 257 (256*(hip_polys mode-2))) 1:// 1:/#
    -(exprD_nneg (grn_renyi order p q) 257 (257+256*(hip_polys mode-2))) 1:// 1:/#.
  congr; smt().
qed.

lemma hrbb_source_bound order (p q : int distr) mode :
  is_lossless p => is_lossless q =>
  is_finite (support p) => is_finite (support q) =>
  grn_mass_bounds p q => hip_mode mode => 2<=order<=1024 =>
  grn_renyi order (hrj_source p mode) (hrj_source q mode) <=
    (1%r+grn_epsilon)^(hip_total mode).
proof.
  move=> hp hq hfp hfq hb hm ho.
  have hs := grn_support_inclusion p q hb.
  have horder : 2<=order by smt().
  have [_ [hcount _]] := hrj_mode_budget mode hm.
  have hu := grn_finite_bound order p q hp hq hfp hfq hb ho.
  have hmoment := hrt_moment_ge1 order p q hp hq hfq hs _; first smt().
  have hnonnegative : 0%r<=grn_renyi order p q by
    rewrite /grn_renyi; apply RealExp.rpow_ge0; smt().
  rewrite (hrbb_source_renyi order p q mode hp hq hfp hfq hs hm horder).
  apply hrt_power_mono; smt().
qed.

lemma hrbb_sources_ll p mode :
  is_lossless (hrj_source gpd_accepted mode) /\
  is_lossless (hrj_source (hrp_exact_payload p) mode).
proof.
  have [ha hb] := hrp_outputs_ll p.
  split; [exact (hrj_source_ll _ mode ha) | exact (hrj_source_ll _ mode hb)].
qed.

lemma hrbb_sources_finite p mode : hip_mode mode =>
  is_finite (support (hrj_source gpd_accepted mode)) /\
  is_finite (support (hrj_source (hrp_exact_payload p) mode)).
proof.
  move=> hm; have [ha hb] := hrp_outputs_finite p.
  split; [exact (hrj_source_finite _ mode ha hm) | exact (hrj_source_finite _ mode hb hm)].
qed.

lemma hrbb_source_supports p mode : hip_mode mode =>
  (forall input, input \in hrj_source gpd_accepted mode =>
    input \in hrj_source (hrp_exact_payload p) mode) /\
  (forall input, input \in hrj_source (hrp_exact_payload p) mode =>
    input \in hrj_source gpd_accepted mode).
proof.
  move=> hm; have [hab hba] := hrp_mass_bounds p.
  split.
  + apply (hrbb_source_support gpd_accepted (hrp_exact_payload p) mode hm).
    exact (grn_support_inclusion _ _ hab).
  apply (hrbb_source_support (hrp_exact_payload p) gpd_accepted mode hm).
  exact (grn_support_inclusion _ _ hba).
qed.

lemma hrbb_renyi_bounds p mode order : hip_mode mode => 2<=order<=1024 =>
  grn_renyi order (hrj_source gpd_accepted mode) (hrj_source (hrp_exact_payload p) mode) <=
    (1%r+grn_epsilon)^(hip_total mode) /\
  grn_renyi order (hrj_source (hrp_exact_payload p) mode) (hrj_source gpd_accepted mode) <=
    (1%r+grn_epsilon)^(hip_total mode).
proof.
  move=> hm ho; have [ha hb] := hrp_outputs_ll p.
  have [hfa hfb] := hrp_outputs_finite p; have [hab hba] := hrp_mass_bounds p.
  split.
  + exact (hrbb_source_bound order gpd_accepted (hrp_exact_payload p) mode ha hb hfa hfb hab hm ho).
  exact (hrbb_source_bound order (hrp_exact_payload p) gpd_accepted mode hb ha hfb hfa hba hm ho).
qed.

lemma hrbb_common_bound p mode order : hip_mode mode => 2<=order<=1024 =>
  grn_renyi order (hrj_source gpd_accepted mode) (hrj_source (hrp_exact_payload p) mode) <
    1%r+1%r/72057594037927936%r /\
  grn_renyi order (hrj_source (hrp_exact_payload p) mode) (hrj_source gpd_accepted mode) <
    1%r+1%r/72057594037927936%r.
proof.
  move=> hm ho; have h := hrbb_renyi_bounds p mode order hm ho.
  have [_ [hn _]] := hrj_mode_budget mode hm.
  have hc := hrt_common_bound (hip_total mode) hn; smt().
qed.

lemma hrbb_mode2_bounds p order : 2<=order<=1024 =>
  grn_renyi order (hrj_source gpd_accepted 2) (hrj_source (hrp_exact_payload p) 2) <=
    (1%r+grn_epsilon)^1538 /\
  grn_renyi order (hrj_source (hrp_exact_payload p) 2) (hrj_source gpd_accepted 2) <=
    (1%r+grn_epsilon)^1538.
proof.
  move=> ho; have h := hrbb_renyi_bounds p 2 order _ ho; first by rewrite /hip_mode.
  have [hc _] := hips_mode_totals; by move: h; rewrite hc.
qed.

lemma hrbb_mode3_bounds p order : 2<=order<=1024 =>
  grn_renyi order (hrj_source gpd_accepted 3) (hrj_source (hrp_exact_payload p) 3) <=
    (1%r+grn_epsilon)^2306 /\
  grn_renyi order (hrj_source (hrp_exact_payload p) 3) (hrj_source gpd_accepted 3) <=
    (1%r+grn_epsilon)^2306.
proof.
  move=> ho; have h := hrbb_renyi_bounds p 3 order _ ho; first by rewrite /hip_mode.
  have [_ [hc _]] := hips_mode_totals; by move: h; rewrite hc.
qed.

lemma hrbb_mode5_bounds p order : 2<=order<=1024 =>
  grn_renyi order (hrj_source gpd_accepted 5) (hrj_source (hrp_exact_payload p) 5) <=
    (1%r+grn_epsilon)^2818 /\
  grn_renyi order (hrj_source (hrp_exact_payload p) 5) (hrj_source gpd_accepted 5) <=
    (1%r+grn_epsilon)^2818.
proof.
  move=> ho; have h := hrbb_renyi_bounds p 5 order _ ho; first by rewrite /hip_mode.
  have [_ [_ hc]] := hips_mode_totals; by move: h; rewrite hc.
qed.
