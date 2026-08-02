require import AllCore IntDiv List Ring StdOrder Real.

from Jasmin require import JModel_x86.

import RField RealOrder.

require import BArray1024 BArray2048.
require import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule
  KeygenM23RootTableTargetBridge
  KeygenM23SingularFFTButterflyBridge
  KeygenM23SingularFFTBounds
  KeygenM23SingularFFTScheduleBridge
  KeygenM23SingularFFTBlockPrefixBridge
  KeygenM23SingularFFTKPrefixBridge
  KeygenM23SingularFFTStageBridge
  KeygenM23SingularFFTStageBounds
  KeygenM23SingularFFTGlobalTrace
  KeygenM23SingularFFTInitBridge
  KeygenM23SingularFFTSpec
  KeygenMode2ParentTarget.

import
  KeygenM23ComplexReal
  KeygenM23IdealRootDFT
  KeygenM23IdealFFTSchedule
  KeygenM23SingularFFTButterflyBridge
  KeygenM23SingularFFTBounds
  KeygenM23SingularFFTScheduleBridge
  KeygenM23SingularFFTBlockPrefixBridge
  KeygenM23SingularFFTKPrefixBridge
  KeygenM23SingularFFTStageBridge
  KeygenM23SingularFFTStageBounds
  KeygenM23SingularFFTGlobalTrace
  KeygenM23SingularFFTInitBridge.

theory KeygenM23SingularFFTStageErrorBridge.

lemma ideal_root_norm1 (j : int) :
  0 <= j =>
  cnorm2 (ideal_root j) = 1%r.
proof.
move=> hj.
elim/intind: j hj => [|j hj ih].
+ by rewrite /ideal_root C.expr0 cnorm2_one.
rewrite /ideal_root C.exprSr 1:hj cnorm2_mul omega512_norm ih.
ring.
qed.

lemma norm_coordinate_le_one (z : complex) :
  cnorm2 z = 1%r =>
  `|creal z| <= 1%r /\ `|cimag z| <= 1%r.
proof.
move=> hnorm.
have hre0 : 0%r <= creal z * creal z.
+ rewrite -expr2; exact (ge0_sqr (creal z)).
have him0 : 0%r <= cimag z * cimag z.
+ rewrite -expr2; exact (ge0_sqr (cimag z)).
have hre1 : creal z * creal z <= 1%r by
  move: hnorm; rewrite /cnorm2; smt().
have him1 : cimag z * cimag z <= 1%r by
  move: hnorm; rewrite /cnorm2; smt().
rewrite ler_norml.
rewrite ler_norml.
split.
+ have hcases : creal z < -1%r \/ -1%r <= creal z by smt().
  case: hcases => // hlt.
  have hsq : 1%r < creal z * creal z.
  + have hneg : - creal z > 1%r by smt().
    have hpos : 0%r <= 1%r by smt().
    have hmul := ltr_pmul 1%r (-creal z) 1%r (-creal z) hpos hpos hneg hneg.
    have hone : 1%r * 1%r = 1%r by ring.
    have hnegmul : (-creal z) * (-creal z) = creal z * creal z by ring.
    by move: hmul; rewrite hone hnegmul.
  smt().
+ have hcases : creal z <= 1%r \/ 1%r < creal z by smt().
  case: hcases => // hgt.
  have hpos : 0%r <= 1%r by smt().
  have hsq := ltr_pmul 1%r (creal z) 1%r (creal z) hpos hpos hgt hgt.
  smt().
+ have hcases : cimag z < -1%r \/ -1%r <= cimag z by smt().
  case: hcases => // hlt.
  have hsq : 1%r < cimag z * cimag z.
  + have hneg : - cimag z > 1%r by smt().
    have hpos : 0%r <= 1%r by smt().
    have hmul := ltr_pmul 1%r (-cimag z) 1%r (-cimag z) hpos hpos hneg hneg.
    have hone : 1%r * 1%r = 1%r by ring.
    have hnegmul : (-cimag z) * (-cimag z) = cimag z * cimag z by ring.
    by move: hmul; rewrite hone hnegmul.
  smt().
+ have hcases : cimag z <= 1%r \/ 1%r < cimag z by smt().
  case: hcases => // hgt.
  have hpos : 0%r <= 1%r by smt().
  have hsq := ltr_pmul 1%r (cimag z) 1%r (cimag z) hpos hpos hgt hgt.
  smt().
qed.

lemma ideal_root_coordinate_bound1 (j : int) :
  0 <= j =>
  `|creal (ideal_root j)| <= 1%r /\
  `|cimag (ideal_root j)| <= 1%r.
proof.
move=> hj.
exact (norm_coordinate_le_one (ideal_root j) (ideal_root_norm1 j hj)).
qed.

lemma cmul_close_left_bounded
    (err bound : real) (x x' w : complex) :
  0%r <= err =>
  0%r <= bound =>
  cclose err x x' =>
  `|creal w| <= bound =>
  `|cimag w| <= bound =>
  cclose (2%r * bound * err) (cmul x w) (cmul x' w).
proof.
move=> herr hbound hclose hwre hwim.
move: hclose; rewrite /cclose; move=> [hxre hxim].
rewrite /cclose !creal_mul !cimag_mul.
split.
+ have heq :
    (creal x * creal w - cimag x * cimag w) -
    (creal x' * creal w - cimag x' * cimag w) =
    (creal x - creal x') * creal w +
    -((cimag x - cimag x') * cimag w) by ring.
  rewrite heq.
  have hsum :=
    ler_norm_add
      ((creal x - creal x') * creal w)
      (-((cimag x - cimag x') * cimag w)).
  rewrite normrN !normrM in hsum.
  have hp1 :
    `|creal x - creal x'| * `|creal w| <= err * bound.
  + apply ler_pmul.
    + exact (RealOrder.normr_ge0 (creal x - creal x')).
    + exact (RealOrder.normr_ge0 (creal w)).
    + exact hxre.
    + exact hwre.
  have hp2 :
    `|cimag x - cimag x'| * `|cimag w| <= err * bound.
  + apply ler_pmul.
    + exact (RealOrder.normr_ge0 (cimag x - cimag x')).
    + exact (RealOrder.normr_ge0 (cimag w)).
    + exact hxim.
    + exact hwim.
  have hbudget : err * bound + err * bound = 2%r * bound * err by ring.
  smt().
+ have heq :
    (creal x * cimag w + cimag x * creal w) -
    (creal x' * cimag w + cimag x' * creal w) =
    (creal x - creal x') * cimag w +
    (cimag x - cimag x') * creal w by ring.
  rewrite heq.
  have hsum :=
    ler_norm_add
      ((creal x - creal x') * cimag w)
      ((cimag x - cimag x') * creal w).
  rewrite !normrM in hsum.
  have hp1 :
    `|creal x - creal x'| * `|cimag w| <= err * bound.
  + apply ler_pmul.
    + exact (RealOrder.normr_ge0 (creal x - creal x')).
    + exact (RealOrder.normr_ge0 (cimag w)).
    + exact hxre.
    + exact hwim.
  have hp2 :
    `|cimag x - cimag x'| * `|creal w| <= err * bound.
  + apply ler_pmul.
    + exact (RealOrder.normr_ge0 (cimag x - cimag x')).
    + exact (RealOrder.normr_ge0 (creal w)).
    + exact hxim.
    + exact hwre.
  have hbudget : err * bound + err * bound = 2%r * bound * err by ring.
  smt().
qed.

lemma cmul_close_right_bounded
    (eps bound : real) (x w w' : complex) :
  0%r <= eps =>
  0%r <= bound =>
  `|creal x| <= bound =>
  `|cimag x| <= bound =>
  cclose eps w w' =>
  cclose (2%r * bound * eps) (cmul x w) (cmul x w').
proof.
move=> heps hbound hxre hxim hclose.
have h :=
  cmul_close_left_bounded
    eps bound w w' x heps hbound hclose hxre hxim.
rewrite (cmulC w x) (cmulC w' x) in h.
exact h.
qed.

lemma fft_butterfly_exact_even_close
    (data roots : BArray2048.t) (even odd twid : int)
    (eps term_eps : real) (even_target term_target : complex) :
  cclose eps
    (fft_decode_at data even)
    even_target =>
  cclose term_eps
    (fft_butterfly_exact_term_at data roots odd twid)
    term_target =>
  cclose (eps + term_eps)
    (fft_butterfly_exact_even_at data roots even odd twid)
    (cadd even_target term_target).
proof.
move=> heven hterm.
rewrite /fft_butterfly_exact_even_at.
exact
  (cclose_add
    eps term_eps
    (fft_decode_at data even) even_target
    (fft_butterfly_exact_term_at data roots odd twid) term_target
    heven hterm).
qed.

lemma fft_butterfly_exact_odd_close
    (data roots : BArray2048.t) (even odd twid : int)
    (eps term_eps : real) (even_target term_target : complex) :
  cclose eps
    (fft_decode_at data even)
    even_target =>
  cclose term_eps
    (fft_butterfly_exact_term_at data roots odd twid)
    term_target =>
  cclose (eps + term_eps)
    (fft_butterfly_exact_odd_at data roots even odd twid)
    (csub even_target term_target).
proof.
move=> heven hterm.
rewrite /fft_butterfly_exact_odd_at.
exact
  (cclose_sub
    eps term_eps
    (fft_decode_at data even) even_target
    (fft_butterfly_exact_term_at data roots odd twid) term_target
    heven hterm).
qed.

lemma fft_butterfly_even_decode_close_to_target
    (data roots : BArray2048.t) (even odd twid : int)
    (eps term_eps : real) (even_target term_target : complex) :
  0 <= even < 256 =>
  0 <= odd < 256 =>
  0 <= twid < 256 =>
  even <> odd =>
  fft_butterfly_safe_at data roots even odd twid =>
  let output =
    KeygenM23SingularFFTSpec.fft_butterfly
      data roots
      (W64.of_int even) (W64.of_int odd) (W64.of_int twid) in
  cclose eps
    (fft_decode_at data even)
    even_target =>
  cclose term_eps
    (fft_butterfly_exact_term_at data roots odd twid)
    term_target =>
  cclose (1%r / 65536%r + (eps + term_eps))
    (fft_decode_at output even)
    (cadd even_target term_target).
proof.
move=> heven hodd htwid hneq hsafe /= hclose_even hclose_term.
have hmachine :=
  fft_butterfly_decode_close
    data roots even odd twid
    heven hodd htwid hneq hsafe.
move: hmachine => [hmachine _].
have hexact :=
  fft_butterfly_exact_even_close
    data roots even odd twid eps term_eps
    even_target term_target
    hclose_even hclose_term.
exact
  (cclose_triangle
    (1%r / 65536%r)
    (eps + term_eps)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_butterfly
        data roots
        (W64.of_int even) (W64.of_int odd) (W64.of_int twid))
      even)
    (fft_butterfly_exact_even_at data roots even odd twid)
    (cadd even_target term_target)
    hmachine hexact).
qed.

lemma fft_butterfly_odd_decode_close_to_target
    (data roots : BArray2048.t) (even odd twid : int)
    (eps term_eps : real) (even_target term_target : complex) :
  0 <= even < 256 =>
  0 <= odd < 256 =>
  0 <= twid < 256 =>
  even <> odd =>
  fft_butterfly_safe_at data roots even odd twid =>
  let output =
    KeygenM23SingularFFTSpec.fft_butterfly
      data roots
      (W64.of_int even) (W64.of_int odd) (W64.of_int twid) in
  cclose eps
    (fft_decode_at data even)
    even_target =>
  cclose term_eps
    (fft_butterfly_exact_term_at data roots odd twid)
    term_target =>
  cclose (1%r / 65536%r + (eps + term_eps))
    (fft_decode_at output odd)
    (csub even_target term_target).
proof.
move=> heven hodd htwid hneq hsafe /= hclose_even hclose_term.
have hmachine :=
  fft_butterfly_decode_close
    data roots even odd twid
    heven hodd htwid hneq hsafe.
move: hmachine => [_ hmachine].
have hexact :=
  fft_butterfly_exact_odd_close
    data roots even odd twid eps term_eps
    even_target term_target
    hclose_even hclose_term.
exact
  (cclose_triangle
    (1%r / 65536%r)
    (eps + term_eps)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_butterfly
        data roots
        (W64.of_int even) (W64.of_int odd) (W64.of_int twid))
      odd)
    (fft_butterfly_exact_odd_at data roots even odd twid)
    (csub even_target term_target)
    hmachine hexact).
qed.

lemma fft_schedule_params_values
    (round : int) (m md2 stride : W64.t) :
  0 <= round < 8 =>
  fft_schedule_params_at round m md2 stride =>
  W64.to_uint m = 2 ^ (round + 1) /\
  W64.to_uint md2 = 2 ^ round /\
  W64.to_uint stride = 2 ^ (8 - round).
proof.
rewrite /fft_schedule_params_at.
move=> hround hstate.
case: hstate => [hs0|hrest0].
+ by move: hs0 => />.
case: hrest0 => [hs1|hrest1].
+ by move: hs1 => />.
case: hrest1 => [hs2|hrest2].
+ by move: hs2 => />.
case: hrest2 => [hs3|hrest3].
+ by move: hs3 => />.
case: hrest3 => [hs4|hrest4].
+ by move: hs4 => />.
case: hrest4 => [hs5|hrest5].
+ by move: hs5 => />.
case: hrest5 => [hs6|hrest6].
+ by move: hs6 => />.
case: hrest6 => [hs7|hs8].
+ by move: hs7 => />.
by move: hs8 hround => />.
qed.

lemma fft_stage_decode_at_lowE
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (block k : int) :
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  0 <= k < W64.to_uint md2 =>
  fft_stage_decode_at data roots m md2 stride
    (fft_k_even_index (fft_block_start_word m block) k) =
  fft_butterfly_even_decode_at
    (KeygenM23SingularFFTSpec.fft_k_prefix
      (KeygenM23SingularFFTSpec.fft_blocks_prefix
        data roots m md2 stride block)
      roots (fft_block_start_word m block) md2 stride k)
    roots
    (fft_k_even_index (fft_block_start_word m block) k)
    (fft_k_odd_index (fft_block_start_word m block) md2 k)
    (fft_k_twid_index stride k).
proof.
move=> hstage hblock hk.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
have hwfk :=
  fft_blocks_schedule_wf_local
    m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    block hwf hblock.
have hj :=
  fft_k_even_index_bounds
    (fft_block_start_word m block) md2 stride
    (W64.to_uint md2) k hwfk hk.
have hjrange :=
  fft_stage_current_block_even_range
    m md2 stride block k hstage hblock hk.
have howner :
  fft_stage_owner_block m
    (fft_k_even_index (fft_block_start_word m block) k) = block.
+ apply eq_sym.
  exact
    (fft_stage_owner_block_unique
      m md2 stride block
      (fft_k_even_index (fft_block_start_word m block) k)
      hstage hj hblock hjrange).
rewrite /fft_stage_decode_at /= howner.
rewrite /fft_k_prefix_decode_at /fft_k_even_index.
rewrite ifT 1:/#.
have hkE :
  W64.to_uint (fft_block_start_word m block) + k -
  W64.to_uint (fft_block_start_word m block) = k by ring.
rewrite hkE /fft_k_odd_index /fft_k_even_index /fft_k_twid_index.
done.
qed.

lemma fft_stage_decode_at_highE
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (block k : int) :
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  0 <= k < W64.to_uint md2 =>
  fft_stage_decode_at data roots m md2 stride
    (fft_k_odd_index (fft_block_start_word m block) md2 k) =
  fft_butterfly_odd_decode_at
    (KeygenM23SingularFFTSpec.fft_k_prefix
      (KeygenM23SingularFFTSpec.fft_blocks_prefix
        data roots m md2 stride block)
      roots (fft_block_start_word m block) md2 stride k)
    roots
    (fft_k_even_index (fft_block_start_word m block) k)
    (fft_k_odd_index (fft_block_start_word m block) md2 k)
    (fft_k_twid_index stride k).
proof.
move=> hstage hblock hk.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
have hwfk :=
  fft_blocks_schedule_wf_local
    m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    block hwf hblock.
have hj :=
  fft_k_odd_index_bounds
    (fft_block_start_word m block) md2 stride
    (W64.to_uint md2) k hwfk hk.
have hjrange :=
  fft_stage_current_block_odd_range
    m md2 stride block k hstage hblock hk.
have howner :
  fft_stage_owner_block m
    (fft_k_odd_index (fft_block_start_word m block) md2 k) = block.
+ apply eq_sym.
  exact
    (fft_stage_owner_block_unique
      m md2 stride block
      (fft_k_odd_index (fft_block_start_word m block) md2 k)
      hstage hj hblock hjrange).
rewrite /fft_stage_decode_at /= howner.
rewrite /fft_k_prefix_decode_at /fft_k_odd_index /fft_k_even_index.
rewrite ifF 1:/# ifT 1:/#.
have hkE :
  W64.to_uint (fft_block_start_word m block) + k + W64.to_uint md2 -
  (W64.to_uint (fft_block_start_word m block) + W64.to_uint md2) = k by ring.
have hevenE :
  W64.to_uint (fft_block_start_word m block) + k + W64.to_uint md2 -
  W64.to_uint md2 =
  W64.to_uint (fft_block_start_word m block) + k by ring.
rewrite hkE hevenE /fft_k_twid_index.
done.
qed.

lemma fft_k_schedule_wf_mono
    (n md2 stride : W64.t) (small large : int) :
  0 <= small <= large =>
  fft_k_schedule_wf n md2 stride large =>
  fft_k_schedule_wf n md2 stride small.
proof.
rewrite /fft_k_schedule_wf.
smt().
qed.

lemma fft_k_prefix_safe_mono
    (data roots : BArray2048.t) (n md2 stride : W64.t)
    (small large : int) :
  0 <= small <= large =>
  fft_k_prefix_safe data roots n md2 stride large =>
  fft_k_prefix_safe data roots n md2 stride small.
proof.
rewrite /fft_k_prefix_safe.
smt().
qed.

lemma fft_blocks_prefix_safe_mono
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (small large : int) :
  0 <= small <= large =>
  fft_blocks_prefix_safe data roots m md2 stride large =>
  fft_blocks_prefix_safe data roots m md2 stride small.
proof.
rewrite /fft_blocks_prefix_safe.
smt().
qed.

lemma fft_stage_owner_pair_decode
    (data roots : BArray2048.t) (m md2 stride : W64.t)
    (block k : int) :
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  0 <= k < W64.to_uint md2 =>
  fft_stage_safe data roots m md2 stride =>
  let block_data =
    KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block in
  let pair_data =
    KeygenM23SingularFFTSpec.fft_k_prefix
      block_data roots (fft_block_start_word m block)
      md2 stride k in
  let even = fft_k_even_index (fft_block_start_word m block) k in
  let odd = fft_k_odd_index (fft_block_start_word m block) md2 k in
  fft_decode_at pair_data even = fft_decode_at data even /\
  fft_decode_at pair_data odd = fft_decode_at data odd.
proof.
move=> hstage hblock hk hsafe /=.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
have hwfk :=
  fft_blocks_schedule_wf_local
    m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    block hwf hblock.
have hwfk_k :=
  fft_k_schedule_wf_mono
    (fft_block_start_word m block) md2 stride
    k (W64.to_uint md2) _ hwfk.
+ smt().
have hwfk_kS :=
  fft_k_schedule_wf_mono
    (fft_block_start_word m block) md2 stride
    (k + 1) (W64.to_uint md2) _ hwfk.
+ smt().
have heven :=
  fft_k_even_index_bounds
    (fft_block_start_word m block) md2 stride
    (W64.to_uint md2) k hwfk hk.
have hodd :=
  fft_k_odd_index_bounds
    (fft_block_start_word m block) md2 stride
    (W64.to_uint md2) k hwfk hk.
have howner_even :
  fft_stage_owner_block m
    (fft_k_even_index (fft_block_start_word m block) k) = block.
+ apply eq_sym.
  exact
    (fft_stage_owner_block_unique
      m md2 stride block
      (fft_k_even_index (fft_block_start_word m block) k)
      hstage heven hblock
      (fft_stage_current_block_even_range
        m md2 stride block k hstage hblock hk)).
have howner_odd :
  fft_stage_owner_block m
    (fft_k_odd_index (fft_block_start_word m block) md2 k) = block.
+ apply eq_sym.
  exact
    (fft_stage_owner_block_unique
      m md2 stride block
      (fft_k_odd_index (fft_block_start_word m block) md2 k)
      hstage hodd hblock
      (fft_stage_current_block_odd_range
        m md2 stride block k hstage hblock hk)).
have hsafe_blocks :
  fft_blocks_prefix_safe data roots m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m) by
  exact hsafe.
have hsafe_blocks_block :=
  fft_blocks_prefix_safe_mono
    data roots m md2 stride block
    (KeygenM23SingularFFTSpec.fft_block_count m)
    _ hsafe_blocks.
+ smt().
have hsafe_block :
  fft_k_prefix_safe
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    roots (fft_block_start_word m block) md2 stride
    (W64.to_uint md2).
+ exact (hsafe_blocks block hblock).
have hsafe_k :=
  fft_k_prefix_safe_mono
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    roots (fft_block_start_word m block) md2 stride
    k (W64.to_uint md2) _ hsafe_block.
+ smt().
have hpair_even :=
  fft_k_prefix_decode
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    roots (fft_block_start_word m block) md2 stride
    k (fft_k_even_index (fft_block_start_word m block) k)
    hwfk_k heven hsafe_k.
have hpending_even :=
  fft_k_prefix_decode_at_pending_even
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    roots (fft_block_start_word m block) md2 stride k _ hwfk_kS.
+ smt().
have hpair_even_base :
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_k_prefix
      (KeygenM23SingularFFTSpec.fft_blocks_prefix
        data roots m md2 stride block)
      roots (fft_block_start_word m block) md2 stride k)
    (fft_k_even_index (fft_block_start_word m block) k) =
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    (fft_k_even_index (fft_block_start_word m block) k) by
  rewrite hpair_even hpending_even.
have hpair_odd :=
  fft_k_prefix_decode
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    roots (fft_block_start_word m block) md2 stride
    k (fft_k_odd_index (fft_block_start_word m block) md2 k)
    hwfk_k hodd hsafe_k.
have hpending_odd :=
  fft_k_prefix_decode_at_pending_odd
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    roots (fft_block_start_word m block) md2 stride k _ hwfk_kS.
+ smt().
have hpair_odd_base :
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_k_prefix
      (KeygenM23SingularFFTSpec.fft_blocks_prefix
        data roots m md2 stride block)
      roots (fft_block_start_word m block) md2 stride k)
    (fft_k_odd_index (fft_block_start_word m block) md2 k) =
  fft_decode_at
    (KeygenM23SingularFFTSpec.fft_blocks_prefix
      data roots m md2 stride block)
    (fft_k_odd_index (fft_block_start_word m block) md2 k) by
  rewrite hpair_odd hpending_odd.
have hblock_even :=
  fft_blocks_prefix_pending_decode
    data roots m md2 stride block
    (fft_k_even_index (fft_block_start_word m block) k)
    hstage heven _ hsafe_blocks_block.
+ rewrite howner_even; smt().
have hblock_odd :=
  fft_blocks_prefix_pending_decode
    data roots m md2 stride block
    (fft_k_odd_index (fft_block_start_word m block) md2 k)
    hstage hodd _ hsafe_blocks_block.
+ rewrite howner_odd; smt().
split.
+ by rewrite hpair_even_base hblock_even.
by rewrite hpair_odd_base hblock_odd.
qed.

lemma fft_decode_at_coordinate_bound
    (data : BArray2048.t) (i raw : int) :
  0 <= raw =>
  fft_word_bound_at data i raw =>
  `|creal (fft_decode_at data i)| <= raw%r / 65536%r /\
  `|cimag (fft_decode_at data i)| <= raw%r / 65536%r.
proof.
move=> hraw hword.
move: hword; rewrite /fft_word_bound_at; move=> [hre him].
rewrite /fft_decode_at /q16_decode_word /q16_decode_int
        /creal /cimag /= !ler_norml.
split.
+ split; smt().
+ split; smt().
qed.

lemma fft_stage_owner_indices_values
    (round : int) (m md2 stride : W64.t) (block k : int) :
  0 <= round < 8 =>
  fft_schedule_params_at round m md2 stride =>
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  W64.to_uint (fft_block_start_word m block) =
    block * 2 ^ (round + 1) /\
  fft_k_even_index (fft_block_start_word m block) k =
    (2 * block) * 2 ^ round + k /\
  fft_k_odd_index (fft_block_start_word m block) md2 k =
    (2 * block + 1) * 2 ^ round + k /\
  fft_k_twid_index stride k = k * 2 ^ (8 - round).
proof.
move=> hround hparams hstage hblock.
have [hm [hmd2 hstride]] :=
  fft_schedule_params_values round m md2 stride hround hparams.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
have [hstart0 hend] :=
  fft_block_start_bounds
    m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    block hwf hblock.
have hstartw :
  W64.to_uint (fft_block_start_word m block) = fft_block_start m block.
+ apply fft_block_start_word_uint.
  split.
  + exact hstart0.
  have hmod : 256 < W64.modulus by trivial.
  smt().
have hpow : 2 ^ (round + 1) = 2 * 2 ^ round by
  rewrite pow2S 1:/#.
rewrite /fft_block_start in hstartw.
rewrite /fft_k_even_index /fft_k_odd_index /fft_k_twid_index.
rewrite hstartw hm hmd2 hstride hpow.
split.
+ ring.
rewrite /fft_k_even_index hstartw hm hpow.
split.
+ ring.
split.
+ ring.
+ ring.
qed.

lemma fft_stage_owner_even_index_value
    (round : int) (m md2 stride : W64.t) (block k : int) :
  0 <= round < 8 =>
  fft_schedule_params_at round m md2 stride =>
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  fft_k_even_index (fft_block_start_word m block) k =
    (2 * block) * 2 ^ round + k.
proof.
move=> hround hparams hstage hblock.
have [_ [heven _]] :=
  fft_stage_owner_indices_values
    round m md2 stride block k hround hparams hstage hblock.
exact heven.
qed.

lemma fft_stage_owner_odd_index_value
    (round : int) (m md2 stride : W64.t) (block k : int) :
  0 <= round < 8 =>
  fft_schedule_params_at round m md2 stride =>
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  fft_k_odd_index (fft_block_start_word m block) md2 k =
    (2 * block + 1) * 2 ^ round + k.
proof.
move=> hround hparams hstage hblock.
have [_ [_ [hodd _]]] :=
  fft_stage_owner_indices_values
    round m md2 stride block k hround hparams hstage hblock.
exact hodd.
qed.

lemma actual_fft_twiddle_close (round k : int) :
  0 <= round < 8 =>
  0 <= k < 2 ^ round =>
  cclose (1%r / 131072%r)
    (fft_decode_at
      KeygenMode2ParentTarget.jfft_roots
      (k * 2 ^ (8 - round)))
    (ideal_twiddle round k).
proof.
move=> hround hk.
have hi : 0 <= k * 2 ^ (8 - round) < 256.
+ have hs : round \in range 0 9 by rewrite mem_range; smt().
  have hp := pow2_stage_product round hs.
  smt().
have h := actual_root_decode_close (k * 2 ^ (8 - round)) hi.
rewrite /fft_root_decode_at in h.
rewrite /ideal_twiddle.
have heq : 2 ^ (8 - round) * k = k * 2 ^ (8 - round) by ring.
rewrite heq.
exact h.
qed.

lemma fft_root_error_budgetE (round : int) :
  2%r * ((fft_round_word_bound round)%r / 65536%r) *
    (1%r / 131072%r) =
  (2 * 3 ^ round)%r / 65536%r.
proof.
rewrite /fft_round_word_bound fromintM.
field; trivial.
qed.

lemma cmul_input_error_budgetE (eps : real) :
  2%r * 1%r * eps = 2%r * eps.
proof. ring. qed.

lemma fft_butterfly_even_observer_close_to_target
    (data roots : BArray2048.t) (even odd twid : int)
    (eps term_eps : real) (even_target term_target : complex) :
  cclose eps (fft_decode_at data even) even_target =>
  cclose term_eps
    (fft_butterfly_exact_term_at data roots odd twid)
    term_target =>
  cclose (eps + (1%r / 65536%r + term_eps))
    (fft_butterfly_even_decode_at data roots even odd twid)
    (cadd even_target term_target).
proof.
move=> heven hterm.
have hround := fft_butterfly_term_rounding_close data roots odd twid.
have hterm_total :=
  cclose_triangle
    (1%r / 65536%r) term_eps
    (fft_butterfly_term_decode_at data roots odd twid)
    (fft_butterfly_exact_term_at data roots odd twid)
    term_target hround hterm.
rewrite /fft_butterfly_even_decode_at.
exact
  (cclose_add
    eps (1%r / 65536%r + term_eps)
    (fft_decode_at data even) even_target
    (fft_butterfly_term_decode_at data roots odd twid) term_target
    heven hterm_total).
qed.

lemma fft_butterfly_odd_observer_close_to_target
    (data roots : BArray2048.t) (even odd twid : int)
    (eps term_eps : real) (even_target term_target : complex) :
  cclose eps (fft_decode_at data even) even_target =>
  cclose term_eps
    (fft_butterfly_exact_term_at data roots odd twid)
    term_target =>
  cclose (eps + (1%r / 65536%r + term_eps))
    (fft_butterfly_odd_decode_at data roots even odd twid)
    (csub even_target term_target).
proof.
move=> heven hterm.
have hround := fft_butterfly_term_rounding_close data roots odd twid.
have hterm_total :=
  cclose_triangle
    (1%r / 65536%r) term_eps
    (fft_butterfly_term_decode_at data roots odd twid)
    (fft_butterfly_exact_term_at data roots odd twid)
    term_target hround hterm.
rewrite /fft_butterfly_odd_decode_at.
exact
  (cclose_sub
    eps (1%r / 65536%r + term_eps)
    (fft_decode_at data even) even_target
    (fft_butterfly_term_decode_at data roots odd twid) term_target
    heven hterm_total).
qed.

lemma fft_stage_error_budgetE (round : int) (eps : real) :
  eps +
    (1%r / 65536%r +
      ((2 * 3 ^ round)%r / 65536%r + 2%r * eps)) =
  3%r * eps + (2 * 3 ^ round + 1)%r / 65536%r.
proof.
rewrite fromintD fromintM.
field; trivial.
qed.

lemma actual_fft_ideal_stage_lowE
    (xp : BArray1024.t) (round block k : int) :
  0 <= round < 8 =>
  k \in range 0 (2 ^ round) =>
  ideal_schedule_prefix
    (actual_fft_ideal_input xp)
    (round + 1)
    (block * 2 ^ (round + 1) + k) =
  cadd
    (ideal_schedule_prefix
      (actual_fft_ideal_input xp)
      round
      ((2 * block) * 2 ^ round + k))
    (cmul
      (ideal_twiddle round k)
      (ideal_schedule_prefix
        (actual_fft_ideal_input xp)
        round
        ((2 * block + 1) * 2 ^ round + k))).
proof.
move=> hround hk.
have hround0 : 0 <= round by smt().
rewrite ideal_schedule_prefixS 1:hround0.
exact
  (ideal_stage_lowE
    (ideal_schedule_prefix (actual_fft_ideal_input xp) round)
    round block k hround0 hk).
qed.

lemma actual_fft_ideal_stage_highE
    (xp : BArray1024.t) (round block k : int) :
  0 <= round < 8 =>
  k \in range 0 (2 ^ round) =>
  ideal_schedule_prefix
    (actual_fft_ideal_input xp)
    (round + 1)
    (block * 2 ^ (round + 1) + (2 ^ round + k)) =
  csub
    (ideal_schedule_prefix
      (actual_fft_ideal_input xp)
      round
      ((2 * block) * 2 ^ round + k))
    (cmul
      (ideal_twiddle round k)
      (ideal_schedule_prefix
        (actual_fft_ideal_input xp)
        round
        ((2 * block + 1) * 2 ^ round + k))).
proof.
move=> hround hk.
have hround0 : 0 <= round by smt().
rewrite ideal_schedule_prefixS 1:hround0.
exact
  (ideal_stage_highE
    (ideal_schedule_prefix (actual_fft_ideal_input xp) round)
    round block k hround0 hk).
qed.

lemma actual_fft_owner_term_close
    (data : BArray2048.t) (target : cvector)
    (round : int) (m md2 stride : W64.t)
    (block k : int) (eps : real) :
  0 <= round < 8 =>
  fft_schedule_params_at round m md2 stride =>
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  0 <= k < 2 ^ round =>
  fft_stage_safe
    data KeygenMode2ParentTarget.jfft_roots m md2 stride =>
  fft_word_bound data (fft_round_word_bound round) =>
  (forall i, 0 <= i < 256 =>
    cclose eps (fft_decode_at data i) (target i)) =>
  let pair_data =
    KeygenM23SingularFFTSpec.fft_k_prefix
      (KeygenM23SingularFFTSpec.fft_blocks_prefix
        data KeygenMode2ParentTarget.jfft_roots
        m md2 stride block)
      KeygenMode2ParentTarget.jfft_roots
      (fft_block_start_word m block) md2 stride k in
  let odd =
    fft_k_odd_index (fft_block_start_word m block) md2 k in
  let twid = fft_k_twid_index stride k in
  cclose
    ((2 * 3 ^ round)%r / 65536%r + 2%r * eps)
    (fft_butterfly_exact_term_at
      pair_data KeygenMode2ParentTarget.jfft_roots odd twid)
    (cmul
      (ideal_twiddle round k)
      (target ((2 * block + 1) * 2 ^ round + k))).
proof.
move=> hround hparams hstage hblock hk hsafe hword hclose /=.
have [hm [hmd2 hstride]] :=
  fft_schedule_params_values round m md2 stride hround hparams.
have [hstart [heven_index [hodd_index htwid_index]]] :=
  fft_stage_owner_indices_values
    round m md2 stride block k
    hround hparams hstage hblock.
have hk_md2 : 0 <= k < W64.to_uint md2 by smt().
have [hpair_even hpair_odd] :=
  fft_stage_owner_pair_decode
    data KeygenMode2ParentTarget.jfft_roots
    m md2 stride block k hstage hblock hk_md2 hsafe.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
have hwfk :=
  fft_blocks_schedule_wf_local
    m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    block hwf hblock.
have hodd_range :=
  fft_k_odd_index_bounds
    (fft_block_start_word m block) md2 stride
    (W64.to_uint md2) k hwfk hk_md2.
have hraw := fft_round_word_bound_exec round hround.
have hword_odd :=
  fft_word_bound_at_global
    data
    (fft_k_odd_index (fft_block_start_word m block) md2 k)
    (fft_round_word_bound round)
    hodd_range hword.
have [hodd_re hodd_im] :=
  fft_decode_at_coordinate_bound
    data
    (fft_k_odd_index (fft_block_start_word m block) md2 k)
    (fft_round_word_bound round)
    _ hword_odd.
+ smt().
have hpair_re :
  `|creal
      (fft_decode_at
        (KeygenM23SingularFFTSpec.fft_k_prefix
          (KeygenM23SingularFFTSpec.fft_blocks_prefix
            data KeygenMode2ParentTarget.jfft_roots
            m md2 stride block)
          KeygenMode2ParentTarget.jfft_roots
          (fft_block_start_word m block) md2 stride k)
        (fft_k_odd_index (fft_block_start_word m block) md2 k))| <=
  (fft_round_word_bound round)%r / 65536%r by
  rewrite hpair_odd; exact hodd_re.
have hpair_im :
  `|cimag
      (fft_decode_at
        (KeygenM23SingularFFTSpec.fft_k_prefix
          (KeygenM23SingularFFTSpec.fft_blocks_prefix
            data KeygenMode2ParentTarget.jfft_roots
            m md2 stride block)
          KeygenMode2ParentTarget.jfft_roots
          (fft_block_start_word m block) md2 stride k)
        (fft_k_odd_index (fft_block_start_word m block) md2 k))| <=
  (fft_round_word_bound round)%r / 65536%r by
  rewrite hpair_odd; exact hodd_im.
have htwiddle := actual_fft_twiddle_close round k hround hk.
have htwiddle_at :
  cclose (1%r / 131072%r)
    (fft_decode_at
      KeygenMode2ParentTarget.jfft_roots
      (fft_k_twid_index stride k))
    (ideal_twiddle round k) by
  rewrite htwid_index; exact htwiddle.
have hroot_err_nonneg : 0%r <= 1%r / 131072%r by
  apply divr_ge0; smt().
have hmachine_bound_nonneg :
  0%r <= (fft_round_word_bound round)%r / 65536%r by
  apply divr_ge0; smt().
have hroot_budget0 :=
  cmul_close_left_bounded
    (1%r / 131072%r)
    ((fft_round_word_bound round)%r / 65536%r)
    (fft_decode_at
      KeygenMode2ParentTarget.jfft_roots
      (fft_k_twid_index stride k))
    (ideal_twiddle round k)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_k_prefix
        (KeygenM23SingularFFTSpec.fft_blocks_prefix
          data KeygenMode2ParentTarget.jfft_roots
          m md2 stride block)
        KeygenMode2ParentTarget.jfft_roots
        (fft_block_start_word m block) md2 stride k)
      (fft_k_odd_index (fft_block_start_word m block) md2 k))
    hroot_err_nonneg hmachine_bound_nonneg
    htwiddle_at hpair_re hpair_im.
rewrite (fft_root_error_budgetE round) in hroot_budget0.
have hinput0 :=
  hclose
    (fft_k_odd_index (fft_block_start_word m block) md2 k)
    hodd_range.
have heps : 0%r <= eps by
  exact
    (cclose_ge0
      eps
      (fft_decode_at data
        (fft_k_odd_index (fft_block_start_word m block) md2 k))
      (target
        (fft_k_odd_index (fft_block_start_word m block) md2 k))
      hinput0).
have hinput :
  cclose eps
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_k_prefix
        (KeygenM23SingularFFTSpec.fft_blocks_prefix
          data KeygenMode2ParentTarget.jfft_roots
          m md2 stride block)
        KeygenMode2ParentTarget.jfft_roots
        (fft_block_start_word m block) md2 stride k)
      (fft_k_odd_index (fft_block_start_word m block) md2 k))
    (target ((2 * block + 1) * 2 ^ round + k)).
+ rewrite hpair_odd.
  rewrite -hodd_index.
  exact hinput0.
have hideal_pow0 : 0 <= 2 ^ (8 - round) by
  apply IntOrder.expr_ge0; smt().
have hk0 : 0 <= k by smt().
have hideal_index0 : 0 <= 2 ^ (8 - round) * k by
  exact
    (IntOrder.mulr_ge0
      (2 ^ (8 - round)) k hideal_pow0 hk0).
have [hideal_re hideal_im] :=
  ideal_root_coordinate_bound1
    (2 ^ (8 - round) * k) hideal_index0.
rewrite /ideal_twiddle in hideal_re.
rewrite /ideal_twiddle in hideal_im.
have hone0 : 0%r <= 1%r by smt().
have hinput_budget0 :=
  cmul_close_right_bounded
    eps 1%r (ideal_twiddle round k)
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_k_prefix
        (KeygenM23SingularFFTSpec.fft_blocks_prefix
          data KeygenMode2ParentTarget.jfft_roots
          m md2 stride block)
        KeygenMode2ParentTarget.jfft_roots
        (fft_block_start_word m block) md2 stride k)
      (fft_k_odd_index (fft_block_start_word m block) md2 k))
    (target ((2 * block + 1) * 2 ^ round + k))
    heps hone0 hideal_re hideal_im hinput.
rewrite (cmul_input_error_budgetE eps) in hinput_budget0.
rewrite /fft_butterfly_exact_term_at.
exact
  (cclose_triangle
    ((2 * 3 ^ round)%r / 65536%r)
    (2%r * eps)
    (cmul
      (fft_decode_at KeygenMode2ParentTarget.jfft_roots
        (fft_k_twid_index stride k))
      (fft_decode_at
        (KeygenM23SingularFFTSpec.fft_k_prefix
          (KeygenM23SingularFFTSpec.fft_blocks_prefix
            data KeygenMode2ParentTarget.jfft_roots
            m md2 stride block)
          KeygenMode2ParentTarget.jfft_roots
          (fft_block_start_word m block) md2 stride k)
        (fft_k_odd_index (fft_block_start_word m block) md2 k)))
    (cmul
      (ideal_twiddle round k)
      (fft_decode_at
        (KeygenM23SingularFFTSpec.fft_k_prefix
          (KeygenM23SingularFFTSpec.fft_blocks_prefix
            data KeygenMode2ParentTarget.jfft_roots
            m md2 stride block)
          KeygenMode2ParentTarget.jfft_roots
          (fft_block_start_word m block) md2 stride k)
        (fft_k_odd_index (fft_block_start_word m block) md2 k)))
    (cmul
      (ideal_twiddle round k)
      (target ((2 * block + 1) * 2 ^ round + k)))
    hroot_budget0 hinput_budget0).
qed.

lemma actual_fft_stage_low_close
    (data : BArray2048.t) (target : cvector)
    (round : int) (m md2 stride : W64.t)
    (block k : int) (eps : real) :
  0 <= round < 8 =>
  fft_schedule_params_at round m md2 stride =>
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  0 <= k < 2 ^ round =>
  fft_stage_safe
    data KeygenMode2ParentTarget.jfft_roots m md2 stride =>
  fft_word_bound data (fft_round_word_bound round) =>
  (forall i, 0 <= i < 256 =>
    cclose eps (fft_decode_at data i) (target i)) =>
  cclose
    (3%r * eps + (2 * 3 ^ round + 1)%r / 65536%r)
    (fft_stage_decode_at
      data KeygenMode2ParentTarget.jfft_roots m md2 stride
      (fft_k_even_index (fft_block_start_word m block) k))
    (cadd
      (target ((2 * block) * 2 ^ round + k))
      (cmul
        (ideal_twiddle round k)
        (target ((2 * block + 1) * 2 ^ round + k)))).
proof.
move=> hround hparams hstage hblock hk hsafe hword hclose.
have [hm [hmd2 hstride]] :=
  fft_schedule_params_values round m md2 stride hround hparams.
have hk_md2 : 0 <= k < W64.to_uint md2 by smt().
have [hstart [heven_index [hodd_index htwid_index]]] :=
  fft_stage_owner_indices_values
    round m md2 stride block k
    hround hparams hstage hblock.
have hstageE :=
  fft_stage_decode_at_lowE
    data KeygenMode2ParentTarget.jfft_roots
    m md2 stride block k hstage hblock hk_md2.
have [hpair_even hpair_odd] :=
  fft_stage_owner_pair_decode
    data KeygenMode2ParentTarget.jfft_roots
    m md2 stride block k hstage hblock hk_md2 hsafe.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
have hwfk :=
  fft_blocks_schedule_wf_local
    m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    block hwf hblock.
have heven_range :=
  fft_k_even_index_bounds
    (fft_block_start_word m block) md2 stride
    (W64.to_uint md2) k hwfk hk_md2.
have heven0 :=
  hclose
    (fft_k_even_index (fft_block_start_word m block) k)
    heven_range.
have heven :
  cclose eps
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_k_prefix
        (KeygenM23SingularFFTSpec.fft_blocks_prefix
          data KeygenMode2ParentTarget.jfft_roots
          m md2 stride block)
        KeygenMode2ParentTarget.jfft_roots
        (fft_block_start_word m block) md2 stride k)
      (fft_k_even_index (fft_block_start_word m block) k))
    (target ((2 * block) * 2 ^ round + k)).
+ rewrite hpair_even.
  rewrite -heven_index.
  exact heven0.
have hterm :=
  actual_fft_owner_term_close
    data target round m md2 stride block k eps
    hround hparams hstage hblock hk hsafe hword hclose.
have hout :=
  fft_butterfly_even_observer_close_to_target
    (KeygenM23SingularFFTSpec.fft_k_prefix
      (KeygenM23SingularFFTSpec.fft_blocks_prefix
        data KeygenMode2ParentTarget.jfft_roots
        m md2 stride block)
      KeygenMode2ParentTarget.jfft_roots
      (fft_block_start_word m block) md2 stride k)
    KeygenMode2ParentTarget.jfft_roots
    (fft_k_even_index (fft_block_start_word m block) k)
    (fft_k_odd_index (fft_block_start_word m block) md2 k)
    (fft_k_twid_index stride k)
    eps ((2 * 3 ^ round)%r / 65536%r + 2%r * eps)
    (target ((2 * block) * 2 ^ round + k))
    (cmul
      (ideal_twiddle round k)
      (target ((2 * block + 1) * 2 ^ round + k)))
    heven hterm.
rewrite hstageE.
rewrite -(fft_stage_error_budgetE round eps).
exact hout.
qed.

lemma actual_fft_stage_high_close
    (data : BArray2048.t) (target : cvector)
    (round : int) (m md2 stride : W64.t)
    (block k : int) (eps : real) :
  0 <= round < 8 =>
  fft_schedule_params_at round m md2 stride =>
  fft_stage_schedule m md2 stride =>
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m =>
  0 <= k < 2 ^ round =>
  fft_stage_safe
    data KeygenMode2ParentTarget.jfft_roots m md2 stride =>
  fft_word_bound data (fft_round_word_bound round) =>
  (forall i, 0 <= i < 256 =>
    cclose eps (fft_decode_at data i) (target i)) =>
  cclose
    (3%r * eps + (2 * 3 ^ round + 1)%r / 65536%r)
    (fft_stage_decode_at
      data KeygenMode2ParentTarget.jfft_roots m md2 stride
      (fft_k_odd_index (fft_block_start_word m block) md2 k))
    (csub
      (target ((2 * block) * 2 ^ round + k))
      (cmul
        (ideal_twiddle round k)
        (target ((2 * block + 1) * 2 ^ round + k)))).
proof.
move=> hround hparams hstage hblock hk hsafe hword hclose.
have [hm [hmd2 hstride]] :=
  fft_schedule_params_values round m md2 stride hround hparams.
have hk_md2 : 0 <= k < W64.to_uint md2 by smt().
have [hstart [heven_index [hodd_index htwid_index]]] :=
  fft_stage_owner_indices_values
    round m md2 stride block k
    hround hparams hstage hblock.
have hstageE :=
  fft_stage_decode_at_highE
    data KeygenMode2ParentTarget.jfft_roots
    m md2 stride block k hstage hblock hk_md2.
have [hpair_even hpair_odd] :=
  fft_stage_owner_pair_decode
    data KeygenMode2ParentTarget.jfft_roots
    m md2 stride block k hstage hblock hk_md2 hsafe.
have [hwf _] : fft_stage_schedule m md2 stride by exact hstage.
have hwfk :=
  fft_blocks_schedule_wf_local
    m md2 stride
    (KeygenM23SingularFFTSpec.fft_block_count m)
    block hwf hblock.
have heven_range :=
  fft_k_even_index_bounds
    (fft_block_start_word m block) md2 stride
    (W64.to_uint md2) k hwfk hk_md2.
have heven0 :=
  hclose
    (fft_k_even_index (fft_block_start_word m block) k)
    heven_range.
have heven :
  cclose eps
    (fft_decode_at
      (KeygenM23SingularFFTSpec.fft_k_prefix
        (KeygenM23SingularFFTSpec.fft_blocks_prefix
          data KeygenMode2ParentTarget.jfft_roots
          m md2 stride block)
        KeygenMode2ParentTarget.jfft_roots
        (fft_block_start_word m block) md2 stride k)
      (fft_k_even_index (fft_block_start_word m block) k))
    (target ((2 * block) * 2 ^ round + k)).
+ rewrite hpair_even.
  rewrite -heven_index.
  exact heven0.
have hterm :=
  actual_fft_owner_term_close
    data target round m md2 stride block k eps
    hround hparams hstage hblock hk hsafe hword hclose.
have hout :=
  fft_butterfly_odd_observer_close_to_target
    (KeygenM23SingularFFTSpec.fft_k_prefix
      (KeygenM23SingularFFTSpec.fft_blocks_prefix
        data KeygenMode2ParentTarget.jfft_roots
        m md2 stride block)
      KeygenMode2ParentTarget.jfft_roots
      (fft_block_start_word m block) md2 stride k)
    KeygenMode2ParentTarget.jfft_roots
    (fft_k_even_index (fft_block_start_word m block) k)
    (fft_k_odd_index (fft_block_start_word m block) md2 k)
    (fft_k_twid_index stride k)
    eps ((2 * 3 ^ round)%r / 65536%r + 2%r * eps)
    (target ((2 * block) * 2 ^ round + k))
    (cmul
      (ideal_twiddle round k)
      (target ((2 * block + 1) * 2 ^ round + k)))
    heven hterm.
rewrite hstageE.
rewrite -(fft_stage_error_budgetE round eps).
exact hout.
qed.

lemma fft_owner_low_indexE (round block j : int) :
  0 <= round =>
  (2 * block) * 2 ^ round +
    (j - block * 2 ^ (round + 1)) = j.
proof.
move=> hround.
rewrite pow2S 1:hround.
ring.
qed.

lemma fft_owner_high_indexE (round block j : int) :
  0 <= round =>
  (2 * block + 1) * 2 ^ round +
    (j - block * 2 ^ (round + 1) - 2 ^ round) = j.
proof.
move=> hround.
rewrite pow2S 1:hround.
ring.
qed.

lemma fft_owner_low_output_indexE (round block j : int) :
  block * 2 ^ (round + 1) +
    (j - block * 2 ^ (round + 1)) = j.
proof. ring. qed.

lemma fft_owner_high_output_indexE (round block j : int) :
  block * 2 ^ (round + 1) +
    (2 ^ round +
      (j - block * 2 ^ (round + 1) - 2 ^ round)) = j.
proof. ring. qed.

lemma ideal_stage_lowE_bounds
    (data : cvector) (round block k : int) :
  0 <= round =>
  0 <= k < 2 ^ round =>
  ideal_stage data round (block * 2 ^ (round + 1) + k) =
  cadd
    (data ((2 * block) * 2 ^ round + k))
    (cmul (ideal_twiddle round k)
      (data ((2 * block + 1) * 2 ^ round + k))).
proof.
move=> hround hk.
apply (ideal_stage_lowE data round block k hround).
by rewrite mem_range.
qed.

lemma ideal_stage_highE_bounds
    (data : cvector) (round block k : int) :
  0 <= round =>
  0 <= k < 2 ^ round =>
  ideal_stage data round
    (block * 2 ^ (round + 1) + (2 ^ round + k)) =
  csub
    (data ((2 * block) * 2 ^ round + k))
    (cmul (ideal_twiddle round k)
      (data ((2 * block + 1) * 2 ^ round + k))).
proof.
move=> hround hk.
apply (ideal_stage_highE data round block k hround).
by rewrite mem_range.
qed.

lemma actual_fft_stage_close_at
    (data : BArray2048.t) (target : cvector)
    (round : int) (m md2 stride : W64.t)
    (j : int) (eps : real) :
  0 <= round < 8 =>
  fft_schedule_params_at round m md2 stride =>
  fft_stage_schedule m md2 stride =>
  0 <= j < 256 =>
  fft_stage_safe
    data KeygenMode2ParentTarget.jfft_roots m md2 stride =>
  fft_word_bound data (fft_round_word_bound round) =>
  (forall i, 0 <= i < 256 =>
    cclose eps (fft_decode_at data i) (target i)) =>
  cclose
    (3%r * eps + (2 * 3 ^ round + 1)%r / 65536%r)
    (fft_stage_decode_at
      data KeygenMode2ParentTarget.jfft_roots m md2 stride j)
    (ideal_stage target round j).
proof.
move=> hround hparams hstage hj hsafe hword hclose.
have [hm [hmd2 hstride]] :=
  fft_schedule_params_values round m md2 stride hround hparams.
have hround0 : 0 <= round by smt().
pose block := fft_stage_owner_block m j.
pose offset := j - block * 2 ^ (round + 1).
have hblock :
  0 <= block < KeygenM23SingularFFTSpec.fft_block_count m by
  exact (fft_stage_owner_block_range m md2 stride j hstage hj).
have hhere := fft_stage_owner_block_here m md2 stride j hstage hj.
have hoffset : 0 <= offset < 2 ^ (round + 1).
+ move: hhere.
  rewrite /fft_block_range /fft_block_start /fft_block_end /offset /block hm.
  smt().
case (offset < 2 ^ round) => hlow.
+ have hk : 0 <= offset < 2 ^ round by smt().
  have hstage_close :=
    actual_fft_stage_low_close
      data target round m md2 stride block offset eps
      hround hparams hstage hblock hk hsafe hword hclose.
  rewrite
    (fft_stage_owner_even_index_value
      round m md2 stride block offset
      hround hparams hstage hblock) in hstage_close.
  rewrite
    -(ideal_stage_lowE_bounds
      target round block offset hround0 hk)
    in hstage_close.
  rewrite /offset
    (fft_owner_low_indexE round block j hround0)
    (fft_owner_low_output_indexE round block j)
    in hstage_close.
  exact hstage_close.
+ pose k := offset - 2 ^ round.
  have hk : 0 <= k < 2 ^ round by
    rewrite /k; smt().
  have hstage_close :=
    actual_fft_stage_high_close
      data target round m md2 stride block k eps
      hround hparams hstage hblock hk hsafe hword hclose.
  rewrite
    (fft_stage_owner_odd_index_value
      round m md2 stride block k
      hround hparams hstage hblock) in hstage_close.
  rewrite
    -(ideal_stage_highE_bounds
      target round block k hround0 hk)
    in hstage_close.
  rewrite /k /offset
    (fft_owner_high_indexE round block j hround0)
    (fft_owner_high_output_indexE round block j)
    in hstage_close.
  exact hstage_close.
qed.

end KeygenM23SingularFFTStageErrorBridge.
