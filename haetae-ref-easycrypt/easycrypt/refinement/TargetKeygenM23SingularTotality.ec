require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenMode2ParentTarget.
require import TargetKeygenM23SingularHelpers.

theory TargetKeygenM23SingularTotality.

module Parent = KeygenMode2ParentTarget.M.

op m23sing_total_fft_outer_state
    (r m md2 stride : W64.t) : bool =
     (r = W64.of_int 1 /\ m = W64.of_int 2 /\
      md2 = W64.of_int 1 /\ stride = W64.of_int 256)
  \/ (r = W64.of_int 2 /\ m = W64.of_int 4 /\
      md2 = W64.of_int 2 /\ stride = W64.of_int 128)
  \/ (r = W64.of_int 3 /\ m = W64.of_int 8 /\
      md2 = W64.of_int 4 /\ stride = W64.of_int 64)
  \/ (r = W64.of_int 4 /\ m = W64.of_int 16 /\
      md2 = W64.of_int 8 /\ stride = W64.of_int 32)
  \/ (r = W64.of_int 5 /\ m = W64.of_int 32 /\
      md2 = W64.of_int 16 /\ stride = W64.of_int 16)
  \/ (r = W64.of_int 6 /\ m = W64.of_int 64 /\
      md2 = W64.of_int 32 /\ stride = W64.of_int 8)
  \/ (r = W64.of_int 7 /\ m = W64.of_int 128 /\
      md2 = W64.of_int 64 /\ stride = W64.of_int 4)
  \/ (r = W64.of_int 8 /\ m = W64.of_int 256 /\
      md2 = W64.of_int 128 /\ stride = W64.of_int 2)
  \/ (r = W64.of_int 9 /\ m = W64.of_int 512 /\
      md2 = W64.of_int 256 /\ stride = W64.of_int 1).

lemma m23sing_total_fft_state_md2_bound r m md2 stride :
  m23sing_total_fft_outer_state r m md2 stride =>
  W64.to_uint md2 <= 256.
proof.
rewrite /m23sing_total_fft_outer_state.
by do 8! (case=> />); auto.
qed.

lemma m23sing_total_fft_state_body_m_bound r m md2 stride :
  m23sing_total_fft_outer_state r m md2 stride =>
  r \ule W64.of_int 8 =>
  1 <= W64.to_uint m <= 256.
proof.
rewrite /m23sing_total_fft_outer_state W64.uleE W64.of_uintK /=.
move=> hstate hr.
case: hstate => [hs1|hrest1].
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
case: hrest6 => [hs7|hrest7].
+ by move: hs7 => />.
case: hrest7 => [hs8|hs9].
+ by move: hs8 => />.
by move: hs9 hr => />.
qed.

lemma m23sing_total_fft_state_block_step_bound r m md2 stride block :
  m23sing_total_fft_outer_state r m md2 stride =>
  r \ule W64.of_int 8 =>
  0 <= block =>
  block * W64.to_uint m < 256 =>
  (block + 1) * W64.to_uint m <= 256.
proof.
rewrite /m23sing_total_fft_outer_state W64.uleE W64.of_uintK /=.
move=> hstate hr hblock hlt.
case: hstate => [hs1|hrest1].
+ move: hs1 => />; smt().
case: hrest1 => [hs2|hrest2].
+ move: hs2 => />; smt().
case: hrest2 => [hs3|hrest3].
+ move: hs3 => />; smt().
case: hrest3 => [hs4|hrest4].
+ move: hs4 => />; smt().
case: hrest4 => [hs5|hrest5].
+ move: hs5 => />; smt().
case: hrest5 => [hs6|hrest6].
+ move: hs6 => />; smt().
case: hrest6 => [hs7|hrest7].
+ move: hs7 => />; smt().
case: hrest7 => [hs8|hs9].
+ move: hs8 => />; smt().
move: hs9 hr => />.
qed.

lemma m23sing_total_fft_state_step r m md2 stride :
  m23sing_total_fft_outer_state r m md2 stride =>
  r \ule W64.of_int 8 =>
  m23sing_total_fft_outer_state
    (r + W64.of_int 1)
    (m `<<` W8.of_int 1)
    (md2 `<<` W8.of_int 1)
    (stride `>>` W8.of_int 1).
proof.
rewrite /m23sing_total_fft_outer_state W64.uleE W64.of_uintK /=.
move=> hstate hr.
case: hstate => [hs1|hrest1].
+ move: hs1 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify.
  auto.
case: hrest1 => [hs2|hrest2].
+ move: hs2 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify.
  auto.
case: hrest2 => [hs3|hrest3].
+ move: hs3 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify.
  auto.
case: hrest3 => [hs4|hrest4].
+ move: hs4 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify.
  auto.
case: hrest4 => [hs5|hrest5].
+ move: hs5 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify.
  auto.
case: hrest5 => [hs6|hrest6].
+ move: hs6 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify.
  auto.
case: hrest6 => [hs7|hrest7].
+ move: hs7 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify.
  auto.
case: hrest7 => [hs8|hs9].
+ move: hs8 => />.
  rewrite W64.shl_shlw 1:/# W64.shl_shlw 1:/#.
  rewrite W64.shlMP 1:/# W64.shlMP 1:/#.
  rewrite W64.shr_shrw 1:/# W64.shrDP 1:/#.
  simplify.
  auto.
by move: hs9 hr => />.
qed.

lemma m23sing_total_fft_mulrnd16_ll :
  islossless Parent.__fft_mulrnd16.
proof. by proc; islossless. qed.

lemma m23sing_total_singular_minmax_ll :
  islossless Parent.__sk_singular_value_minmax.
proof. by proc; islossless. qed.

lemma m23sing_total_singular_mulrnd16_ll :
  islossless Parent.__sk_singular_value_mulrnd16.
proof. by proc; islossless. qed.

lemma m23sing_total_fft_init_and_bitrev_ll :
  islossless Parent._fft_init_and_bitrev.
proof.
proc.
while (W64.to_uint i <= 256) (256 - W64.to_uint i).
+ move=> z.
  auto => /> &hr hi hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  smt().
auto => /> i0 hi hvariant.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma m23sing_total_fft_butterfly_ll :
  islossless Parent._fft_butterfly.
proof.
proc.
wp.
call m23sing_total_fft_mulrnd16_ll.
wp.
call m23sing_total_fft_mulrnd16_ll.
wp.
call m23sing_total_fft_mulrnd16_ll.
wp.
call m23sing_total_fft_mulrnd16_ll.
by auto.
qed.

lemma m23sing_total_fft_full_mode2_ll :
  islossless Parent._fft_full.
proof.
proc.
while
  (m23sing_total_fft_outer_state r m md2 stride)
  (9 - W64.to_uint r).
+ move=> z.
  wp.
  while
    (#pre /\
     exists block,
       0 <= block /\
       W64.to_uint n = block * W64.to_uint m /\
       W64.to_uint n <= 256)
    (256 - W64.to_uint n).
  + move=> z0.
    wp.
    while
      (#pre /\ W64.to_uint k <= W64.to_uint md2)
      (W64.to_uint md2 - W64.to_uint k).
    + move=> z1.
      wp.
      call m23sing_total_fft_butterfly_ll.
      auto => /> &hr *.
      have hsmall :
          W64.to_uint k{hr} + 1 < W64.modulus by
        smt(W64.ultE W64.to_uint_cmp).
      rewrite W64.to_uintD_small 1:hsmall W64.to_uint1.
      smt(W64.ultE W64.to_uint_cmp).
    auto => />.
    move=> &hr hstate hrbody block hblock0 hn hnbound hguard.
    rewrite W64.ultE in hguard.
    have hm :
        1 <= W64.to_uint m{hr} <= 256.
    + exact
        (m23sing_total_fft_state_body_m_bound
           r{hr} m{hr} md2{hr} stride{hr} hstate hrbody).
    have hnlt : W64.to_uint n{hr} < 256.
    + move: hguard.
      rewrite W64.of_uintK /=.
      trivial.
    have hnsmall :
        W64.to_uint n{hr} + W64.to_uint m{hr} < W64.modulus by
      smt(W64.to_uint_cmp).
    have hstepbound :
        (block + 1) * W64.to_uint m{hr} <= 256.
    + apply
        (m23sing_total_fft_state_block_step_bound
           r{hr} m{hr} md2{hr} stride{hr} block).
      + exact hstate.
      + exact hrbody.
      + exact hblock0.
      + smt().
    split.
    + smt().
    move=> k0 m0 md20 n0 r0 stride0.
    split.
    + move=> hstate0 hrbody0 hrmeasure0 block0 hblock00 hn0
             hnbound0 hnguard0 hnmeasure0 hk0 hkvariant0.
      rewrite W64.ultE.
      smt(W64.to_uint_cmp).
    move=> hkdone0 hstate0 hrbody0 hrmeasure0 block0 hblock00 hn0
           hnbound0 hnguard0 hnmeasure0 hk0.
    have hm0 : 1 <= W64.to_uint m0 <= 256.
    + exact
        (m23sing_total_fft_state_body_m_bound
           r0 m0 md20 stride0 hstate0 hrbody0).
    have hnlt0 : W64.to_uint n0 < 256.
    + move: hnguard0.
      rewrite W64.ultE W64.of_uintK /=.
      trivial.
    have hnsmall0 :
        W64.to_uint n0 + W64.to_uint m0 < W64.modulus by
      smt(W64.to_uint_cmp).
    have hstepbound0 :
        (block0 + 1) * W64.to_uint m0 <= 256.
    + apply
        (m23sing_total_fft_state_block_step_bound
           r0 m0 md20 stride0 block0).
      + exact hstate0.
      + exact hrbody0.
      + exact hblock00.
      + smt().
    rewrite W64.to_uintD_small 1:hnsmall0.
    split.
    + exists (block0 + 1).
      smt().
    smt().
  auto => />.
  move=> &hr hstate hrbody.
  split.
  + exists 0.
    smt().
  move=> m0 md20 n0 r0 stride0.
  split.
  + move=> hstate0 hrbody0 hrmeasure0 block0 hblock00 hn0
           hnbound0 hnvariant0.
    rewrite W64.ultE W64.of_uintK /=.
    smt(W64.to_uint_cmp).
  move=> hndone0 hstate0 hrbody0 hrmeasure0 block0 hblock00 hn0
         hnbound0.
  have hnext0 :
      m23sing_total_fft_outer_state
        (r0 + W64.of_int 1)
        (m0 `<<` W8.of_int 1)
        (md20 `<<` W8.of_int 1)
        (stride0 `>>` W8.of_int 1) by
    exact
      (m23sing_total_fft_state_step
         r0 m0 md20 stride0 hstate0 hrbody0).
  have hrsmall0 :
      W64.to_uint r0 + 1 < W64.modulus by
    smt(W64.to_uint_cmp).
  rewrite W64.to_uintD_small 1:hrsmall0 W64.to_uint1.
  split.
  + exact hnext0.
  smt().
auto => />.
move=> mm dd rr ss hstate hvariant.
move: hvariant hstate.
rewrite /m23sing_total_fft_outer_state W64.uleE W64.of_uintK /=.
smt().
qed.

lemma m23sing_total_singular_clear_sum_ll :
  islossless Parent._singular_clear_sum.
proof.
proc.
while (W64.to_uint i <= 256) (256 - W64.to_uint i).
+ move=> z.
  auto => /> &hr hi hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  smt().
auto => /> i0 hi hvariant.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma m23sing_total_singular_accumulate_fft_sqabs_ll :
  islossless Parent._sk_singular_value_accumulate_fft_sqabs.
proof.
proc.
while (W64.to_uint i <= 256) (256 - W64.to_uint i).
+ move=> z.
  wp.
  call m23sing_total_singular_mulrnd16_ll.
  call m23sing_total_singular_mulrnd16_ll.
  auto => /> &hr hi hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  smt().
auto => /> i0 hi hvariant.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma m23sing_total_singular_finish_mode2_ll :
  phoare [Parent._singular_finish_typed :
    best_count = 5 /\
    tau = 58 /\
    rem = 24
    ==> true] = 1%r.
proof.
bypr=> &m hpre.
byphoare
  (TargetKeygenM23SingularHelpers.singular_finish_typed_mode2_ll
     sump{m}) => //.
qed.

lemma m23sing_total_singular_full_mode2_ll :
  phoare [Parent._singular_full :
    mcount = 3 /\
    kcount = 2 /\
    best_count = 5 /\
    tau = 58 /\
    rem = 24
    ==> true] = 1%r.
proof.
proc.
wp.
call m23sing_total_singular_finish_mode2_ll.
wp.
while
  (mcount = 3 /\
   kcount = 2 /\
   best_count = 5 /\
   tau = 58 /\
   rem = 24 /\
   W64.to_uint i <= 2)
  (2 - W64.to_uint i).
+ move=> z.
  wp.
  call m23sing_total_singular_accumulate_fft_sqabs_ll.
  call m23sing_total_fft_full_mode2_ll.
  call m23sing_total_fft_init_and_bitrev_ll.
  auto => /> &hr hi hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  smt().
auto => />.
wp.
while
  (mcount = 3 /\
   kcount = 2 /\
   best_count = 5 /\
   tau = 58 /\
   rem = 24 /\
   W64.to_uint i <= 3)
  (3 - W64.to_uint i).
+ move=> z.
  wp.
  call m23sing_total_singular_accumulate_fft_sqabs_ll.
  call m23sing_total_fft_full_mode2_ll.
  call m23sing_total_fft_init_and_bitrev_ll.
  auto => /> &hr hi hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.to_uint1.
  smt().
auto => />.
call m23sing_total_singular_clear_sum_ll.
auto => />.
move=> i0.
split.
+ move=> hi0 hvariant0.
  rewrite W64.ultE W64.of_uintK /=.
  smt(W64.to_uint_cmp).
move=> _ _ i1 hi1 hvariant1.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

end TargetKeygenM23SingularTotality.
