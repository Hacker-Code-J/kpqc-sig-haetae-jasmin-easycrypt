require import AllCore IntDiv List StdOrder.

from Jasmin require import JModel_x86.

import SLH64.

require import
  KeygenSamplerCallersTarget
  HAETAE_Keccak1600
  KeygenKeccak1600Spec
  HAETAE_Keccak1600
  BArray40 BArray192 BArray200 Array5 Array24 Array25.

theory TargetKeygenKeccak1600.

import KeygenKeccak1600Spec.Word.

lemma rol64_by0 (w : W64.t) : w `|<<<|` 0 = w.
proof.
by apply W64.all_eq_eq; rewrite /all_eq /=.
qed.

lemma rol64_primitive_value (w : W64.t) (i : int) :
  (ROL_64 w (W8.of_int i)).`3 = w `|<<<|` (i %% 64).
proof.
rewrite /ROL_64 /shift_mask /=.
rewrite modz_dvd 1:/#.
case (i %% 64 = 0) => [-> | //].
by apply W64.all_eq_eq; rewrite /all_eq.
qed.

lemma rol_u64_correct (x0 : W64.t) (i0 : int) :
  hoare [KeygenSamplerCallersTarget.M.__rol_u64 :
    x = x0 /\ i = i0 %% 64 ==>
    res = x0 `|<<<|` (i0 %% 64)].
proof.
proc; simplify.
case: (i = 0).
+ by rcondf 1; auto => /> ->; rewrite rol64_by0.
rcondt 1; auto => /> hi.
rewrite /ROL_64 /shift_mask /=.
by rewrite !modz_dvd 1..2:/# hi.
qed.

lemma andn_u64_correct (a0 b0 : W64.t) :
  hoare [KeygenSamplerCallersTarget.M.__andn_u64 :
    a = a0 /\ b = b0 ==>
    res = (invw a0) `&` b0].
proof. by proc; auto. qed.

lemma theta_sum_correct (a0 : BArray200.t) :
  hoare [KeygenSamplerCallersTarget.M.__keccak_theta_sum :
    a = a0 ==>
    word_row_of_barray res = keccak_C (word_state_of_barray a0)].
proof.
proc.
do 6! unroll for ^while.
auto => />.
apply Array5.ext_eq => x hx.
rewrite row_of_barray_get 1://.
rewrite /keccak_C Array5.initiE 1:// /idx /=.
rewrite !state_of_barray_get 1..5:/#.
have hxmem : x \in iota_ 0 5 by rewrite mem_iota /#.
move: {hx} x hxmem.
apply/List.allP.
by rewrite -iotaredE /=.
qed.

lemma theta_rol_correct (c0 : BArray40.t) :
  hoare [KeygenSamplerCallersTarget.M.__keccak_theta_rol :
    c = c0 ==>
    word_row_of_barray res = keccak_D (word_row_of_barray c0)].
proof.
proc.
unroll for ^while.
inline*.
auto => />.
apply Array5.ext_eq => x hx.
rewrite row_of_barray_get 1://.
rewrite /keccak_D Array5.initiE 1:// /rol_64 /=.
rewrite !row_of_barray_get 1..2:/#.
have hxmem : x \in iota_ 0 5 by rewrite mem_iota /#.
move: {hx} x hxmem.
apply/List.allP.
by rewrite -iotaredE /ROL_64 /shift_mask /=; smt(W64.xorwC).
qed.

lemma keccakf1600_rho_offset_correct (i0 : int) :
  hoare [KeygenSamplerCallersTarget.M.__keccakf1600_rho_offset :
    0 <= i < 25 /\ i = i0 ==>
    res = W64.to_uint rhotates.[i0]].
proof.
proc.
while (
  0 <= t <= 24 /\ i = i0 /\ 0 <= x < 5 /\ 0 <= y < 5 /\
  (x, y, r) =
    foldl
      (fun (a : int * int * int) t =>
         (a.`2,
          (2 * a.`1 + 3 * a.`2) %% 5,
          if i = a.`1 + 5 * a.`2
          then ((t + 1) * (t + 2) %/ 2) %% 64
          else a.`3))
      (1, 0, 0)
      (iota_ 0 t)).
+ auto => &m [[ht [hi [hx [hy ih]]]] hguard].
  split.
  + move=> hbranch /=; split; first smt().
    by rewrite iotaSr 1:/# foldl_rcons /= -ih /= /#.
  move=> hbranch /=; split; first smt().
  by rewrite iotaSr 1:/# foldl_rcons /= -ih /= /#.
auto => /> hi0 hi25; split.
+ by rewrite -iotaredE /=.
move=> r0 t0 x0 y0 ht0 ht24 hx0 hx5 hy0 hy5 hfold hdone.
have ht_eq : t0 = 24 by smt().
move: hdone.
rewrite ht_eq.
have hi_mem : i0 \in iota_ 0 25 by smt(mem_iota).
move: {hi0 hi25} i0 hi_mem.
apply/List.allP.
by rewrite -iotaredE /rhotates /= /#.
qed.

lemma rhotates_mod64 (i : int) :
  0 <= i < 25 =>
  W64.to_uint rhotates.[i] %% 64 = W64.to_uint rhotates.[i].
proof.
move=> hi.
have hi_mem : i \in iota_ 0 25 by smt(mem_iota).
move: {hi} i hi_mem.
apply/List.allP.
by rewrite -iotaredE /rhotates /=.
qed.

lemma keccakf1600_rho_correct (x0 y0 : int) :
  hoare [KeygenSamplerCallersTarget.M.__keccakf1600_rho :
    x = x0 /\ y = y0 /\ 0 <= x0 < 5 /\ 0 <= y0 < 5 ==>
    res = W64.to_uint rhotates.[idx x0 y0]].
proof.
proc.
call (keccakf1600_rho_offset_correct (idx x0 y0)).
inline*.
auto => /> *.
rewrite /idx /=.
by smt().
qed.

lemma row_of_barray_eq_get (a : BArray40.t) (r : word_row) (i : int) :
  word_row_of_barray a = r =>
  0 <= i < 5 =>
  BArray40.get64 a i = r.[i].
proof.
move=> har hi.
rewrite -har.
by rewrite row_of_barray_get.
qed.

lemma idx_mod5 (x y : int) : idx x y %% 5 = x %% 5.
proof.
rewrite /idx /=.
by rewrite
  (mulzC 5 (y %% 5))
  (addzC (x %% 5) ((y %% 5) * 5))
  modzMDl modz_mod.
qed.

lemma idx_mod_left (x y : int) : idx (x %% 5) y = idx x y.
proof. by rewrite /idx modz_mod. qed.

lemma keccak_chi_idx (a : word_state) (x y : int) :
  0 <= x < 5 => 0 <= y < 5 =>
  (keccak_chi a).[idx x y] =
    a.[idx x y] `^`
      (invw a.[idx (x + 1) y] `&` a.[idx (x + 2) y]).
proof.
move=> hx hy.
rewrite /keccak_chi Array25.initiE 1:idx_bnd /=.
by rewrite idxK 1:// 1:// /=.
qed.

lemma rol_sum_correct (a0 : BArray200.t) (y0 : int) :
  hoare [KeygenSamplerCallersTarget.M.__keccak_rol_sum :
    a = a0 /\
    word_row_of_barray d = keccak_D (keccak_C (word_state_of_barray a0)) /\
    y = y0 /\ 0 <= y0 < 5 ==>
    forall x, 0 <= x < 5 =>
      BArray40.get64 res x =
      (keccak_pi (keccak_rho (keccak_theta (word_state_of_barray a0)))).[idx x y0]].
proof.
proc; simplify.
while (#pre /\ 0 <= x <= 5 /\
       forall i, 0 <= i < x =>
        BArray40.get64 b i =
        rol_64
          ((word_state_of_barray a0).[idx (i + 3 * y0) i] `^`
           (keccak_D (keccak_C (word_state_of_barray a0))).[(i + 3 * y0) %% 5])
          rhotates.[idx (i + 3 * y0) i]).
+ wp; ecall (rol_u64_correct (BArray40.get64 b x) r).
  wp; ecall (keccakf1600_rho_correct xp yp).
  auto => /> &m hdrel hy5 hd hx0 _ ih hx5.
  split; first smt().
  move=> hz0 hz5; split.
  + rewrite rhotates_mod64 1:/#.
    smt().
  move=> _; split; first smt().
  move=> i hi0 hi1.
  case (i = x{m}) => heq.
  + rewrite heq.
    rewrite BArray40.get_set64E 1:/# 1:/# ifT 1:/#.
    rewrite BArray40.get_set64E 1:/# 1:/# ifT 1:/#.
    rewrite BArray40.get_set64E 1:/# 1:/# ifT 1:/#.
    rewrite -hdrel.
    rewrite row_of_barray_get 1:/#.
    rewrite rhotates_mod64 1:/# /rol_64.
    congr; congr.
    + by rewrite state_of_barray_get 1:/# /idx /= /#.
    by rewrite /idx /= /#.
  rewrite BArray40.get_set64E 1:/# 1:/# ifF 1:/#.
  rewrite BArray40.get_set64E 1:/# 1:/# ifF 1:/#.
  rewrite BArray40.get_set64E 1:/# 1:/# ifF 1:/#.
  apply ih.
  smt().
auto => /> &hr hrow hylo hyhi; split; first smt().
move=> b x hdone hxlo hxhi ih x0 hx00 hx05.
have hx_eq : x = 5 by smt().
rewrite ih 1:/#.
rewrite /keccak_pi Array25.initiE 1:idx_bnd /=.
rewrite /keccak_rho Array25.initiE 1:idx_bnd /=.
rewrite /keccak_theta Array25.initiE 1:idx_bnd /=.
rewrite /rol_64.
rewrite Array25.initiE 1:idx_bnd /=.
rewrite Array25.initiE 1:idx_bnd /=.
rewrite idxK' /=.
have hxmod : x0 %% 5 = x0 by rewrite modz_small.
have hymod : y0 %% 5 = y0 by rewrite modz_small.
rewrite hxmod hymod.
congr.
+ congr.
  + by rewrite state_of_barray_get 1:idx_bnd.
  by rewrite idx_mod5.
by rewrite /rhotates Array25.initiE 1:idx_bnd /=.
qed.

lemma set_row_correct
  (a0 e0 : BArray200.t) (b0 : BArray40.t) (y0 : int) :
  hoare [KeygenSamplerCallersTarget.M.__keccak_set_row :
    e = e0 /\ b = b0 /\ y = y0 /\ 0 <= y0 < 5 /\
    (forall x, 0 <= x < 5 =>
      BArray40.get64 b0 x =
      (keccak_pi (keccak_rho (keccak_theta (word_state_of_barray a0)))).[idx x y0]) /\
    (forall k, 0 <= k < 5 * y0 =>
      BArray200.get64 e0 k =
      (keccak_pround (word_state_of_barray a0)).[k]) ==>
    forall k, 0 <= k < 5 * y0 + 5 =>
      BArray200.get64 res k =
      (keccak_pround (word_state_of_barray a0)).[k]].
proof.
proc; simplify.
while (
  b = b0 /\ y = y0 /\ 0 <= y0 < 5 /\
  (forall i, 0 <= i < 5 =>
    BArray40.get64 b0 i =
    (keccak_pi (keccak_rho (keccak_theta (word_state_of_barray a0)))).[idx i y0]) /\
  0 <= x <= 5 /\
  forall k, 0 <= k < x + 5 * y0 =>
    BArray200.get64 e k =
    (keccak_pround (word_state_of_barray a0)).[k]).
+ wp; ecall (andn_u64_correct (BArray40.get64 b x1) (BArray40.get64 b x2)).
  auto => /> &m hylo hyhi hb hxlo _ ih hxhi.
  split; first smt().
  move=> k hklo hkhi.
  case (k = x{m} + y0 * 5) => heq.
  + rewrite BArray200.get_set64E 1:/# 1:/# ifT 1:/#.
    rewrite !hb 1..3:/#.
    have hkidx : k = idx x{m} y0
      by rewrite heq /idx !modz_small /#.
    rewrite hkidx /keccak_pround keccak_chi_idx 1:/# 1:/#.
    by rewrite W64.xorwC !idx_mod_left.
  rewrite BArray200.get_set64E 1:/# 1:/# ifF 1:/#.
  apply ih.
  smt().
auto => />.
move=> hylo hyhi hb he0 e x hdone hxlo hxhi ih k hklo hkhi.
apply ih.
smt().
qed.

lemma pround_correct (a0 e0 : BArray200.t) :
  hoare [KeygenSamplerCallersTarget.M._keccak_pround :
    a = a0 /\ e = e0 ==>
    word_state_of_barray res = keccak_pround (word_state_of_barray a0)].
proof.
proc; simplify.
while (
  0 <= y <= 5 /\ a = a0 /\
  word_row_of_barray d = keccak_D (keccak_C (word_state_of_barray a0)) /\
  forall k, 0 <= k < 5 * y =>
    BArray200.get64 e k =
    (keccak_pround (word_state_of_barray a0)).[k]).
+ wp; ecall (set_row_correct a0 e b y).
  simplify; ecall (rol_sum_correct a0 y); simplify.
  auto => /> &m hylo _ ih hyhi b hb e he.
  smt().
wp; ecall (theta_rol_correct c).
ecall (theta_sum_correct a).
auto => />.
+ move=> c hc d hd.
  split; first smt().
  move=> e y hdone hylo hyhi hdrel ih.
  have hy_eq : y = 5 by smt().
  apply Array25.ext_eq => k hk.
  rewrite state_of_barray_get 1://.
  apply ih.
  smt().
qed.

lemma target_rc_wordE (i : int) :
  0 <= i < 24 =>
  BArray192.get64 KeygenSamplerCallersTarget.haetae_keccak1600_rc i =
  rc_spec.[i].
proof.
move=> hi.
rewrite /KeygenSamplerCallersTarget.haetae_keccak1600_rc
        BArray192.get64_of_list64 1://.
have himem : i \in iota_ 0 24 by rewrite mem_iota /#.
move: {hi} i himem.
apply/List.allP.
by rewrite -iotaredE /rc_spec /=.
qed.

lemma state_of_barray_iota_word (a : BArray200.t) (rc : W64.t) :
  word_state_of_barray (BArray200.set64 a 0 (BArray200.get64 a 0 `^` rc)) =
  keccak_iota rc (word_state_of_barray a).
proof.
rewrite state_of_barray_set 1:/# /keccak_iota.
congr.
by rewrite state_of_barray_get 1:/#.
qed.

lemma state_of_barray_iota_word0 (a : BArray200.t) (rc : W64.t) :
  word_state_of_barray
    (BArray200.set64d a 0 (BArray200.get64d a 0 `^` rc)) =
  keccak_iota rc (word_state_of_barray a).
proof.
exact (state_of_barray_iota_word a rc).
qed.

lemma keccak_statepermute_word_correct (a0 : BArray200.t) :
  hoare [KeygenSamplerCallersTarget.M.__keccakf1600_statepermute :
    a = a0 ==>
    word_state_of_barray res = keccak_f1600 (word_state_of_barray a0)].
proof.
proc.
while (0 <= c <= 12 /\
       word_state_of_barray a = word_rounds (word_state_of_barray a0) (2 * c)).
+ wp; ecall (pround_correct e a).
  wp; ecall (pround_correct a e).
  auto => /> &m hc0 hc12 ha hguard.
  move=> e1 he1 a1 ha1.
  split; first smt().
  rewrite /swap_ /=.
  rewrite state_of_barray_iota_word0.
  rewrite /swap_ /= in ha1.
  rewrite state_of_barray_iota_word0 in ha1.
  rewrite target_rc_wordE 1:/#.
  rewrite target_rc_wordE 1:/# in ha1.
  have hcount : 2 * (c{m} + 1) = (2 * c{m} + 1) + 1 by ring.
  rewrite hcount word_rounds_succ 1:/# word_rounds_succ 1:/#.
  rewrite /keccak_round.
  rewrite -ha.
  rewrite ha1 -he1.
  trivial.
auto => />.
split.
+ by rewrite word_rounds0.
move=> a1 c1 hdone hc0 hc12 ha.
have hc : c1 = 12 by smt().
subst c1.
rewrite ha /= word_rounds24.
trivial.
qed.

lemma keccakf1600_word_correct (sp0 : BArray200.t) :
  hoare [KeygenSamplerCallersTarget.M._keccakf1600 :
    sp_0 = sp0 ==>
    word_state_of_barray res = keccak_f1600 (word_state_of_barray sp0)].
proof.
proc.
by call (keccak_statepermute_word_correct sp0).
qed.

lemma keccakf1600_correct (sp0 : BArray200.t) :
  hoare [KeygenSamplerCallersTarget.M._keccakf1600 :
    sp_0 = sp0 ==>
    KeygenKeccak1600Spec.state_of_barray res =
      HAETAE_Keccak1600.keccak_f1600_lanes
        (KeygenKeccak1600Spec.state_of_barray sp0)].
proof.
proc.
call (keccak_statepermute_word_correct sp0).
auto => /> a1 ha.
have ha1 := state_of_barray_lanes a1.
rewrite -ha1 ha.
apply keccak_f1600_state_of_barray_bridge.
qed.

(* These losslessness facts are deliberately proved from the generated loop
   bounds.  They make no assumption about the values produced by Keccak. *)
lemma keccak_init_state_ll :
  islossless KeygenSamplerCallersTarget.M._keccak_init_state.
proof.
proc.
while (W64.to_uint i <= 25) (25 - W64.to_uint i).
+ move=> z.
  auto => /> &hr hi hguard.
  rewrite W64.ultE W64.of_uintK /= in hguard.
  rewrite W64.to_uintD_small 1:/# W64.of_uintK /=.
  smt().
auto => /> i0 hi hvariant.
rewrite W64.ultE W64.of_uintK /=.
smt(W64.to_uint_cmp).
qed.

lemma keccak_rho_offset_ll :
  islossless KeygenSamplerCallersTarget.M.__keccakf1600_rho_offset.
proof.
proc.
while (0 <= t <= 24) (24 - t).
+ by move=> z; auto => />; smt().
by auto => />; smt().
qed.

lemma keccak_index_ll :
  islossless KeygenSamplerCallersTarget.M.__keccakf1600_index.
proof. by proc; auto. qed.

lemma keccak_rho_ll :
  islossless KeygenSamplerCallersTarget.M.__keccakf1600_rho.
proof.
proc.
call keccak_rho_offset_ll.
call keccak_index_ll.
by auto.
qed.

lemma keccak_theta_sum_ll :
  islossless KeygenSamplerCallersTarget.M.__keccak_theta_sum.
proof.
proc.
while (0 <= y <= 5) (5 - y).
+ move=> z.
  wp.
  while (0 <= x <= 5) (5 - x).
  + by move=> z0; auto => />; smt().
  by auto => />; smt().
wp.
while (0 <= x <= 5) (5 - x).
+ by move=> z; auto => />; smt().
by auto => />; smt().
qed.

lemma keccak_rol_u64_ll :
  islossless KeygenSamplerCallersTarget.M.__rol_u64.
proof. by proc; auto. qed.

lemma keccak_theta_rol_ll :
  islossless KeygenSamplerCallersTarget.M.__keccak_theta_rol.
proof.
proc.
while (0 <= x <= 5) (5 - x).
+ move=> z.
  wp.
  call keccak_rol_u64_ll.
  by auto => />; smt().
by auto => />; smt().
qed.

lemma keccak_rol_sum_ll :
  islossless KeygenSamplerCallersTarget.M.__keccak_rol_sum.
proof.
proc.
while (0 <= x <= 5) (5 - x).
+ move=> z.
  wp.
  call keccak_rol_u64_ll.
  wp.
  call keccak_rho_ll.
  by auto => />; smt().
by auto => />; smt().
qed.

lemma keccak_andn_u64_ll :
  islossless KeygenSamplerCallersTarget.M.__andn_u64.
proof. by proc; auto. qed.

lemma keccak_set_row_ll :
  islossless KeygenSamplerCallersTarget.M.__keccak_set_row.
proof.
proc.
while (0 <= x <= 5) (5 - x).
+ move=> z.
  wp.
  call keccak_andn_u64_ll.
  by auto => />; smt().
by auto => />; smt().
qed.

lemma keccak_pround_ll :
  islossless KeygenSamplerCallersTarget.M._keccak_pround.
proof.
proc.
while (0 <= y <= 5) (5 - y).
+ move=> z.
  wp.
  call keccak_set_row_ll.
  call keccak_rol_sum_ll.
  by auto => />; smt().
wp.
call keccak_theta_rol_ll.
call keccak_theta_sum_ll.
by auto => />; smt().
qed.

lemma keccak_statepermute_ll :
  islossless KeygenSamplerCallersTarget.M.__keccakf1600_statepermute.
proof.
proc.
while (0 <= c <= 12) (12 - c).
+ move=> z.
  wp.
  call keccak_pround_ll.
  wp.
  call keccak_pround_ll.
  by auto => />; smt().
by auto => />; smt().
qed.

lemma keccakf1600_ll :
  islossless KeygenSamplerCallersTarget.M._keccakf1600.
proof.
proc.
call keccak_statepermute_ll.
by auto.
qed.

end TargetKeygenKeccak1600.
