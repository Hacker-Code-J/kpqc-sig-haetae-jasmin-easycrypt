require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

require import
  BArray40 BArray200 Array5 Array24 Array25 HAETAE_Keccak1600.

import SLH64.

theory KeygenKeccak1600Spec.

op lane_of_word (w : W64.t) : HAETAE_Keccak1600.keccak_lane =
  mkseq (fun i => w.[i]) HAETAE_Keccak1600.keccak_lane_bits.

op state_of_barray (a : BArray200.t) : HAETAE_Keccak1600.keccak_state =
  mkseq
    (fun i => lane_of_word (BArray200.get64 a i))
    HAETAE_Keccak1600.keccak_state_lanes.

op state_set_lane
  (st : HAETAE_Keccak1600.keccak_state)
  (lane : int)
  (value : HAETAE_Keccak1600.keccak_lane) :
  HAETAE_Keccak1600.keccak_state =
  mkseq
    (fun i =>
       if i = lane
       then value
       else nth HAETAE_Keccak1600.keccak_lane_zero st i)
    HAETAE_Keccak1600.keccak_state_lanes.

op jasmin_rol64 (x : W64.t) (offset : int) : W64.t =
  if offset = 0 then x else (ROL_64 x (W8.of_int offset)).`3.

lemma lane_of_word_size w :
  size (lane_of_word w) = HAETAE_Keccak1600.keccak_lane_bits.
proof. by rewrite /lane_of_word size_mkseq. qed.

lemma lane_of_word_wf w :
  HAETAE_Keccak1600.keccak_lane_wf (lane_of_word w).
proof.
by rewrite /HAETAE_Keccak1600.keccak_lane_wf lane_of_word_size.
qed.

lemma lane_of_word_bitE w bit :
  0 <= bit < HAETAE_Keccak1600.keccak_lane_bits =>
  HAETAE_Keccak1600.keccak_lane_bit (lane_of_word w) bit = w.[bit].
proof.
move=> hbit.
by rewrite /HAETAE_Keccak1600.keccak_lane_bit /lane_of_word nth_mkseq.
qed.

lemma state_of_barray_size a :
  size (state_of_barray a) = HAETAE_Keccak1600.keccak_state_lanes.
proof. by rewrite /state_of_barray size_mkseq. qed.

lemma state_of_barray_laneE a lane :
  0 <= lane < HAETAE_Keccak1600.keccak_state_lanes =>
  nth HAETAE_Keccak1600.keccak_lane_zero (state_of_barray a) lane =
  lane_of_word (BArray200.get64 a lane).
proof.
move=> hlane.
by rewrite /state_of_barray nth_mkseq.
qed.

lemma state_of_barray_lane_bitE a lane bit :
  0 <= lane < HAETAE_Keccak1600.keccak_state_lanes =>
  0 <= bit < HAETAE_Keccak1600.keccak_lane_bits =>
  HAETAE_Keccak1600.keccak_lane_bit
    (nth HAETAE_Keccak1600.keccak_lane_zero (state_of_barray a) lane)
    bit =
  (BArray200.get64 a lane).[bit].
proof.
move=> hlane hbit.
by rewrite state_of_barray_laneE // lane_of_word_bitE.
qed.

lemma state_of_barray_set64 a lane value :
  0 <= lane < HAETAE_Keccak1600.keccak_state_lanes =>
  state_of_barray (BArray200.set64 a lane value) =
  state_set_lane (state_of_barray a) lane (lane_of_word value).
proof.
move=> hlane.
rewrite /state_of_barray /state_set_lane.
apply eq_in_mkseq => i hi /=.
rewrite BArray200.get_set64E 1:/# 1:/#.
case (i = lane) => hilane.
+ by rewrite hilane.
rewrite nth_mkseq.
+ exact hi.
case (lane = i) => hli; first by smt().
by trivial.
qed.

lemma lane_of_word_xor (x y : W64.t) :
  lane_of_word (x `^` y) =
  HAETAE_Keccak1600.keccak_lane_xor (lane_of_word x) (lane_of_word y).
proof.
rewrite /lane_of_word /HAETAE_Keccak1600.keccak_lane_xor.
apply eq_in_mkseq => bit hbit /=.
rewrite /HAETAE_Keccak1600.keccak_lane_bit !nth_mkseq.
+ exact hbit.
+ exact hbit.
by smt().
qed.

lemma keccak_lane_xorC (a b : HAETAE_Keccak1600.keccak_lane) :
  HAETAE_Keccak1600.keccak_lane_xor a b =
  HAETAE_Keccak1600.keccak_lane_xor b a.
proof.
rewrite /HAETAE_Keccak1600.keccak_lane_xor.
apply eq_in_mkseq => bit hbit /=.
by smt().
qed.

lemma lane_of_word_and (x y : W64.t) :
  lane_of_word (x `&` y) =
  HAETAE_Keccak1600.keccak_lane_and (lane_of_word x) (lane_of_word y).
proof.
rewrite /lane_of_word /HAETAE_Keccak1600.keccak_lane_and.
apply eq_in_mkseq => bit hbit /=.
rewrite /HAETAE_Keccak1600.keccak_lane_bit !nth_mkseq.
+ exact hbit.
+ exact hbit.
by done.
qed.

lemma lane_of_word_not (x : W64.t) :
  lane_of_word (invw x) =
  HAETAE_Keccak1600.keccak_lane_not (lane_of_word x).
proof.
rewrite /lane_of_word /HAETAE_Keccak1600.keccak_lane_not.
apply eq_in_mkseq => bit hbit /=.
rewrite /HAETAE_Keccak1600.keccak_lane_bit !nth_mkseq.
+ exact hbit.
rewrite HAETAE_Keccak1600.keccak_lane_bitsE in hbit.
by case (x.[bit]) => //; smt().
qed.

lemma lane_of_word_andn (x y : W64.t) :
  lane_of_word ((invw x) `&` y) =
  HAETAE_Keccak1600.keccak_lane_and
    (HAETAE_Keccak1600.keccak_lane_not (lane_of_word x))
    (lane_of_word y).
proof. by rewrite lane_of_word_and lane_of_word_not. qed.

lemma lane_of_word_rol (x : W64.t) (offset : int) :
  lane_of_word (W64.rol x offset) =
  HAETAE_Keccak1600.keccak_lane_rotl (lane_of_word x) offset.
proof.
rewrite /lane_of_word /HAETAE_Keccak1600.keccak_lane_rotl.
apply eq_in_mkseq => bit hbit /=.
rewrite /HAETAE_Keccak1600.keccak_lane_bit nth_mkseq.
+ exact (HAETAE_Keccak1600.keccak_lane_mod_range (bit - offset)).
rewrite HAETAE_Keccak1600.keccak_lane_bitsE in hbit.
by rewrite HAETAE_Keccak1600.keccak_lane_bitsE hbit.
qed.

lemma ROL_64_word (x : W64.t) (offset : int) :
  0 < offset < 64 =>
  (ROL_64 x (W8.of_int offset)).`3 = W64.rol x offset.
proof.
move=> hoff.
rewrite ROL_64_E /W64.shift_mask /=.
rewrite (modz_small offset 256) 1:/# (modz_small offset 64) 1:/# /=.
by smt().
qed.

lemma W64_rol0 (x : W64.t) : W64.rol x 0 = x.
proof.
apply W64.wordP => bit hbit.
by rewrite W64.rolwE hbit /= modz_small.
qed.

lemma jasmin_rol64E (x : W64.t) (offset : int) :
  0 <= offset < 64 =>
  jasmin_rol64 x offset = W64.rol x offset.
proof.
move=> hoff.
rewrite /jasmin_rol64.
case (offset = 0) => hoff0.
+ by rewrite hoff0 W64_rol0.
by rewrite ROL_64_word 1:/#.
qed.

lemma lane_of_jasmin_rol64 (x : W64.t) (offset : int) :
  0 <= offset < 64 =>
  lane_of_word (jasmin_rol64 x offset) =
  HAETAE_Keccak1600.keccak_lane_rotl (lane_of_word x) offset.
proof. by move=> hoff; rewrite jasmin_rol64E // lane_of_word_rol. qed.

lemma lane_of_word_of_int (x : int) :
  lane_of_word (W64.of_int x) = HAETAE_Keccak1600.keccak_lane_of_int x.
proof.
rewrite /lane_of_word /HAETAE_Keccak1600.keccak_lane_of_int.
apply eq_in_mkseq => bit hbit /=.
rewrite W64.of_intwE hbit /= /W64.int_bit.
by rewrite /HAETAE_Keccak1600.keccak_word_bit
           /HAETAE_Keccak1600.keccak_word_norm
           HAETAE_Keccak1600.keccak_lane_bitsE.
qed.

lemma lane_of_word_of_int_mod (x y : int) :
  x %% (2 ^ 64) = y %% (2 ^ 64) =>
  lane_of_word (W64.of_int x) = HAETAE_Keccak1600.keccak_lane_of_int y.
proof.
move=> hmod.
rewrite /lane_of_word /HAETAE_Keccak1600.keccak_lane_of_int.
apply eq_in_mkseq => bit hbit /=.
rewrite W64.of_intwE hbit /= /W64.int_bit.
by rewrite /HAETAE_Keccak1600.keccak_word_bit
           /HAETAE_Keccak1600.keccak_word_norm
           HAETAE_Keccak1600.keccak_lane_bitsE hmod.
qed.


op row_of_barray (a : BArray40.t) : HAETAE_Keccak1600.keccak_lane list =
  mkseq
    (fun i => lane_of_word (BArray40.get64 a i))
    5.

lemma row_of_barray_size a :
  size (row_of_barray a) = 5.
proof. by rewrite /row_of_barray size_mkseq. qed.

lemma row_of_barray_laneE a lane :
  0 <= lane < 5 =>
  nth HAETAE_Keccak1600.keccak_lane_zero (row_of_barray a) lane =
  lane_of_word (BArray40.get64 a lane).
proof. by move=> hlane; rewrite /row_of_barray nth_mkseq. qed.

lemma keccak_theta_c_mod st x :
  HAETAE_Keccak1600.keccak_theta_c st x =
  HAETAE_Keccak1600.keccak_theta_c st (x %% 5).
proof.
by rewrite /HAETAE_Keccak1600.keccak_theta_c
           /HAETAE_Keccak1600.keccak_state_lane
           /HAETAE_Keccak1600.keccak_lane_index !modz_mod.
qed.

lemma state_of_barray_iota (a : BArray200.t) (rc : W64.t) :
  state_of_barray
    (BArray200.set64 a 0 (BArray200.get64 a 0 `^` rc)) =
  HAETAE_Keccak1600.keccak_iota
    (state_of_barray a) (lane_of_word rc).
proof.
rewrite state_of_barray_set64 1:/#.
rewrite /state_set_lane /HAETAE_Keccak1600.keccak_iota.
apply eq_in_mkseq => i hi /=.
case (i = 0) => hi0.
+ subst i; rewrite /= lane_of_word_xor.
  by rewrite state_of_barray_laneE 1:/#.
trivial.
qed.

op keccak_round_at
    (st : HAETAE_Keccak1600.keccak_state) (round : int) :
    HAETAE_Keccak1600.keccak_state =
  HAETAE_Keccak1600.keccak_round st
    (HAETAE_Keccak1600.keccak_lane_of_int
      (nth 0 HAETAE_Keccak1600.keccak_round_constants round)).

op keccak_rounds
    (st : HAETAE_Keccak1600.keccak_state) (count : int) :
    HAETAE_Keccak1600.keccak_state =
  foldl keccak_round_at st (iota_ 0 count).

lemma keccak_rounds0 st : keccak_rounds st 0 = st.
proof. by rewrite /keccak_rounds iota0. qed.

lemma keccak_rounds_succ st count :
  0 <= count =>
  keccak_rounds st (count + 1) =
  keccak_round_at (keccak_rounds st count) count.
proof.
move=> hcount.
by rewrite /keccak_rounds iotaSr 1:// foldl_rcons.
qed.

lemma keccak_rounds24 st :
  keccak_rounds st 24 = HAETAE_Keccak1600.keccak_f1600_lanes st.
proof.
by rewrite /keccak_rounds /keccak_round_at
           /HAETAE_Keccak1600.keccak_f1600_lanes
           /HAETAE_Keccak1600.keccak_round_constants -iotaredE /=.
qed.

theory Word.

type word_state = W64.t Array25.t.
type word_row = W64.t Array5.t.

op idx (x y : int) : int = (x %% 5) + 5 * (y %% 5).
op invidx (i : int) : int * int = (i %% 5, i %/ 5).

lemma idx_bnd x y : 0 <= idx x y < 25.
proof. by rewrite /idx /#. qed.

lemma idxK x y :
  0 <= x < 5 => 0 <= y < 5 => invidx (idx x y) = (x, y).
proof. by rewrite /idx /invidx /#; smt(). qed.

lemma idxK' x y : invidx (idx x y) = (x %% 5, y %% 5).
proof. by rewrite (: idx x y = idx (x %% 5) (y %% 5)) 1:/# idxK /#. qed.

op rhotates : W64.t Array25.t =
  Array25.of_list W64.zero
    [ W64.of_int 0; W64.of_int 1; W64.of_int 62;
      W64.of_int 28; W64.of_int 27; W64.of_int 36;
      W64.of_int 44; W64.of_int 6; W64.of_int 55;
      W64.of_int 20; W64.of_int 3; W64.of_int 10;
      W64.of_int 43; W64.of_int 25; W64.of_int 39;
      W64.of_int 41; W64.of_int 45; W64.of_int 15;
      W64.of_int 21; W64.of_int 8; W64.of_int 18;
      W64.of_int 2; W64.of_int 61; W64.of_int 56;
      W64.of_int 14 ].

op rc_spec : W64.t Array24.t =
  Array24.of_list witness
    [ W64.of_int 1; W64.of_int 32898;
      W64.of_int 9223372036854808714;
      W64.of_int 9223372039002292224;
      W64.of_int 32907; W64.of_int 2147483649;
      W64.of_int 9223372039002292353;
      W64.of_int 9223372036854808585;
      W64.of_int 138; W64.of_int 136;
      W64.of_int 2147516425; W64.of_int 2147483658;
      W64.of_int 2147516555;
      W64.of_int 9223372036854775947;
      W64.of_int 9223372036854808713;
      W64.of_int 9223372036854808579;
      W64.of_int 9223372036854808578;
      W64.of_int 9223372036854775936;
      W64.of_int 32778;
      W64.of_int 9223372039002259466;
      W64.of_int 9223372039002292353;
      W64.of_int 9223372036854808704;
      W64.of_int 2147483649;
      W64.of_int 9223372039002292232 ].

op word_state_of_barray (a : BArray200.t) : word_state =
  Array25.init (fun i => BArray200.get64 a i).

op word_row_of_barray (a : BArray40.t) : word_row =
  Array5.init (fun i => BArray40.get64 a i).

lemma state_of_barray_get a i :
  0 <= i < 25 =>
  (word_state_of_barray a).[i] = BArray200.get64 a i.
proof. by move=> hi; rewrite /word_state_of_barray Array25.initiE. qed.

lemma row_of_barray_get a i :
  0 <= i < 5 =>
  (word_row_of_barray a).[i] = BArray40.get64 a i.
proof. by move=> hi; rewrite /word_row_of_barray Array5.initiE. qed.

lemma state_of_barray_set a i w :
  0 <= i < 25 =>
  word_state_of_barray (BArray200.set64 a i w) =
    (word_state_of_barray a).[i <- w].
proof.
move=> hi; apply Array25.ext_eq => j hj.
rewrite state_of_barray_get 1://.
rewrite Array25.get_setE 1://.
rewrite state_of_barray_get 1://.
rewrite BArray200.get_set64E 1:/# 1:/#.
case: (j = i) => hji.
+ by rewrite hji.
have hij : i <> j by smt().
by rewrite hij.
qed.

lemma row_of_barray_set a i w :
  0 <= i < 5 =>
  word_row_of_barray (BArray40.set64 a i w) =
    (word_row_of_barray a).[i <- w].
proof.
move=> hi; apply Array5.ext_eq => j hj.
rewrite row_of_barray_get 1://.
rewrite Array5.get_setE 1://.
rewrite row_of_barray_get 1://.
rewrite BArray40.get_set64E 1:/# 1:/#.
case: (j = i) => hji.
+ by rewrite hji.
have hij : i <> j by smt().
by rewrite hij.
qed.

op rol_64 (w r : W64.t) : W64.t = w `|<<<|` W64.to_uint r.

op keccak_C (a : word_state) : word_row =
  Array5.init (fun x =>
    a.[x + 5 * 0] `^` a.[x + 5 * 1] `^`
    a.[x + 5 * 2] `^` a.[x + 5 * 3] `^` a.[x + 5 * 4]).

op keccak_D (c : word_row) : word_row =
  Array5.init (fun x =>
    c.[(x - 1) %% 5] `^` rol_64 c.[(x + 1) %% 5] (W64.of_int 1)).

op keccak_theta (a : word_state) : word_state =
  Array25.init (fun i => a.[i] `^` (keccak_D (keccak_C a)).[i %% 5]).

op keccak_rho (a : word_state) : word_state =
  Array25.init (fun i => rol_64 a.[i] rhotates.[i]).

op keccak_pi (a : word_state) : word_state =
  Array25.init (fun i =>
    let xy = invidx i in a.[idx (xy.`1 + 3 * xy.`2) xy.`1]).

op keccak_chi (a : word_state) : word_state =
  Array25.init (fun i =>
    let xy = invidx i in
    a.[idx xy.`1 xy.`2] `^`
      (invw a.[idx (xy.`1 + 1) xy.`2] `&`
             a.[idx (xy.`1 + 2) xy.`2])).

op keccak_pround (a : word_state) : word_state =
  keccak_chi (keccak_pi (keccak_rho (keccak_theta a))).

op keccak_iota (c : W64.t) (a : word_state) : word_state =
  a.[0 <- a.[0] `^` c].

op keccak_round (c : W64.t) (a : word_state) : word_state =
  keccak_iota c (keccak_pround a).

op keccak_f1600 (a : word_state) : word_state =
  foldl (fun s ir => keccak_round rc_spec.[ir] s) a (iota_ 0 24).

abbrev keccak_double_round (a : word_state) (i : int) : word_state =
  keccak_round rc_spec.[2 * i + 1]
    (keccak_round rc_spec.[2 * i] a).


op lanes_of_word_state (a : word_state) :
  HAETAE_Keccak1600.keccak_state =
  mkseq
    (fun i => KeygenKeccak1600Spec.lane_of_word a.[i])
    HAETAE_Keccak1600.keccak_state_lanes.

lemma lanes_of_word_state_size (a : word_state) :
  size (lanes_of_word_state a) = HAETAE_Keccak1600.keccak_state_lanes.
proof. by rewrite /lanes_of_word_state size_mkseq. qed.

lemma lanes_of_word_state_nth (a : word_state) (i : int) :
  0 <= i < 25 =>
  nth HAETAE_Keccak1600.keccak_lane_zero (lanes_of_word_state a) i =
  KeygenKeccak1600Spec.lane_of_word a.[i].
proof.
move=> hi.
by rewrite /lanes_of_word_state
           HAETAE_Keccak1600.keccak_state_lanesE nth_mkseq.
qed.

lemma lanes_of_word_state_lane (a : word_state) (x y : int) :
  HAETAE_Keccak1600.keccak_state_lane (lanes_of_word_state a) x y =
  KeygenKeccak1600Spec.lane_of_word a.[idx x y].
proof.
rewrite /HAETAE_Keccak1600.keccak_state_lane
        /HAETAE_Keccak1600.keccak_lane_index.
rewrite lanes_of_word_state_nth 1:idx_bnd.
by rewrite /idx (mulzC 5 (y %% 5)).
qed.

lemma state_of_barray_lanes (a : BArray200.t) :
  lanes_of_word_state (word_state_of_barray a) =
  KeygenKeccak1600Spec.state_of_barray a.
proof.
apply/(eq_from_nth HAETAE_Keccak1600.keccak_lane_zero).
+ by rewrite lanes_of_word_state_size
             KeygenKeccak1600Spec.state_of_barray_size.
move=> i.
rewrite lanes_of_word_state_size
        HAETAE_Keccak1600.keccak_state_lanesE => hi.
rewrite lanes_of_word_state_nth 1://
        KeygenKeccak1600Spec.state_of_barray_laneE 1://.
by rewrite state_of_barray_get.
qed.

lemma idx_small (x y : int) :
  0 <= x < 5 => 0 <= y < 5 => idx x y = x + 5 * y.
proof.
move=> hx hy.
by rewrite /idx !modz_small.
qed.

lemma keccak_C_lanes (a : word_state) (x : int) :
  0 <= x < 5 =>
  KeygenKeccak1600Spec.lane_of_word (keccak_C a).[x] =
  HAETAE_Keccak1600.keccak_theta_c (lanes_of_word_state a) x.
proof.
move=> hx.
rewrite /keccak_C Array5.initiE 1://
        /HAETAE_Keccak1600.keccak_theta_c.
rewrite !lanes_of_word_state_lane.
rewrite !idx_small 1..10:/#.
by rewrite !KeygenKeccak1600Spec.lane_of_word_xor.
qed.

lemma keccak_D_lanes (a : word_state) (x : int) :
  0 <= x < 5 =>
  KeygenKeccak1600Spec.lane_of_word
    (keccak_D (keccak_C a)).[x] =
  HAETAE_Keccak1600.keccak_theta_d (lanes_of_word_state a) x.
proof.
move=> hx.
rewrite /keccak_D Array5.initiE 1://
        /HAETAE_Keccak1600.keccak_theta_d /rol_64.
rewrite KeygenKeccak1600Spec.lane_of_word_xor
        KeygenKeccak1600Spec.lane_of_word_rol.
rewrite !keccak_C_lanes 1..2:/#.
congr.
+ rewrite (KeygenKeccak1600Spec.keccak_theta_c_mod
             (lanes_of_word_state a) (x + 4)).
  congr.
  smt().
congr.
+ rewrite eq_sym.
  exact (KeygenKeccak1600Spec.keccak_theta_c_mod
           (lanes_of_word_state a) (x + 1)).
rewrite /W64.one.
smt().
qed.

lemma keccak_theta_lanes (a : word_state) :
  lanes_of_word_state (keccak_theta a) =
  HAETAE_Keccak1600.keccak_theta (lanes_of_word_state a).
proof.
apply/(eq_from_nth HAETAE_Keccak1600.keccak_lane_zero).
+ by rewrite lanes_of_word_state_size
             /HAETAE_Keccak1600.keccak_theta size_mkseq.
move=> i.
rewrite lanes_of_word_state_size
        HAETAE_Keccak1600.keccak_state_lanesE => hi.
rewrite lanes_of_word_state_nth 1://
        /keccak_theta Array25.initiE 1://.
rewrite /HAETAE_Keccak1600.keccak_theta nth_mkseq 1:/# /=.
rewrite KeygenKeccak1600Spec.lane_of_word_xor.
have hix : 0 <= i %% 5 < 5 by apply modz_cmp; smt().
rewrite lanes_of_word_state_lane keccak_D_lanes 1://.
congr.
have hiy : 0 <= i %/ 5 < 5 by smt(divz_cmp).
rewrite /idx.
by smt(divz_eq).
qed.

lemma rhotates_laneE (i : int) :
  0 <= i < 25 =>
  W64.to_uint rhotates.[i] =
  nth 0 HAETAE_Keccak1600.keccak_rho_offsets i.
proof.
move=> hi.
have himem : i \in iota_ 0 25 by rewrite mem_iota /#.
move: {hi} i himem.
apply/List.allP.
by rewrite -iotaredE /rhotates
           /HAETAE_Keccak1600.keccak_rho_offsets /=.
qed.

lemma keccak_rho_pi_lanes (a : word_state) :
  lanes_of_word_state (keccak_pi (keccak_rho a)) =
  HAETAE_Keccak1600.keccak_rho_pi (lanes_of_word_state a).
proof.
apply/(eq_from_nth HAETAE_Keccak1600.keccak_lane_zero).
+ by rewrite lanes_of_word_state_size
             /HAETAE_Keccak1600.keccak_rho_pi size_mkseq.
move=> i.
rewrite lanes_of_word_state_size
        HAETAE_Keccak1600.keccak_state_lanesE => hi.
rewrite lanes_of_word_state_nth 1://
        /keccak_pi Array25.initiE 1:// /=.
rewrite /keccak_rho Array25.initiE 1:idx_bnd /= /rol_64.
rewrite KeygenKeccak1600Spec.lane_of_word_rol.
rewrite /HAETAE_Keccak1600.keccak_rho_pi nth_mkseq 1:/# /=.
rewrite lanes_of_word_state_lane.
rewrite rhotates_laneE 1:idx_bnd.
rewrite /invidx /=.
congr.
+ congr; rewrite /idx /HAETAE_Keccak1600.keccak_lane_index /=.
  by rewrite !modz_mod.
rewrite /idx /HAETAE_Keccak1600.keccak_lane_index /=.
by rewrite !modz_mod.
qed.

lemma keccak_chi_lanes (a : word_state) :
  lanes_of_word_state (keccak_chi a) =
  HAETAE_Keccak1600.keccak_chi (lanes_of_word_state a).
proof.
apply/(eq_from_nth HAETAE_Keccak1600.keccak_lane_zero).
+ by rewrite lanes_of_word_state_size
             /HAETAE_Keccak1600.keccak_chi size_mkseq.
move=> i.
rewrite lanes_of_word_state_size
        HAETAE_Keccak1600.keccak_state_lanesE => hi.
rewrite lanes_of_word_state_nth 1://
        /keccak_chi Array25.initiE 1:// /=.
rewrite /HAETAE_Keccak1600.keccak_chi nth_mkseq 1:/# /=.
rewrite KeygenKeccak1600Spec.lane_of_word_xor
        KeygenKeccak1600Spec.lane_of_word_andn.
rewrite !lanes_of_word_state_lane /invidx /=.
trivial.
qed.

lemma keccak_iota_lanes (c : W64.t) (a : word_state) :
  lanes_of_word_state (keccak_iota c a) =
  HAETAE_Keccak1600.keccak_iota
    (lanes_of_word_state a) (KeygenKeccak1600Spec.lane_of_word c).
proof.
apply/(eq_from_nth HAETAE_Keccak1600.keccak_lane_zero).
+ by rewrite lanes_of_word_state_size
             /HAETAE_Keccak1600.keccak_iota size_mkseq.
move=> i.
rewrite lanes_of_word_state_size
        HAETAE_Keccak1600.keccak_state_lanesE => hi.
rewrite lanes_of_word_state_nth 1://
        /keccak_iota Array25.get_setE 1://.
rewrite /HAETAE_Keccak1600.keccak_iota nth_mkseq 1:/# /=.
case (i = 0) => hi0.
+ subst i.
  rewrite /= KeygenKeccak1600Spec.lane_of_word_xor.
  by rewrite lanes_of_word_state_nth 1:/#.
by rewrite lanes_of_word_state_nth 1://.
qed.

lemma keccak_pround_lanes (a : word_state) :
  lanes_of_word_state (keccak_pround a) =
  HAETAE_Keccak1600.keccak_chi
    (HAETAE_Keccak1600.keccak_rho_pi
      (HAETAE_Keccak1600.keccak_theta (lanes_of_word_state a))).
proof.
by rewrite /keccak_pround keccak_chi_lanes
           keccak_rho_pi_lanes keccak_theta_lanes.
qed.

lemma keccak_round_lanes (c : W64.t) (a : word_state) :
  lanes_of_word_state (keccak_round c a) =
  HAETAE_Keccak1600.keccak_round
    (lanes_of_word_state a) (KeygenKeccak1600Spec.lane_of_word c).
proof.
by rewrite /keccak_round /HAETAE_Keccak1600.keccak_round
           keccak_iota_lanes keccak_pround_lanes.
qed.

lemma rc_spec_laneE (i : int) :
  0 <= i < 24 =>
  KeygenKeccak1600Spec.lane_of_word rc_spec.[i] =
  HAETAE_Keccak1600.keccak_lane_of_int
    (nth 0 HAETAE_Keccak1600.keccak_round_constants i).
proof.
move=> hi.
have himem : i \in iota_ 0 24 by rewrite mem_iota /#.
move: {hi} i himem.
apply/List.allP.
by rewrite -iotaredE /rc_spec
           /HAETAE_Keccak1600.keccak_round_constants /=
           !KeygenKeccak1600Spec.lane_of_word_of_int.
qed.

op word_rounds (a : word_state) (count : int) =
  foldl (fun s i => keccak_round rc_spec.[i] s) a (iota_ 0 count).

lemma word_rounds0 (a : word_state) : word_rounds a 0 = a.
proof. by rewrite /word_rounds iota0. qed.

lemma word_rounds_succ (a : word_state) (count : int) :
  0 <= count =>
  word_rounds a (count + 1) =
  keccak_round rc_spec.[count] (word_rounds a count).
proof.
move=> hcount.
by rewrite /word_rounds iotaSr 1:// foldl_rcons.
qed.

lemma word_rounds24 (a : word_state) :
  word_rounds a 24 = keccak_f1600 a.
proof. by rewrite /word_rounds /keccak_f1600. qed.

lemma word_rounds_lanes (a : word_state) (count : int) :
  0 <= count <= 24 =>
  lanes_of_word_state (word_rounds a count) =
  KeygenKeccak1600Spec.keccak_rounds (lanes_of_word_state a) count.
proof.
move=> [hcount0 hcount24].
move: count hcount0 hcount24.
apply intind.
+ move=> _.
  by rewrite word_rounds0 KeygenKeccak1600Spec.keccak_rounds0.
move=> i hi ih hi24.
rewrite word_rounds_succ 1://
        KeygenKeccak1600Spec.keccak_rounds_succ 1://.
rewrite keccak_round_lanes.
rewrite ih 1:/# rc_spec_laneE 1:/#.
trivial.
qed.

lemma keccak_f1600_lanes (a : word_state) :
  lanes_of_word_state (keccak_f1600 a) =
  HAETAE_Keccak1600.keccak_f1600_lanes (lanes_of_word_state a).
proof.
rewrite -word_rounds24
        -KeygenKeccak1600Spec.keccak_rounds24.
apply word_rounds_lanes.
smt().
qed.

lemma keccak_f1600_state_of_barray_bridge (a : BArray200.t) :
  lanes_of_word_state (keccak_f1600 (word_state_of_barray a)) =
  HAETAE_Keccak1600.keccak_f1600_lanes
    (KeygenKeccak1600Spec.state_of_barray a).
proof.
by rewrite keccak_f1600_lanes state_of_barray_lanes.
qed.


end Word.

end KeygenKeccak1600Spec.
