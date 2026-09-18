require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import BArray8192 BArray200 BArray40 Array5 Array24 Array25.

(* Byte-serialization lemmas adapted from the historical KeygenShakeStreamSpec.
   This local specification concerns one 136-byte block and its returned state;
   it does not identify the permutation with a FIPS sponge or stream. *)
theory SHAKEBlockSpec.

op drop_byte (w : W64.t) (_ : int) : W64.t =
  w `>>` (W8.of_int 8).

op drop_bytes (w : W64.t) (count : int) : W64.t =
  foldl drop_byte w (iota_ 0 count).

op rate_lane_byte
    (state : BArray200.t) (lane byte : int) : W8.t =
  truncateu8 (drop_bytes (BArray200.get64 state lane) byte).

op rate_prefix_matches
    (out : BArray8192.t) (outoff : int)
    (state : BArray200.t) (count : int) : bool =
  forall lane byte,
    0 <= lane =>
    0 <= byte < 8 =>
    8 * lane + byte < count =>
    BArray8192.get8 out (outoff + 8 * lane + byte) =
      rate_lane_byte state lane byte.

op rate_block_matches
    (out : BArray8192.t) (outoff : int)
    (state : BArray200.t) (rate : int) : bool =
  rate_prefix_matches out outoff state rate.

op rate_block_frame
    (before after : BArray8192.t) (outoff rate : int) : bool =
  forall byte_index,
    0 <= byte_index < BArray8192.size =>
    !(outoff <= byte_index < outoff + rate) =>
    BArray8192.get8 after byte_index =
      BArray8192.get8 before byte_index.

lemma drop_bytes0 w : drop_bytes w 0 = w.
proof. by rewrite /drop_bytes iota0. qed.

lemma drop_bytes_succ w count :
  0 <= count =>
  drop_bytes w (count + 1) =
    drop_bytes w count `>>` (W8.of_int 8).
proof.
move=> hcount.
by rewrite /drop_bytes iotaSr 1:// foldl_rcons /drop_byte.
qed.

lemma rate_prefix_zero out outoff state :
  rate_prefix_matches out outoff state 0.
proof. by rewrite /rate_prefix_matches => lane byte /#. qed.

lemma rate_prefix_set_next out outoff state count lane byte :
  0 <= outoff =>
  count = 8 * lane + byte =>
  0 <= lane =>
  0 <= byte < 8 =>
  outoff + count < BArray8192.size =>
  rate_prefix_matches out outoff state count =>
  rate_prefix_matches
    (BArray8192.set8 out (outoff + count)
      (rate_lane_byte state lane byte))
    outoff state (count + 1).
proof.
rewrite /rate_prefix_matches.
move=> hoff hcount hlane hbyte hcap hprefix lane0 byte0
        hlane0 hbyte0 hlt.
case (8 * lane0 + byte0 = count) => heq.
+ have -> : lane0 = lane by smt().
  have -> : byte0 = byte by smt().
  rewrite BArray8192.set_eqiE 1:/# 1:/#.
  trivial.
rewrite BArray8192.set_neqiE 1:/#.
have hprev : 8 * lane0 + byte0 < count by smt().
exact (hprefix lane0 byte0 hlane0 hbyte0 hprev).
qed.

lemma div8_split i :
  0 <= i => i %% 8 = 0 => i = 8 * (i %/ 8).
proof.
move=> hi hmod.
have hdiv := divz_eq i 8.
smt().
qed.

lemma rate_prefix_set_cursor out outoff state i j :
  0 <= outoff =>
  0 <= i =>
  i %% 8 = 0 =>
  0 <= j < 8 =>
  outoff + (i + j) < BArray8192.size =>
  rate_prefix_matches out outoff state (i + j) =>
  rate_prefix_matches
    (BArray8192.set8 out (outoff + (i + j))
      (rate_lane_byte state (i %/ 8) j))
    outoff state (i + j + 1).
proof.
move=> hoff hi himod hj hcap hprefix.
apply (rate_prefix_set_next out outoff state (i + j) (i %/ 8) j).
+ exact hoff.
+ have hi8 := div8_split i hi himod.
  smt().
+ have hd : 0 < 8 by smt().
  have hdiv := divz_ge0 i 8 hd.
  smt().
+ exact hj.
+ exact hcap.
exact hprefix.
qed.

lemma rate_block_frame_refl out outoff rate :
  rate_block_frame out out outoff rate.
proof. by rewrite /rate_block_frame. qed.

lemma rate_block_frame_set_inside before current outoff rate count w :
  0 <= outoff =>
  0 <= count < rate =>
  outoff + rate <= BArray8192.size =>
  rate_block_frame before current outoff rate =>
  rate_block_frame before
    (BArray8192.set8 current (outoff + count) w) outoff rate.
proof.
rewrite /rate_block_frame.
move=> hoff hcount hcap hframe byte_index hindex hout.
rewrite BArray8192.set_neqiE 1:/#.
exact (hframe byte_index hindex hout).
qed.

lemma barray_get64_byte_le (a : BArray200.t) lane byte :
  0 <= lane < 25 =>
  0 <= byte < 8 =>
  BArray200.get64 a lane \bits8 byte =
  BArray200.get8 a (8 * lane + byte).
proof.
move=> hlane hbyte.
rewrite BArray200.get64dE.
rewrite W8u8.get_pack8.
+ by rewrite BArray200.size_sub.
by rewrite BArray200.nth_sub.
qed.

lemma drop_bytes_shrw w count :
  0 <= count =>
  drop_bytes w count = w `>>>` (8 * count).
proof.
move: count.
apply intind.
+ apply W64.wordP => bit hbit.
  rewrite /drop_bytes.
  rewrite iota0 1:/#.
  rewrite /=.
  by rewrite hbit /=.
+ move=> count hcount ih.
  rewrite /= in ih.
  rewrite /=.
  rewrite drop_bytes_succ 1:// ih.
  rewrite /(`>>`) W8.of_uintK /=.
  rewrite W64.shrw_add 1:/# 1:/#.
  congr; ring.
qed.

lemma rate_lane_byte_get8 state lane byte :
  0 <= lane < 25 =>
  0 <= byte < 8 =>
  rate_lane_byte state lane byte =
    BArray200.get8 state (8 * lane + byte).
proof.
move=> hlane hbyte.
rewrite /rate_lane_byte drop_bytes_shrw 1:/#.
rewrite -barray_get64_byte_le 1:// 1://.
apply W8.to_uint_eq.
rewrite to_uint_truncateu8 W64.to_uint_shr 1:/#.
rewrite W8u8.bits8_div 1:/# /=.
trivial.
qed.

lemma rate_block_bytes out outoff state :
  rate_block_matches out outoff state 136 =>
  forall j, 0 <= j < 136 =>
    BArray8192.get8 out (outoff + j) = BArray200.get8 state j.
proof.
  rewrite /rate_block_matches /rate_prefix_matches.
  move=> hp j hj.
  have hq : 0 <= j %/ 8 < 25 by smt(divz_cmp).
  have hr : 0 <= j %% 8 < 8 by smt(modz_cmp).
  have heq : j = 8 * (j %/ 8) + j %% 8 by smt(divz_eq).
  have hlane : 0 <= j %/ 8 by smt().
  have hinside : 8 * (j %/ 8) + j %% 8 < 136 by smt().
  have h := hp (j %/ 8) (j %% 8) hlane hr hinside.
  rewrite rate_lane_byte_get8 1:hq 1:hr in h.
  smt().
qed.

(* Pure 24-round word specification adapted from the historical
   KeygenKeccak1600Spec.Word section. No bit-level/FIPS or stream model is
   imported; concrete constants and round operations are explicit below. *)
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

end Word.

end SHAKEBlockSpec.
