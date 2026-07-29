require import AllCore IntDiv List Ring StdOrder BitEncoding Bigalg.

require import KeygenM23ComplexReal KeygenM23IdealRootDFT.

import IntOrder BitReverse.
import KeygenM23ComplexReal KeygenM23IdealRootDFT.

theory KeygenM23IdealFFTSchedule.

(* Finite complex sums, instantiated from the proved additive big-operator
   theory.  The direct realizations keep this file independent of any
   project-authored unproved algebraic assumption. *)
clone import Bigalg.BigZModule as CB with
  type ZM.t <- complex,
  op ZM.zeror <- czero,
  op ZM.(+) <- cadd,
  op ZM.([-]) <- cneg
  proof *.

realize ZM.addrA.
proof.
move=> x y z.
apply complex_ext.
+ rewrite !creal_add.
  ring.
+ rewrite !cimag_add.
  ring.
qed.

realize ZM.addrC.
proof.
move=> x y.
apply complex_ext.
+ rewrite !creal_add.
  ring.
+ rewrite !cimag_add.
  ring.
qed.

realize ZM.add0r.
proof.
move=> x.
apply complex_ext.
+ rewrite creal_add creal_zero.
  ring.
+ rewrite cimag_add cimag_zero.
  ring.
qed.

realize ZM.addNr.
proof.
move=> x.
apply complex_ext.
+ rewrite creal_add creal_neg creal_zero.
  ring.
+ rewrite cimag_add cimag_neg cimag_zero.
  ring.
qed.

type cvector = int -> complex.

op csum_range (n : int) (f : int -> complex) : complex =
  CB.bigi predT f 0 n.

lemma csum_range256E f :
  csum_range 256 f = csum256 f.
proof.
by rewrite /csum_range /CB.big filter_predT /range
           /csum256 /csum.
qed.

lemma cmul_csum_range (z : complex) (n : int) (f : int -> complex) :
  cmul z (csum_range n f) =
  csum_range n (fun i => cmul z (f i)).
proof.
rewrite /csum_range.
apply (CB.big_distrr cmul).
+ exact cmul0.
+ exact cmul_add.
qed.

lemma pow2_8 :
  (2 ^ 8)%Int = 256.
proof. by ring. qed.

lemma pow2S (n : int) :
  0 <= n =>
  2 ^ (n + 1) = 2 * 2 ^ n.
proof. by move=> hn; rewrite exprS. qed.

lemma dft_root_pow128 :
  cpow dft_root 128 = cneg cone.
proof. by rewrite dft_root_power /ideal_root omega512_pow256. qed.

lemma dft_root_pow256 :
  cpow dft_root 256 = cone.
proof. by rewrite dft_root_power /ideal_root omega512_pow512. qed.

lemma dft_root_pow256_mul (q : int) :
  cpow dft_root (256 * q) = cone.
proof. by rewrite C.exprM dft_root_pow256 C.expr1z. qed.

lemma dft_root_periodic (e q : int) :
  0 <= e =>
  0 <= q =>
  cpow dft_root (e + 256 * q) = cpow dft_root e.
proof.
move=> he hq.
rewrite C.exprD_nneg 1:he 1:/# dft_root_pow256_mul.
exact cmul1r.
qed.

lemma dft_root_half_turn (e : int) :
  0 <= e =>
  cpow dft_root (e + 128) = cneg (cpow dft_root e).
proof.
move=> he.
rewrite C.exprD_nneg 1:he 1:// dft_root_pow128 cmul_neg.
by rewrite cmul1r.
qed.

lemma bsrev8_range (i : int) :
  bsrev 8 i \in range 0 256.
proof. by move: (bsrev_range 8 i); rewrite pow2_8. qed.

lemma bsrev8_involutive (i : int) :
  i \in range 0 256 =>
  bsrev 8 (bsrev 8 i) = i.
proof.
move=> hi.
apply bsrev_involutive.
+ by smt().
+ by rewrite pow2_8.
qed.

lemma bsrev8_add_pow2 (s i : int) :
  s \in range 0 8 =>
  i \in range 0 (2 ^ s) =>
  bsrev 8 (2 ^ s + i) = 2 ^ (7 - s) + bsrev 8 i.
proof.
move=> hs hi.
rewrite addrC (bsrev_add s 8 i 1).
+ by rewrite mem_range in hs; smt().
+ exact hi.
rewrite bsrev1 1:/#.
have hpow :
  2 ^ 7 %/ 2 ^ s = 2 ^ (7 - s).
+ rewrite expz_div.
  + by rewrite mem_range in hs; smt().
  + by [].
  + by [].
by rewrite hpow addrC.
qed.

lemma bsrev8_low_factor (s i : int) :
  s \in range 0 9 =>
  i \in range 0 (2 ^ s) =>
  bsrev 8 i = 2 ^ (8 - s) * bsrev s i.
proof.
move=> hs hi.
rewrite (bsrev_cat s 8 i).
+ by rewrite mem_range in hs; smt().
have hdiv : i %/ 2 ^ s = 0
  by rewrite divz_small; rewrite mem_range in hi; smt().
rewrite hdiv bsrev0.
by rewrite add0r.
qed.

lemma pow2_stage_product (s : int) :
  s \in range 0 9 =>
  2 ^ s * 2 ^ (8 - s) = 256.
proof.
move=> hs.
rewrite -exprD_nneg.
+ by rewrite mem_range in hs; smt().
+ by rewrite mem_range in hs; smt().
have -> : s + (8 - s) = 8 by ring.
exact pow2_8.
qed.

lemma bsrev8_low_period (s i : int) :
  s \in range 0 9 =>
  i \in range 0 (2 ^ s) =>
  2 ^ s * bsrev 8 i = 256 * bsrev s i.
proof.
move=> hs hi.
rewrite (bsrev8_low_factor s i hs hi).
by smt(pow2_stage_product).
qed.

(* A block-local transform.  At length one it is the bit-reversed input;
   doubling the length is exactly one simultaneous DIT butterfly stage. *)
op partial_dft
    (input : cvector) (len k block : int) : complex =
  csum_range len
    (fun j =>
      cmul (input (bsrev 8 (block * len + j)))
        (cpow dft_root (k * bsrev 8 j))).

op ideal_bitrev8 (input : cvector) : cvector =
  fun i => input (bsrev 8 i).

lemma partial_dft1 (input : cvector) (block : int) :
  partial_dft input 1 0 block = ideal_bitrev8 input block.
proof.
rewrite /partial_dft /csum_range CB.big_int1 /ideal_bitrev8 /=.
by rewrite C.expr0 cmul1r.
qed.

lemma pow2_stage_half (s : int) :
  s \in range 0 8 =>
  2 ^ s * 2 ^ (7 - s) = 128.
proof.
move=> hs.
rewrite -exprD_nneg.
+ by rewrite mem_range in hs; smt().
+ by rewrite mem_range in hs; smt().
have -> : s + (7 - s) = 7 by ring.
by ring.
qed.

lemma dft_root_high_low_shift (s k i : int) :
  s \in range 0 8 =>
  k \in range 0 (2 ^ s) =>
  i \in range 0 (2 ^ s) =>
  cpow dft_root ((2 ^ s + k) * bsrev 8 i) =
  cpow dft_root (k * bsrev 8 i).
proof.
move=> hs hk hi.
have hs9 : s \in range 0 9 by
  rewrite mem_range in hs; rewrite mem_range; smt().
have hperiod := bsrev8_low_period s i hs9 hi.
have hrev8 : 0 <= bsrev 8 i by
  move: (bsrev8_range i); rewrite mem_range; smt().
have hrev : 0 <= bsrev s i by
  move: (bsrev_range s i); rewrite mem_range; smt().
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have -> :
  (2 ^ s + k) * bsrev 8 i =
  k * bsrev 8 i + 256 * bsrev s i by smt().
by rewrite dft_root_periodic 1:/# 1:/#.
qed.

lemma dft_root_high_high_shift (s k i : int) :
  s \in range 0 8 =>
  k \in range 0 (2 ^ s) =>
  i \in range 0 (2 ^ s) =>
  cpow dft_root
    ((2 ^ s + k) * (2 ^ (7 - s) + bsrev 8 i)) =
  cneg
    (cmul (cpow dft_root (k * 2 ^ (7 - s)))
          (cpow dft_root (k * bsrev 8 i))).
proof.
move=> hs hk hi.
have hs9 : s \in range 0 9 by
  rewrite mem_range in hs; rewrite mem_range; smt().
have hperiod := bsrev8_low_period s i hs9 hi.
have hhalf := pow2_stage_half s hs.
have hrev8 : 0 <= bsrev 8 i by
  move: (bsrev8_range i); rewrite mem_range; smt().
have hrev : 0 <= bsrev s i by
  move: (bsrev_range s i); rewrite mem_range; smt().
have hk0 : 0 <= k by rewrite mem_range in hk; smt().
have htw : 0 <= 2 ^ (7 - s)
  by apply expr_ge0.
have -> :
  (2 ^ s + k) * (2 ^ (7 - s) + bsrev 8 i) =
  (k * 2 ^ (7 - s) + k * bsrev 8 i + 128) +
  256 * bsrev s i by smt().
rewrite dft_root_periodic 1:/# 1:/#.
rewrite dft_root_half_turn 1:/#.
rewrite C.exprD_nneg 1:/# 1:/#.
done.
qed.

lemma partial_dft_split_low
    (input : cvector) (s k block : int) :
  s \in range 0 8 =>
  k \in range 0 (2 ^ s) =>
  block \in range 0 (2 ^ (7 - s)) =>
  partial_dft input (2 ^ (s + 1)) k block =
  cadd
    (partial_dft input (2 ^ s) k (2 * block))
    (cmul (cpow dft_root (k * 2 ^ (7 - s)))
          (partial_dft input (2 ^ s) k (2 * block + 1))).
proof.
move=> hs hk hblock.
rewrite /partial_dft cmul_csum_range /csum_range.
rewrite (CB.big_cat_int (2 ^ s) 0 (2 ^ (s + 1))).
+ by rewrite expr_ge0.
+ have hs0 : 0 <= s by rewrite mem_range in hs; smt().
  by rewrite pow2S //; smt(expr_ge0).
congr.
+ apply CB.eq_big_int => i hi /=.
  have hs0 : 0 <= s by rewrite mem_range in hs; smt().
  have -> :
    block * 2 ^ (s + 1) + i =
    (2 * block) * 2 ^ s + i.
  + rewrite pow2S //.
    ring.
  done.
have hs0 : 0 <= s by rewrite mem_range in hs; smt().
rewrite (CB.big_addn 0 (2 ^ (s + 1)) (2 ^ s)) /=.
have -> : 2 ^ (s + 1) - 2 ^ s = 2 ^ s.
+ rewrite pow2S //.
  ring.
apply CB.eq_big_int => i hi /=.
have hi' : i \in range 0 (2 ^ s) by rewrite mem_range.
have -> : i + 2 ^ s = 2 ^ s + i by ring.
rewrite (bsrev8_add_pow2 s i hs hi').
have -> :
  k * (2 ^ (7 - s) + bsrev 8 i) =
  k * 2 ^ (7 - s) + k * bsrev 8 i by ring.
rewrite C.exprD_nneg.
+ by rewrite mem_range in hk; smt(expr_ge0).
+ have hrev8 : 0 <= bsrev 8 i
     by move: (bsrev8_range i); rewrite mem_range; smt().
  by rewrite mem_range in hk; smt().
have -> :
  block * 2 ^ (s + 1) + (2 ^ s + i) =
  (2 * block + 1) * 2 ^ s + i.
+ rewrite pow2S //.
  ring.
apply complex_ext.
+ rewrite !creal_mul !cimag_mul.
  ring.
+ rewrite !cimag_mul !creal_mul.
  ring.
qed.

lemma partial_dft_split_high
    (input : cvector) (s k block : int) :
  s \in range 0 8 =>
  k \in range 0 (2 ^ s) =>
  block \in range 0 (2 ^ (7 - s)) =>
  partial_dft input (2 ^ (s + 1)) (2 ^ s + k) block =
  csub
    (partial_dft input (2 ^ s) k (2 * block))
    (cmul (cpow dft_root (k * 2 ^ (7 - s)))
          (partial_dft input (2 ^ s) k (2 * block + 1))).
proof.
move=> hs hk hblock.
rewrite /partial_dft /csub cmul_csum_range /csum_range.
rewrite (CB.big_cat_int (2 ^ s) 0 (2 ^ (s + 1))).
+ by rewrite expr_ge0.
+ have hs0 : 0 <= s by rewrite mem_range in hs; smt().
  by rewrite pow2S //; smt(expr_ge0).
congr.
+ apply CB.eq_big_int => i hi /=.
  have hi' : i \in range 0 (2 ^ s) by rewrite mem_range.
  rewrite (dft_root_high_low_shift s k i hs hk hi').
  have hs0 : 0 <= s by rewrite mem_range in hs; smt().
  have -> :
    block * 2 ^ (s + 1) + i =
    (2 * block) * 2 ^ s + i.
  + rewrite pow2S //.
    ring.
  done.
rewrite CB.sumrN.
have hs0 : 0 <= s by rewrite mem_range in hs; smt().
rewrite (CB.big_addn 0 (2 ^ (s + 1)) (2 ^ s)) /=.
have -> : 2 ^ (s + 1) - 2 ^ s = 2 ^ s.
+ rewrite pow2S //.
  ring.
apply CB.eq_big_int => i hi /=.
have hi' : i \in range 0 (2 ^ s) by rewrite mem_range.
have -> : i + 2 ^ s = 2 ^ s + i by ring.
rewrite (bsrev8_add_pow2 s i hs hi').
rewrite (dft_root_high_high_shift s k i hs hk hi').
have -> :
  block * 2 ^ (s + 1) + (2 ^ s + i) =
  (2 * block + 1) * 2 ^ s + i.
+ rewrite pow2S //.
  ring.
apply complex_ext.
+ rewrite /cmul /cneg /creal /cimag /=.
  ring.
+ rewrite /cmul /cneg /creal /cimag /=.
  ring.
qed.

(* The exact stage twiddle uses the same root-index stride as the machine
   schedule: k times 256, 128, ..., 2 across rounds zero through seven. *)
op ideal_twiddle (s k : int) : complex =
  ideal_root (2 ^ (8 - s) * k).

lemma ideal_twiddleE (s k : int) :
  s \in range 0 8 =>
  ideal_twiddle s k =
  cpow dft_root (k * 2 ^ (7 - s)).
proof.
move=> hs.
rewrite /ideal_twiddle dft_root_power.
congr.
have h7s : 0 <= 7 - s by rewrite mem_range in hs; smt().
have -> : 8 - s = (7 - s) + 1 by ring.
rewrite pow2S 1:h7s.
ring.
qed.

(* A simultaneous, pointwise butterfly stage.  Its definition is total on
   integer indices; the correctness lemmas below use only the canonical
   256-entry range. *)
op ideal_stage (data : cvector) (s : int) : cvector =
  fun i =>
    let half = 2 ^ s in
    let off = i %% (2 * half) in
    let k = off %% half in
    let base = i - off in
    let t =
      cmul (ideal_twiddle s k)
        (data (base + k + half)) in
    if off < half
    then cadd (data (base + k)) t
    else csub (data (base + k)) t.

lemma fft_low_offset (half block k : int) :
  0 < half =>
  k \in range 0 half =>
  (block * (2 * half) + k) %% (2 * half) = k.
proof.
move=> hhalf hk.
rewrite modzMDl.
by rewrite modz_small; rewrite mem_range in hk; smt().
qed.

lemma fft_high_offset (half block k : int) :
  0 < half =>
  k \in range 0 half =>
  (block * (2 * half) + (half + k)) %% (2 * half) = half + k.
proof.
move=> hhalf hk.
rewrite modzMDl.
by rewrite modz_small; rewrite mem_range in hk; smt().
qed.

lemma fft_low_inner_offset (half k : int) :
  0 < half =>
  k \in range 0 half =>
  k %% half = k.
proof.
move=> hhalf hk.
by rewrite modz_small; rewrite mem_range in hk; smt().
qed.

lemma fft_high_inner_offset (half k : int) :
  0 < half =>
  k \in range 0 half =>
  (half + k) %% half = k.
proof.
move=> hhalf hk.
have -> : half + k = 1 * half + k by ring.
rewrite modzMDl.
by rewrite modz_small; rewrite mem_range in hk; smt().
qed.

lemma ideal_stage_lowE
    (data : cvector) (s block k : int) :
  0 <= s =>
  k \in range 0 (2 ^ s) =>
  ideal_stage data s (block * 2 ^ (s + 1) + k) =
  cadd
    (data ((2 * block) * 2 ^ s + k))
    (cmul (ideal_twiddle s k)
          (data ((2 * block + 1) * 2 ^ s + k))).
proof.
move=> hs hk.
have hhalf : 0 < 2 ^ s by rewrite expr_gt0.
have hwidth : 2 ^ (s + 1) = 2 * 2 ^ s by rewrite pow2S.
rewrite /ideal_stage hwidth /=.
rewrite (fft_low_offset (2 ^ s) block k hhalf hk).
rewrite (fft_low_inner_offset (2 ^ s) k hhalf hk) /=.
rewrite ifT.
+ by rewrite mem_range in hk; smt().
have -> :
  block * (2 * 2 ^ s) + k - k + k =
  (2 * block) * 2 ^ s + k by ring.
have -> :
  (2 * block) * 2 ^ s + k + 2 ^ s =
  (2 * block + 1) * 2 ^ s + k by ring.
done.
qed.

lemma ideal_stage_highE
    (data : cvector) (s block k : int) :
  0 <= s =>
  k \in range 0 (2 ^ s) =>
  ideal_stage data s
    (block * 2 ^ (s + 1) + (2 ^ s + k)) =
  csub
    (data ((2 * block) * 2 ^ s + k))
    (cmul (ideal_twiddle s k)
          (data ((2 * block + 1) * 2 ^ s + k))).
proof.
move=> hs hk.
have hhalf : 0 < 2 ^ s by rewrite expr_gt0.
have hwidth : 2 ^ (s + 1) = 2 * 2 ^ s by rewrite pow2S.
rewrite /ideal_stage hwidth /=.
rewrite (fft_high_offset (2 ^ s) block k hhalf hk).
rewrite (fft_high_inner_offset (2 ^ s) k hhalf hk) /=.
rewrite ifF.
+ by rewrite mem_range in hk; smt().
have -> :
  block * (2 * 2 ^ s) + (2 ^ s + k) - (2 ^ s + k) + k =
  (2 * block) * 2 ^ s + k by ring.
have -> :
  (2 * block) * 2 ^ s + k + 2 ^ s =
  (2 * block + 1) * 2 ^ s + k by ring.
done.
qed.

op ideal_stage_spec
    (data input : cvector) (s : int) : bool =
  forall block k,
    block \in range 0 (2 ^ (8 - s)) =>
    k \in range 0 (2 ^ s) =>
    data (block * 2 ^ s + k) =
    partial_dft input (2 ^ s) k block.

lemma ideal_bitrev8_stage_spec (input : cvector) :
  ideal_stage_spec (ideal_bitrev8 input) input 0.
proof.
rewrite /ideal_stage_spec => block k hblock hk.
have -> : k = 0 by rewrite mem_range in hk; smt().
by rewrite expr0 /= partial_dft1.
qed.

lemma ideal_stage_spec_step
    (data input : cvector) (s : int) :
  s \in range 0 8 =>
  ideal_stage_spec data input s =>
  ideal_stage_spec (ideal_stage data s) input (s + 1).
proof.
move=> hs hspec.
rewrite /ideal_stage_spec in hspec.
rewrite /ideal_stage_spec.
move=> block out hblock hout.
have hs0 : 0 <= s by rewrite mem_range in hs; smt().
have h7s : 0 <= 7 - s by rewrite mem_range in hs; smt().
have hhalf : 0 < 2 ^ s by rewrite expr_gt0.
have hwidth : 2 ^ (s + 1) = 2 * 2 ^ s by rewrite pow2S.
have hblocks : 2 ^ (8 - s) = 2 * 2 ^ (7 - s).
+ have -> : 8 - s = (7 - s) + 1 by ring.
  by rewrite pow2S.
have hblock' : block \in range 0 (2 ^ (7 - s)).
+ move: hblock.
  have heq : 8 - (s + 1) = 7 - s by ring.
  by rewrite heq.
have hleft : 2 * block \in range 0 (2 ^ (8 - s)).
+ rewrite hblocks mem_range.
  rewrite mem_range in hblock'.
  smt().
have hright : 2 * block + 1 \in range 0 (2 ^ (8 - s)).
+ rewrite hblocks mem_range.
  rewrite mem_range in hblock'.
  have hpositive : 0 < 2 ^ (7 - s) by rewrite expr_gt0.
  smt().
case (out < 2 ^ s) => hout_low.
+ have hk : out \in range 0 (2 ^ s).
  + by rewrite mem_range in hout; rewrite mem_range; smt().
  rewrite (ideal_stage_lowE data s block out hs0 hk).
  rewrite (hspec (2 * block) out hleft hk).
  rewrite (hspec (2 * block + 1) out hright hk).
  rewrite (ideal_twiddleE s out hs).
  apply eq_sym.
  exact (partial_dft_split_low input s out block hs hk hblock').
have hk : out - 2 ^ s \in range 0 (2 ^ s).
+ rewrite mem_range in hout.
  rewrite mem_range.
  smt().
have houtE : out = 2 ^ s + (out - 2 ^ s) by ring.
rewrite {1}houtE.
rewrite (ideal_stage_highE data s block (out - 2 ^ s) hs0 hk).
rewrite (hspec (2 * block) (out - 2 ^ s) hleft hk).
rewrite (hspec (2 * block + 1) (out - 2 ^ s) hright hk).
rewrite (ideal_twiddleE s (out - 2 ^ s) hs).
apply eq_sym.
rewrite {1}houtE.
exact
  (partial_dft_split_high input s (out - 2 ^ s) block
     hs hk hblock').
qed.

(* This fold is the pure exact-complex schedule.  Relating its values to the
   rounded Q16 machine evaluator requires a separate error and safety bridge. *)
op ideal_schedule_prefix (input : cvector) (rounds : int) : cvector =
  foldl
    (fun data s => ideal_stage data s)
    (ideal_bitrev8 input)
    (iota_ 0 rounds).

op ideal_fft256 (input : cvector) : cvector =
  ideal_schedule_prefix input 8.

lemma ideal_schedule_prefix0 (input : cvector) :
  ideal_schedule_prefix input 0 = ideal_bitrev8 input.
proof. by rewrite /ideal_schedule_prefix iota0. qed.

lemma ideal_schedule_prefixS (input : cvector) (rounds : int) :
  0 <= rounds =>
  ideal_schedule_prefix input (rounds + 1) =
  ideal_stage (ideal_schedule_prefix input rounds) rounds.
proof.
move=> hrounds.
by rewrite /ideal_schedule_prefix iotaSr 1:hrounds foldl_rcons.
qed.

lemma ideal_schedule_prefix_stage_spec
    (input : cvector) (rounds : int) :
  0 <= rounds <= 8 =>
  ideal_stage_spec (ideal_schedule_prefix input rounds) input rounds.
proof.
move=> [hrounds0 hrounds8].
have hgeneral :
  forall rounds, 0 <= rounds =>
    rounds <= 8 =>
    ideal_stage_spec (ideal_schedule_prefix input rounds) input rounds.
+ apply intind.
  + move=> _.
    rewrite ideal_schedule_prefix0.
    exact ideal_bitrev8_stage_spec.
  + move=> s hs0 ih hs1.
    rewrite ideal_schedule_prefixS 1:hs0.
    apply ideal_stage_spec_step.
    + by rewrite mem_range; smt().
    + apply ih.
      smt().
exact (hgeneral rounds hrounds0 hrounds8).
qed.

lemma partial_dft256E (input : cvector) (k : int) :
  partial_dft input 256 k 0 = dft256 input k.
proof.
rewrite /partial_dft /dft256 -csum_range256E /csum_range /=.
have hperm :
  perm_eq (range 0 256) (map (bsrev 8) (range 0 256)).
+ rewrite perm_eq_sym.
  have h := bsrev_range_pow2_perm_eq 8 8 _.
  + by [].
  move: h.
  rewrite !pow2_8 expr0.
  have -> : map (( * ) 1) (range 0 256) = range 0 256.
  + by apply/id_map => x; ring.
  by [].
rewrite
  (CB.eq_big_perm _ _ _ (map (bsrev 8) (range 0 256))) 1:hperm.
rewrite CB.big_mapT.
apply CB.eq_big_int => j hj /=.
rewrite /(\o) /=.
have -> : bsrev 8 (bsrev 8 j) = j.
+ apply bsrev8_involutive.
  by rewrite mem_range; smt().
by [].
qed.

lemma ideal_fft256_correct (input : cvector) (k : int) :
  k \in range 0 256 =>
  ideal_fft256 input k = dft256 input k.
proof.
move=> hk.
have hspec := ideal_schedule_prefix_stage_spec input 8 _.
+ by smt().
rewrite /ideal_stage_spec in hspec.
have hblock : 0 \in range 0 (2 ^ (8 - 8)).
+ by rewrite mem_range expr0; smt().
have hk8 : k \in range 0 (2 ^ 8).
+ by rewrite pow2_8.
rewrite /ideal_fft256 (hspec 0 k hblock hk8) /=.
rewrite pow2_8.
exact (partial_dft256E input k).
qed.

lemma ideal_odd_fft256_correct (input : cvector) (k : int) :
  k \in range 0 256 =>
  ideal_fft256 (twist256 input) k = odd_dft256 input k.
proof.
move=> hk.
rewrite (ideal_fft256_correct (twist256 input) k hk).
apply eq_sym.
apply odd_dft256_twist.
by rewrite mem_range in hk; smt().
qed.

end KeygenM23IdealFFTSchedule.
