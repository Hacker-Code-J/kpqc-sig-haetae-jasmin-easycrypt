(* -------------------------------------------------------------------- *)
(* Cancellation lemmas for WArray5120 / W32 / W256 word packing.         *)
(* Used by the mask-copy loop proof in ml_dsa_65_sign_correct.           *)
(* -------------------------------------------------------------------- *)

require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import Array1280 WArray5120.

(* init32 is a right inverse of get32 at aligned W32 positions. *)
lemma get32_init32 (f : int -> W32.t) (i : int) :
  0 <= i < 1280 =>
  WArray5120.get32 (WArray5120.init32 f) i = f i.
proof.
move => Hi.
rewrite /WArray5120.get32_direct /WArray5120.init32 /W4u8.pack4_t /=.
apply W32.wordP => k kb.
rewrite W32.initiE 1:/# /=.
rewrite W4u8.Pack.initiE 1:/# /=.
rewrite WArray5120.initiE 1:/# /=.
rewrite (_: (4 * i + k %/ 8) %/ 4 = i) 1:/#.
rewrite (_: (4 * i + k %/ 8) %% 4 = k %/ 8) 1:/#.
by rewrite W4u8.get_bits8 1:/# /#.
qed.

(* get32 reading over set256_direct, aligned j, i in word domain. *)
lemma get32_set256_direct_eq (t : WArray5120.t) (j i : int) (w : W256.t) :
  0 <= j =>
  j + 32 <= 5120 =>
  j %% 4 = 0 =>
  0 <= i < 1280 =>
  WArray5120.get32 (WArray5120.set256_direct t j w) i =
  if j %/ 4 <= i < j %/ 4 + 8
  then w \bits32 (i - j %/ 4)
  else WArray5120.get32 t i.
proof.
move => Hj_lo Hj_hi Hj_mod Hi.
rewrite /WArray5120.get32_direct /=.
apply W32.wordP => k kb.
rewrite /W4u8.pack4_t W32.initiE 1:/# /=.
rewrite W4u8.Pack.initiE 1:/# /=.
rewrite /WArray5120.set256_direct WArray5120.initiE 1:/# /=.
case (j %/ 4 <= i < j %/ 4 + 8) => Hi_region.
+ rewrite (_: j <= 4 * i + k %/ 8 < j + 32) 1:/# /=.
  rewrite /W8u32.(\bits32) /W32u8.(\bits8).
  rewrite W32.initiE 1:/# /=.
  rewrite W8.initiE 1:/# /=.
  congr; smt().
+ rewrite (_: !(j <= 4 * i + k %/ 8 < j + 32)) 1:/# /=.
  rewrite /WArray5120.get32_direct /W4u8.pack4_t.
  rewrite W32.initiE 1:/# /=.
  rewrite W4u8.Pack.initiE 1:/# /=.
  done.
qed.

(* get256_direct of init32, aligned, extracting the k-th W32 lane. *)
lemma get256_direct_init32_bits32 (f : int -> W32.t) (j k : int) :
  0 <= j =>
  j + 32 <= 5120 =>
  j %% 4 = 0 =>
  0 <= k < 8 =>
  (WArray5120.get256_direct (WArray5120.init32 f) j) \bits32 k = f (j %/ 4 + k).
proof.
move => Hj_lo Hj_hi Hj_mod Hk.
rewrite /get256_direct /W8u32.(\bits32) /=.
apply W32.wordP => b bb.
rewrite W32.initiE 1:/# /=.
rewrite pack32wE 1:/#.
rewrite W32u8.Pack.initiE 1:/# /=.
rewrite /init32 WArray5120.initiE 1:/# /=.
rewrite (_: (j + (k * 32 + b) %/ 8) %/ 4 = j %/ 4 + k) 1:/#.
rewrite (_: (j + (k * 32 + b) %/ 8) %% 4 = b %/ 8) 1:/#.
rewrite (_: (k * 32 + b) %% 8 = b %% 8) 1:/#.
by rewrite W4u8.get_bits8 1:/# /#.
qed.
