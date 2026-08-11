require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import HbzPrepareTarget HbzApplyTarget.

theory Mode2HbzCodecSpec.

op mode2_hbz_count : int = 1024.
op mode2_hbz_capacity : int = 2048.
op mode2_hbz_alphabet : int = 13.
op mode2_hbz_offset : int = 6.
op rans_scale_bits : int = 10.
op rans_scale : int = 1024.
op rans_initial_state : int = 8388608.

op hbz_symbol_word (w : W32.t) : W8.t =
  W8.of_int (W32.to_sint w + mode2_hbz_offset).

op canonical_hbz_mode2 (hbz : BArray8192.t) : bool =
  forall i, 0 <= i < mode2_hbz_count =>
    -mode2_hbz_offset <= W32.to_sint (BArray8192.get32 hbz i) <
      mode2_hbz_alphabet - mode2_hbz_offset.

op prepared_hbz_prefix
    (symbols : BArray2048.t) (hbz : BArray8192.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray2048.get8 symbols i = hbz_symbol_word (BArray8192.get32 hbz i).

op decoded_hbz_prefix
    (decoded original : BArray8192.t) (n : int) : bool =
  forall i, 0 <= i < n =>
    BArray8192.get32 decoded i = BArray8192.get32 original i.

op byte_tail_frame
    (before after : BArray2048.t) (start : int) : bool =
  forall i, start <= i < mode2_hbz_capacity =>
    BArray2048.get8 after i = BArray2048.get8 before i.

op coeff_tail_frame
    (before after : BArray8192.t) (start : int) : bool =
  forall i, start <= i < mode2_hbz_capacity =>
    BArray8192.get32 after i = BArray8192.get32 before i.

lemma prepared_hbz_prefix_zero symbols hbz :
  prepared_hbz_prefix symbols hbz 0.
proof. rewrite /prepared_hbz_prefix; smt(). qed.

lemma decoded_hbz_prefix_zero decoded original :
  decoded_hbz_prefix decoded original 0.
proof. rewrite /decoded_hbz_prefix; smt(). qed.

lemma byte_tail_frame_refl bytes start :
  byte_tail_frame bytes bytes start.
proof. rewrite /byte_tail_frame; trivial. qed.

lemma coeff_tail_frame_refl coeffs start :
  coeff_tail_frame coeffs coeffs start.
proof. rewrite /coeff_tail_frame; trivial. qed.

lemma prepared_hbz_prefix_step symbols hbz n :
  0 <= n < mode2_hbz_count =>
  prepared_hbz_prefix symbols hbz n =>
  prepared_hbz_prefix
    (BArray2048.set8 symbols n (hbz_symbol_word (BArray8192.get32 hbz n)))
    hbz (n + 1).
proof.
move=> hn hp.
rewrite /prepared_hbz_prefix => i hi.
rewrite BArray2048.get_setE 1:/#.
case (i = n) => heq.
+ by subst i.
+ apply hp; smt().
qed.

lemma decoded_hbz_prefix_step decoded original n :
  0 <= n < mode2_hbz_count =>
  decoded_hbz_prefix decoded original n =>
  decoded_hbz_prefix
    (BArray8192.set32 decoded n (BArray8192.get32 original n))
    original (n + 1).
proof.
move=> hn hp.
rewrite /decoded_hbz_prefix => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i = n) => heq.
+ by subst i.
+ rewrite ifF 1:/#.
  apply hp; smt().
qed.

lemma byte_tail_frame_set_before before after start idx value :
  0 <= idx < start =>
  byte_tail_frame before after start =>
  byte_tail_frame before (BArray2048.set8 after idx value) start.
proof.
move=> hidx hframe.
rewrite /byte_tail_frame => i hi.
rewrite BArray2048.get_setE 1:/#.
rewrite ifF 1:/#.
apply hframe; exact hi.
qed.

lemma coeff_tail_frame_set_before before after start idx value :
  0 <= idx < start =>
  coeff_tail_frame before after start =>
  coeff_tail_frame before (BArray8192.set32 after idx value) start.
proof.
move=> hidx hframe.
rewrite /coeff_tail_frame => i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
rewrite ifF 1:/#.
apply hframe; exact hi.
qed.

lemma canonical_hbz_symbol_bounds hbz i :
  canonical_hbz_mode2 hbz =>
  0 <= i < mode2_hbz_count =>
  0 <= W32.to_sint (BArray8192.get32 hbz i) + mode2_hbz_offset <
    mode2_hbz_alphabet.
proof.
rewrite /canonical_hbz_mode2 /mode2_hbz_offset
        /mode2_hbz_alphabet /mode2_hbz_count.
smt().
qed.

lemma zeroextu32_word (byte : W8.t) :
  zeroextu32 byte = W32.of_int (W8.to_uint byte).
proof.
apply W32.to_uint_eq.
rewrite W4u8.to_uint_zeroextu32 W32.of_uintK /=.
have hbyte := W8.to_uint_cmp byte.
by rewrite modz_small 1:/#.
qed.

lemma hbz_symbol_word_uint (w : W32.t) :
  -mode2_hbz_offset <= W32.to_sint w <
    mode2_hbz_alphabet - mode2_hbz_offset =>
  W8.to_uint (hbz_symbol_word w) =
    W32.to_sint w + mode2_hbz_offset.
proof.
move=> hw.
rewrite /hbz_symbol_word W8.of_uintK /=.
rewrite modz_small.
+ rewrite /mode2_hbz_offset /mode2_hbz_alphabet in hw.
  smt().
+ trivial.
qed.

lemma hbz_symbol_word_zeroext (w : W32.t) :
  -mode2_hbz_offset <= W32.to_sint w <
    mode2_hbz_alphabet - mode2_hbz_offset =>
  zeroextu32 (hbz_symbol_word w) =
    W32.of_int (W32.to_sint w + mode2_hbz_offset).
proof.
move=> hw.
rewrite zeroextu32_word (hbz_symbol_word_uint w hw).
trivial.
qed.

lemma w32_of_sintK (w : W32.t) :
  W32.of_int (W32.to_sint w) = w.
proof.
rewrite /W32.to_sint /W32.smod.
case (2 ^ (W32.size - 1) <= W32.to_uint w) => _.
+ by rewrite -W32.of_intS' W32.to_uintK'
             W32.of_int_modulus subr0.
+ by rewrite W32.to_uintK'.
qed.

lemma hbz_apply_symbol_inverse (w : W32.t) :
  -mode2_hbz_offset <= W32.to_sint w <
    mode2_hbz_alphabet - mode2_hbz_offset =>
  zeroextu32 (hbz_symbol_word w) - W32.of_int mode2_hbz_offset = w.
proof.
move=> hw.
rewrite hbz_symbol_word_zeroext 1:hw.
rewrite W32.of_intS'.
have -> :
    W32.to_sint w + mode2_hbz_offset - mode2_hbz_offset =
    W32.to_sint w by ring.
exact (w32_of_sintK w).
qed.

lemma w64_sar_nonnegative (w : W64.t) (k : int) :
  0 <= k =>
  W64.to_uint w < 9223372036854775808 =>
  W64.sar w k = w `>>>` k.
proof.
move=> hk hw.
apply W64.ext_eq => i hi.
rewrite /W64.sar /W64.(`|>>>`) W64.initiE 1:hi.
rewrite /W64.(`>>>`) W64.initiE 1:hi /=.
case (63 < i + k) => hik.
+ have hmin : min 63 (i + k) = 63 by smt().
  rewrite hmin W64.get_to_uint /=.
  have hdiv : W64.to_uint w %/ 2 ^ 63 = 0.
  + apply divz_small.
    apply bound_abs.
    have hpow : 2 ^ 63 = 9223372036854775808 by trivial.
    rewrite hpow.
    smt(W64.to_uint_cmp).
  rewrite hdiv /=.
  by rewrite W64.get_out 1:/#.
+ have hmin : min 63 (i + k) = i + k by smt().
  rewrite hmin.
  case (0 <= i + k < 64) => hb.
  + done.
  have hout : !(0 <= i + k < 64) by smt().
  by rewrite W64.get_out 1:hout.
qed.

lemma w64_sar_nonnegative_of_int (x k : int) :
  0 <= x < 9223372036854775808 =>
  0 <= k =>
  W64.sar (W64.of_int x) k = W64.of_int (x %/ 2 ^ k).
proof.
move=> hx hk.
rewrite w64_sar_nonnegative 1:hk.
+ rewrite W64.to_uint_small 1:/#.
  smt().
rewrite W64.shrDP 1:hk.
rewrite (modz_small x W64.modulus).
+ apply bound_abs.
  smt().
by [].
qed.

lemma hbz_prepare_tmp_word (w : W32.t) :
  sigextu64 w + W64.of_int mode2_hbz_offset =
    W64.of_int (W32.to_sint w + mode2_hbz_offset).
proof.
rewrite /sigextu64 W64.of_intD'.
trivial.
qed.

lemma hbz_prepare_tmp_uint (w : W32.t) :
  -mode2_hbz_offset <= W32.to_sint w <
    mode2_hbz_alphabet - mode2_hbz_offset =>
  W64.to_uint (sigextu64 w + W64.of_int mode2_hbz_offset) =
    W32.to_sint w + mode2_hbz_offset.
proof.
move=> hw.
rewrite hbz_prepare_tmp_word W64.to_uint_small.
+ rewrite /mode2_hbz_offset /mode2_hbz_alphabet in hw.
  smt().
+ trivial.
qed.

lemma hbz_prepare_neg_zero (w : W32.t) :
  -mode2_hbz_offset <= W32.to_sint w <
    mode2_hbz_alphabet - mode2_hbz_offset =>
  (sigextu64 w + W64.of_int mode2_hbz_offset) `|>>`
      W8.of_int 63 = W64.zero.
proof.
move=> hw.
rewrite hbz_prepare_tmp_word /(`|>>`) W8.of_uintK /=.
rewrite w64_sar_nonnegative_of_int.
+ rewrite /mode2_hbz_offset /mode2_hbz_alphabet in hw.
  smt().
+ smt().
rewrite divz_small 1:/#.
trivial.
qed.

lemma hbz_prepare_tmp_lt_alphabet (w : W32.t) :
  -mode2_hbz_offset <= W32.to_sint w <
    mode2_hbz_alphabet - mode2_hbz_offset =>
  ! (W64.of_int mode2_hbz_alphabet \ule
       (sigextu64 w + W64.of_int mode2_hbz_offset)).
proof.
move=> hw.
rewrite W64.uleE !W64.of_uintK /= hbz_prepare_tmp_uint 1:hw.
rewrite /mode2_hbz_offset /mode2_hbz_alphabet in hw.
smt().
qed.

lemma hbz_prepare_truncate_symbol (w : W32.t) :
  -mode2_hbz_offset <= W32.to_sint w <
    mode2_hbz_alphabet - mode2_hbz_offset =>
  truncateu8 (sigextu64 w + W64.of_int mode2_hbz_offset) =
    hbz_symbol_word w.
proof.
move=> hw.
apply W8.to_uint_eq.
rewrite W8u8.to_uint_truncateu8 hbz_prepare_tmp_uint 1:hw.
rewrite hbz_symbol_word_uint 1:hw.
rewrite modz_small.
+ rewrite /mode2_hbz_offset /mode2_hbz_alphabet in hw.
  smt().
+ trivial.
qed.

lemma canonical_hbz_mode2_satisfiable :
  exists hbz, canonical_hbz_mode2 hbz.
proof.
exists (BArray8192.init (fun _ => W8.zero)).
rewrite /canonical_hbz_mode2 => i hi.
have hz :
    BArray8192.get32 (BArray8192.init (fun _ => W8.zero)) i = W32.zero.
+ apply W32.ext_eq => bit hbit.
  rewrite W4u8.get_bits8 1:hbit.
  rewrite BArray8192.get32d_byte 1:/#.
  rewrite BArray8192.initiE 1:/# W8.zerowE W32.zerowE.
  trivial.
rewrite hz W32.to_sintE W32.to_uint0
        /mode2_hbz_offset /mode2_hbz_alphabet /=.
smt().
qed.

end Mode2HbzCodecSpec.
