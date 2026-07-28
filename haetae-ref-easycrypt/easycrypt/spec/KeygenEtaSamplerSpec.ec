require import AllCore IntDiv List Ring StdOrder.

from Jasmin require import JModel_x86.

require import BArray8192 KeygenShakeStreamSpec.

theory KeygenEtaSamplerSpec.

op eta_poly_words_i : int = 256.
op eta_block_bytes_i : int = 136.
op eta_accept_bound_i : int = 243.
op eta_digits_per_byte_i : int = 5.

op poly_frame8192 (before after : BArray8192.t) (base : int) : bool =
  forall i,
    0 <= i < BArray8192.size %/ 4 =>
    !(base <= i < base + eta_poly_words_i) =>
    BArray8192.get32 after i = BArray8192.get32 before i.

op word_frame8192 (before after : BArray8192.t)
                  (base start stop : int) : bool =
  forall i,
    0 <= i < BArray8192.size %/ 4 =>
    !(base + start <= i < base + stop) =>
    BArray8192.get32 after i = BArray8192.get32 before i.

op centered_interval8192 (a : BArray8192.t)
                         (base start stop : int) : bool =
  forall i,
    start <= i < stop =>
    -1 <= W32.to_sint (BArray8192.get32 a (base + i)) <= 1.

op base3_residue (x : W32.t) : int = W32.to_uint x %% 3.

op centered_trit_value (x : W32.t) : int =
  if base3_residue x = 2 then -1 else base3_residue x.

op centered_trit (x : W32.t) : W32.t =
  W32.of_int (centered_trit_value x).

op eta_centered_digit (byte digit : int) : int =
  centered_trit_value (W32.of_int (byte %/ (3 ^ digit))).

op eta_decode_byte (byte : int) : int list =
  if 0 <= byte < eta_accept_bound_i then
    mkseq (eta_centered_digit byte) eta_digits_per_byte_i
  else [].

op eta_decode_bytes (bytes : int list) : int list =
  flatten (map eta_decode_byte bytes).

op eta_fill (values bytes : int list) : int list =
  take eta_poly_words_i (values ++ eta_decode_bytes bytes).

op eta_sufficient_prefix
    (seed : BArray128.t) (seedoff nonce : W64.t) (limit : int) : bool =
  1 <= limit /\
  size (eta_fill []
    (KeygenShakeStreamSpec.shake256_squeeze_bytes
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed seedoff nonce) limit)) = eta_poly_words_i.

op eta_prefix_count
    (seed : BArray128.t) (seedoff nonce : W64.t) (blocks : int) : int =
  size (eta_fill []
    (KeygenShakeStreamSpec.shake256_squeeze_bytes
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed seedoff nonce) blocks)).

(* As for the uniform sampler, this is an explicit deterministic progress
   certificate over a finite exact SHAKE prefix, not a distribution axiom. *)
op eta_progress_prefix
    (seed : BArray128.t) (seedoff nonce : W64.t) (limit : int) : bool =
  eta_sufficient_prefix seed seedoff nonce limit /\
  forall blocks,
    1 <= blocks < limit =>
    eta_prefix_count seed seedoff nonce blocks < eta_poly_words_i =>
    eta_prefix_count seed seedoff nonce blocks <
      eta_prefix_count seed seedoff nonce (blocks + 1).

op eta_decoded_prefix8192
    (a : BArray8192.t) (base : int) (values : int list) : bool =
  forall i,
    0 <= i < size values =>
    W32.to_sint (BArray8192.get32 a (base + i)) = nth 0 values i.

lemma base3_residue_range x :
  0 <= base3_residue x < 3.
proof.
rewrite /base3_residue.
by smt(W32.to_uint_cmp modz_cmp).
qed.

lemma centered_trit_value_range x :
  -1 <= centered_trit_value x <= 1.
proof.
have hrange := base3_residue_range x.
rewrite /centered_trit_value.
by smt().
qed.

lemma centered_trit_to_sint x :
  W32.to_sint (centered_trit x) = centered_trit_value x.
proof.
rewrite /centered_trit W32.of_sintK /W32.smod /=.
have hrange := centered_trit_value_range x.
by smt().
qed.

lemma centered_trit_range x :
  -1 <= W32.to_sint (centered_trit x) <= 1.
proof.
rewrite centered_trit_to_sint.
exact (centered_trit_value_range x).
qed.

lemma div3_via_171 x :
  0 <= x <= 242 =>
  (x * 171) %/ 512 = x %/ 3.
proof. move=> hx; smt(). qed.

lemma eta_decode_byte_accepted byte :
  0 <= byte < eta_accept_bound_i =>
  eta_decode_byte byte =
    mkseq (eta_centered_digit byte) eta_digits_per_byte_i.
proof. by move=> hbyte; rewrite /eta_decode_byte hbyte. qed.

lemma eta_decode_byte_rejected byte :
  !(0 <= byte < eta_accept_bound_i) =>
  eta_decode_byte byte = [].
proof. by move=> hbyte; rewrite /eta_decode_byte hbyte. qed.

lemma eta_decode_byte_size byte :
  size (eta_decode_byte byte) =
    if 0 <= byte < eta_accept_bound_i then eta_digits_per_byte_i else 0.
proof.
rewrite /eta_decode_byte.
case (0 <= byte < eta_accept_bound_i) => hbyte.
+ by rewrite size_mkseq.
by trivial.
qed.

lemma eta_decode_byte_nth byte digit :
  0 <= byte < eta_accept_bound_i =>
  0 <= digit < eta_digits_per_byte_i =>
  nth 0 (eta_decode_byte byte) digit = eta_centered_digit byte digit.
proof.
move=> hbyte hdigit.
by rewrite eta_decode_byte_accepted 1:// nth_mkseq.
qed.

lemma eta_div3_digit_succ byte digit :
  0 <= digit =>
  byte %/ (3 ^ (digit + 1)) = (byte %/ (3 ^ digit)) %/ 3.
proof.
move=> hdigit.
by rewrite exprSr 1:// divzMr 1:IntOrder.expr_ge0.
qed.

lemma eta_accepted_quotient_range byte digit :
  0 <= byte < eta_accept_bound_i =>
  0 <= digit =>
  0 <= byte %/ (3 ^ digit) <= 242.
proof.
move=> hbyte hdigit.
have hpow : 0 < 3 ^ digit by apply IntOrder.expr_gt0; smt().
have hlo : 0 <= byte %/ (3 ^ digit).
+ by rewrite divz_ge0 1:hpow; smt().
have hbyte0 : 0 <= byte by smt().
have hpow0 : 0 <= 3 ^ digit by smt().
have hhi := leq_div byte (3 ^ digit) hbyte0 hpow0.
rewrite /eta_accept_bound_i in hbyte.
by smt().
qed.

lemma eta_accepted_quotient_word byte digit :
  0 <= byte < eta_accept_bound_i =>
  0 <= digit =>
  W32.to_uint (W32.of_int (byte %/ (3 ^ digit))) =
    byte %/ (3 ^ digit).
proof.
move=> hbyte hdigit.
have hrange := eta_accepted_quotient_range byte digit hbyte hdigit.
rewrite W32.of_uintK /=.
by rewrite modz_small 1:/#.
qed.

lemma eta_centered_digit_to_sint byte digit :
  W32.to_sint
    (centered_trit (W32.of_int (byte %/ (3 ^ digit)))) =
  eta_centered_digit byte digit.
proof. by rewrite centered_trit_to_sint /eta_centered_digit. qed.

lemma eta_centered_digit_range byte digit :
  -1 <= eta_centered_digit byte digit <= 1.
proof.
rewrite /eta_centered_digit.
exact (centered_trit_value_range
         (W32.of_int (byte %/ (3 ^ digit)))).
qed.

lemma eta_decode_bytes_nil : eta_decode_bytes [] = [].
proof. by rewrite /eta_decode_bytes /= flatten_nil. qed.

lemma eta_decode_bytes_cons byte bytes :
  eta_decode_bytes (byte :: bytes) =
    eta_decode_byte byte ++ eta_decode_bytes bytes.
proof. by rewrite /eta_decode_bytes /= flatten_cons. qed.

lemma eta_decode_bytes_cat xs ys :
  eta_decode_bytes (xs ++ ys) =
    eta_decode_bytes xs ++ eta_decode_bytes ys.
proof. by rewrite /eta_decode_bytes map_cat flatten_cat. qed.

lemma eta_decode_bytes_rcons bytes byte :
  eta_decode_bytes (rcons bytes byte) =
    eta_decode_bytes bytes ++ eta_decode_byte byte.
proof.
have hsingle : eta_decode_bytes [byte] = eta_decode_byte byte.
+ by rewrite eta_decode_bytes_cons eta_decode_bytes_nil cats0.
by rewrite -cats1 eta_decode_bytes_cat hsingle.
qed.

lemma eta_decode_bytes_singleton byte :
  eta_decode_bytes [byte] = eta_decode_byte byte.
proof. by rewrite eta_decode_bytes_cons eta_decode_bytes_nil cats0. qed.

lemma eta_take_after_take_cat ['a] (xs ys : 'a list) :
  take eta_poly_words_i (take eta_poly_words_i xs ++ ys) =
  take eta_poly_words_i (xs ++ ys).
proof.
case (eta_poly_words_i <= size xs) => hfull.
+ have hsize : size (take eta_poly_words_i xs) = eta_poly_words_i.
  + apply size_takel.
    rewrite /eta_poly_words_i.
    smt().
  rewrite (take_size_cat eta_poly_words_i
             (take eta_poly_words_i xs) ys hsize).
  by rewrite take_catl 1:hfull.
have hshort : size xs <= eta_poly_words_i by smt().
by rewrite (take_oversize eta_poly_words_i xs hshort).
qed.

lemma eta_fill_nil values :
  size values <= eta_poly_words_i => eta_fill values [] = values.
proof.
move=> hsize.
by rewrite /eta_fill eta_decode_bytes_nil cats0 take_oversize.
qed.

lemma eta_fill_extension values bytes :
  size values <= eta_poly_words_i =>
  eta_fill values bytes =
    values ++
    take (eta_poly_words_i - size values) (eta_decode_bytes bytes).
proof.
move=> hsize.
rewrite /eta_fill.
by apply take_catr.
qed.

lemma eta_fill_cat values xs ys :
  eta_fill (eta_fill values xs) ys = eta_fill values (xs ++ ys).
proof.
rewrite /eta_fill eta_decode_bytes_cat catA.
exact (eta_take_after_take_cat
         (values ++ eta_decode_bytes xs) (eta_decode_bytes ys)).
qed.

lemma eta_fill_rcons values bytes byte :
  eta_fill values (rcons bytes byte) =
  eta_fill (eta_fill values bytes) [byte].
proof.
rewrite -cats1.
by rewrite -eta_fill_cat.
qed.

lemma eta_fill_size_le values bytes :
  size (eta_fill values bytes) <= eta_poly_words_i.
proof.
rewrite /eta_fill.
apply size_take_le.
by rewrite /eta_poly_words_i.
qed.

lemma eta_fill_uncapped values bytes :
  size (values ++ eta_decode_bytes bytes) <= eta_poly_words_i =>
  eta_fill values bytes = values ++ eta_decode_bytes bytes.
proof.
move=> hsize.
by rewrite /eta_fill take_oversize.
qed.

lemma eta_fill_full_extension values bytes :
  eta_poly_words_i <= size (values ++ eta_decode_bytes bytes) =>
  size (eta_fill values bytes) = eta_poly_words_i.
proof.
move=> hsize.
rewrite /eta_fill.
apply size_takel.
rewrite /eta_poly_words_i.
by smt().
qed.

lemma eta_fill_not_full values bytes :
  size (eta_fill values bytes) < eta_poly_words_i =>
  eta_fill values bytes = values ++ eta_decode_bytes bytes.
proof.
move=> hnotfull.
have hraw :
  size (values ++ eta_decode_bytes bytes) <= eta_poly_words_i.
+ case (eta_poly_words_i <= size (values ++ eta_decode_bytes bytes)) => hfull.
  + have := eta_fill_full_extension values bytes hfull.
    smt().
  by smt().
exact (eta_fill_uncapped values bytes hraw).
qed.

lemma eta_fill_full values bytes :
  size values = eta_poly_words_i => eta_fill values bytes = values.
proof.
move=> hsize.
rewrite /eta_fill.
exact (take_size_cat eta_poly_words_i
         values (eta_decode_bytes bytes) hsize).
qed.

lemma eta_fill_shake256_succ state blocks :
  0 <= blocks =>
  eta_fill []
      (KeygenShakeStreamSpec.shake256_squeeze_bytes state (blocks + 1)) =
    eta_fill
      (eta_fill []
        (KeygenShakeStreamSpec.shake256_squeeze_bytes state blocks))
      (KeygenShakeStreamSpec.shake256_squeeze_block state blocks).
proof.
move=> hblocks.
rewrite KeygenShakeStreamSpec.shake256_squeeze_bytes_succ 1://.
by rewrite eta_fill_cat.
qed.

lemma eta_fill_shake256_full_succ state blocks :
  0 <= blocks =>
  size (eta_fill []
    (KeygenShakeStreamSpec.shake256_squeeze_bytes state blocks)) =
      eta_poly_words_i =>
  eta_fill []
      (KeygenShakeStreamSpec.shake256_squeeze_bytes state (blocks + 1)) =
    eta_fill []
      (KeygenShakeStreamSpec.shake256_squeeze_bytes state blocks).
proof.
move=> hblocks hfull.
rewrite eta_fill_shake256_succ 1://.
by rewrite eta_fill_full.
qed.

lemma eta_fill_shake256_full_mono state blocks extra :
  0 <= blocks =>
  0 <= extra =>
  size (eta_fill []
    (KeygenShakeStreamSpec.shake256_squeeze_bytes state blocks)) =
      eta_poly_words_i =>
  size (eta_fill []
    (KeygenShakeStreamSpec.shake256_squeeze_bytes state (blocks + extra))) =
      eta_poly_words_i.
proof.
move=> hblocks.
move: extra.
apply intind.
+ trivial.
move=> extra hextra ih hfull.
have hprev := ih hfull.
have heq := eta_fill_shake256_full_succ
  state (blocks + extra) _ hprev.
+ smt().
have hsum : blocks + (extra + 1) = blocks + extra + 1 by ring.
by rewrite hsum heq.
qed.

lemma eta_sufficient_prefix_limit seed seedoff nonce limit :
  eta_sufficient_prefix seed seedoff nonce limit => 1 <= limit.
proof. by rewrite /eta_sufficient_prefix; smt(). qed.

lemma eta_sufficient_prefix_full seed seedoff nonce limit :
  eta_sufficient_prefix seed seedoff nonce limit =>
  size (eta_fill []
    (KeygenShakeStreamSpec.shake256_squeeze_bytes
      (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
        seed seedoff nonce) limit)) = eta_poly_words_i.
proof. by rewrite /eta_sufficient_prefix; smt(). qed.

lemma eta_sufficient_prefix_mono seed seedoff nonce limit blocks :
  eta_sufficient_prefix seed seedoff nonce limit =>
  limit <= blocks =>
  eta_sufficient_prefix seed seedoff nonce blocks.
proof.
move=> hcert hle.
have hlimit := eta_sufficient_prefix_limit
  seed seedoff nonce limit hcert.
have hfull := eta_sufficient_prefix_full
  seed seedoff nonce limit hcert.
have hmono := eta_fill_shake256_full_mono
  (KeygenShakeStreamSpec.shake256_seed_nonce_padded_state
    seed seedoff nonce)
  limit (blocks - limit) _ _ hfull.
+ smt().
+ smt().
rewrite (_ : limit + (blocks - limit) = blocks) 1:/# in hmono.
rewrite /eta_sufficient_prefix.
by split; [smt() | exact hmono].
qed.

lemma eta_progress_prefix_sufficient seed seedoff nonce limit :
  eta_progress_prefix seed seedoff nonce limit =>
  eta_sufficient_prefix seed seedoff nonce limit.
proof. by rewrite /eta_progress_prefix; smt(). qed.

lemma eta_progress_prefix_limit seed seedoff nonce limit :
  eta_progress_prefix seed seedoff nonce limit => 1 <= limit.
proof.
move=> hcert.
apply (eta_sufficient_prefix_limit seed seedoff nonce limit).
exact (eta_progress_prefix_sufficient seed seedoff nonce limit hcert).
qed.

lemma eta_progress_prefix_step seed seedoff nonce limit blocks :
  eta_progress_prefix seed seedoff nonce limit =>
  1 <= blocks < limit =>
  eta_prefix_count seed seedoff nonce blocks < eta_poly_words_i =>
  eta_prefix_count seed seedoff nonce blocks <
    eta_prefix_count seed seedoff nonce (blocks + 1).
proof. by rewrite /eta_progress_prefix; smt(). qed.

lemma eta_progress_prefix_endpoint seed seedoff nonce limit :
  eta_progress_prefix seed seedoff nonce limit =>
  eta_prefix_count seed seedoff nonce limit = eta_poly_words_i.
proof.
rewrite /eta_progress_prefix /eta_sufficient_prefix /eta_prefix_count.
by smt().
qed.

lemma eta_progress_prefix_before_limit
    seed seedoff nonce limit blocks :
  eta_progress_prefix seed seedoff nonce limit =>
  1 <= blocks =>
  eta_prefix_count seed seedoff nonce blocks < eta_poly_words_i =>
  blocks < limit.
proof.
move=> hcert hblocks hincomplete.
case (blocks < limit) => // hnotlt.
have hsufficient := eta_progress_prefix_sufficient
  seed seedoff nonce limit hcert.
have hsufficient_blocks := eta_sufficient_prefix_mono
  seed seedoff nonce limit blocks hsufficient _.
+ smt().
have hfull := eta_sufficient_prefix_full
  seed seedoff nonce blocks hsufficient_blocks.
rewrite /eta_prefix_count in hincomplete.
by smt().
qed.

lemma word_frame8192_refl a base start :
  word_frame8192 a a base start start.
proof. by rewrite /word_frame8192. qed.

lemma poly_frame8192_refl a base : poly_frame8192 a a base.
proof. by rewrite /poly_frame8192. qed.

lemma poly_frame8192_trans a b c base :
  poly_frame8192 a b base =>
  poly_frame8192 b c base =>
  poly_frame8192 a c base.
proof.
rewrite /poly_frame8192.
move=> hab hbc i hi hout.
by rewrite (hbc i hi hout) (hab i hi hout).
qed.

lemma centered_interval8192_empty a base start :
  centered_interval8192 a base start start.
proof. by rewrite /centered_interval8192; smt(). qed.

lemma base_counter_no_wrap8192 (base ctr : W64.t) :
  W64.to_uint base + eta_poly_words_i <= BArray8192.size %/ 4 =>
  W64.to_uint ctr < eta_poly_words_i =>
  W64.to_uint (base + ctr) = W64.to_uint base + W64.to_uint ctr.
proof.
rewrite /eta_poly_words_i.
move=> hbase hctr.
by rewrite W64.to_uintD_small 1:/#.
qed.

lemma word_frame8192_succ before current base start count w :
  0 <= base =>
  base + eta_poly_words_i <= BArray8192.size %/ 4 =>
  0 <= start <= count < eta_poly_words_i =>
  word_frame8192 before current base start count =>
  word_frame8192 before
    (BArray8192.set32 current (base + count) w)
    base start (count + 1).
proof.
rewrite /word_frame8192 /eta_poly_words_i.
move=> hbase hcap hcount hframe i hi hout.
rewrite BArray8192.get_set32E 1:/# 1:/#.
have hne : base + count <> i by smt().
rewrite ifF 1:/#.
by apply hframe; smt().
qed.

lemma poly_frame8192_set32_word before current base_i
                                  (base ctr : W64.t) w :
  poly_frame8192 before current base_i =>
  W64.to_uint base = base_i =>
  base_i + eta_poly_words_i <= BArray8192.size %/ 4 =>
  W64.to_uint ctr < eta_poly_words_i =>
  poly_frame8192 before
    (BArray8192.set32 current (W64.to_uint (base + ctr)) w)
    base_i.
proof.
move=> hframe hbase hcap hctr.
have hcapw :
  W64.to_uint base + eta_poly_words_i <= BArray8192.size %/ 4
  by rewrite hbase.
rewrite (base_counter_no_wrap8192 base ctr hcapw hctr) hbase.
rewrite /poly_frame8192 /eta_poly_words_i.
move=> i hi hout.
rewrite BArray8192.get_set32E 1:/# 1:/#.
have hne : base_i + W64.to_uint ctr <> i by smt(W64.to_uint_cmp).
rewrite ifF 1:/#.
rewrite /poly_frame8192 in hframe.
by apply hframe.
qed.

lemma centered_interval8192_succ a base start count w :
  0 <= base =>
  base + eta_poly_words_i <= BArray8192.size %/ 4 =>
  0 <= start <= count < eta_poly_words_i =>
  centered_interval8192 a base start count =>
  -1 <= W32.to_sint w <= 1 =>
  centered_interval8192
    (BArray8192.set32 a (base + count) w)
    base start (count + 1).
proof.
rewrite /centered_interval8192 /eta_poly_words_i.
move=> hbase hcap hcount hrange hw i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (base + count = base + i) => heq.
+ exact hw.
by apply hrange; smt().
qed.

lemma centered_interval8192_set32_word current base_i
                                        (base ctr : W64.t) w :
  W64.to_uint base = base_i =>
  base_i + eta_poly_words_i <= BArray8192.size %/ 4 =>
  W64.to_uint ctr < eta_poly_words_i =>
  centered_interval8192 current base_i 0 (W64.to_uint ctr) =>
  -1 <= W32.to_sint w <= 1 =>
  centered_interval8192
    (BArray8192.set32 current (W64.to_uint (base + ctr)) w)
    base_i 0 (W64.to_uint ctr + 1).
proof.
move=> hbase hcap hctr hrange hw.
have hcapw :
  W64.to_uint base + eta_poly_words_i <= BArray8192.size %/ 4
  by rewrite hbase.
rewrite (base_counter_no_wrap8192 base ctr hcapw hctr) hbase.
apply (centered_interval8192_succ current base_i 0
         (W64.to_uint ctr) w).
+ smt(W64.to_uint_cmp).
+ exact hcap.
+ smt(W64.to_uint_cmp).
+ exact hrange.
exact hw.
qed.

lemma eta_decoded_prefix8192_zero a base :
  eta_decoded_prefix8192 a base [].
proof. by rewrite /eta_decoded_prefix8192; smt(). qed.

lemma eta_decoded_prefix8192_rcons a base values w value :
  0 <= base =>
  base + eta_poly_words_i <= BArray8192.size %/ 4 =>
  0 <= size values < eta_poly_words_i =>
  eta_decoded_prefix8192 a base values =>
  W32.to_sint w = value =>
  eta_decoded_prefix8192
    (BArray8192.set32 a (base + size values) w)
    base (rcons values value).
proof.
rewrite /eta_decoded_prefix8192 /eta_poly_words_i.
move=> hbase hcap hsize hprefix hword i hi.
rewrite nth_rcons.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (i < size values) => hbefore.
+ have -> : !(base + size values = base + i) by smt().
  by rewrite (hprefix i) 1:/#.
have -> : base + size values = base + i by smt().
rewrite hword.
smt().
qed.

lemma eta_decoded_prefix8192_set32_word
    a base_i (base ctr : W64.t) values w value :
  W64.to_uint base = base_i =>
  base_i + eta_poly_words_i <= BArray8192.size %/ 4 =>
  W64.to_uint ctr = size values =>
  W64.to_uint ctr < eta_poly_words_i =>
  eta_decoded_prefix8192 a base_i values =>
  W32.to_sint w = value =>
  eta_decoded_prefix8192
    (BArray8192.set32 a (W64.to_uint (base + ctr)) w)
    base_i (rcons values value).
proof.
move=> hbase hcap hctr hctrlt hprefix hword.
have hcapw :
  W64.to_uint base + eta_poly_words_i <= BArray8192.size %/ 4
  by rewrite hbase.
rewrite (base_counter_no_wrap8192 base ctr hcapw hctrlt) hbase hctr.
apply eta_decoded_prefix8192_rcons.
+ by rewrite -hbase; smt(W64.to_uint_cmp).
+ exact hcap.
+ rewrite -hctr; smt(W64.to_uint_cmp).
+ exact hprefix.
exact hword.
qed.

end KeygenEtaSamplerSpec.
