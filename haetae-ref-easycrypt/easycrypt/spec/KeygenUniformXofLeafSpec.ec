require import AllCore IntDiv List StdOrder.

from Jasmin require import JModel_x86.

require import BArray8192 BArray32768 KeygenShakeStreamSpec.

theory KeygenUniformXofLeafSpec.

op uniform_q_i : int = 64513.
op uniform_poly_words_i : int = 256.
op uniform_first_bytes_i : int = 672.
op uniform_first_pairs_i : int = 336.
op uniform_block_bytes_i : int = 168.
op uniform_block_pairs_i : int = 84.

op uniform_le16 (bytes : int list) (pair : int) : int =
  nth 0 bytes (2 * pair) + 256 * nth 0 bytes (2 * pair + 1).

op uniform_candidates (bytes : int list) (pairs : int) : int list =
  mkseq (uniform_le16 bytes) pairs.

op uniform_accepted (bytes : int list) (pairs : int) : int list =
  filter (fun x => x < uniform_q_i) (uniform_candidates bytes pairs).

op uniform_sufficient_prefix
    (seed : BArray128.t) (seedoff nonce : W64.t) (limit : int) : bool =
  4 <= limit /\
  uniform_poly_words_i <=
    size (uniform_accepted
      (KeygenShakeStreamSpec.shake128_squeeze_bytes
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed seedoff nonce) limit)
      (limit * uniform_block_pairs_i)).

op uniform_prefix_count
    (seed : BArray128.t) (seedoff nonce : W64.t) (blocks : int) : int =
  size (uniform_accepted
    (KeygenShakeStreamSpec.shake128_squeeze_bytes
      (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
        seed seedoff nonce) blocks)
    (blocks * uniform_block_pairs_i)).

(* This strengthening is a proof-oriented deterministic certificate: before
   the certified endpoint, every still-incomplete full block prefix makes
   strict progress.  It does not assert any probabilistic Keccak property. *)
op uniform_progress_prefix
    (seed : BArray128.t) (seedoff nonce : W64.t) (limit : int) : bool =
  uniform_sufficient_prefix seed seedoff nonce limit /\
  forall blocks,
    4 <= blocks < limit =>
    uniform_prefix_count seed seedoff nonce blocks < uniform_poly_words_i =>
    uniform_prefix_count seed seedoff nonce blocks <
      uniform_prefix_count seed seedoff nonce (blocks + 1).

op decoded_prefix8192
    (a : BArray8192.t) (base : int) (values : int list) : bool =
  forall i,
    0 <= i < size values =>
    W32.to_uint (BArray8192.get32 a (base + i)) = nth 0 values i.

op decoded_prefix32768
    (a : BArray32768.t) (base : int) (values : int list) : bool =
  forall i,
    0 <= i < size values =>
    W32.to_uint (BArray32768.get32 a (base + i)) = nth 0 values i.

op in_poly_bytes (base byte_index : int) : bool =
  4 * base <= byte_index < 4 * (base + uniform_poly_words_i).

op frame8192 (before after : BArray8192.t) (base : int) : bool =
  forall byte_index,
    0 <= byte_index < BArray8192.size =>
    ! in_poly_bytes base byte_index =>
    BArray8192.get8 after byte_index =
    BArray8192.get8 before byte_index.

op frame32768 (before after : BArray32768.t) (base : int) : bool =
  forall byte_index,
    0 <= byte_index < BArray32768.size =>
    ! in_poly_bytes base byte_index =>
    BArray32768.get8 after byte_index =
    BArray32768.get8 before byte_index.

op bounded_prefix8192 (a : BArray8192.t) (base count : int) : bool =
  forall i,
    0 <= i < count =>
    W32.to_uint (BArray8192.get32 a (base + i)) < uniform_q_i.

op bounded_prefix32768 (a : BArray32768.t) (base count : int) : bool =
  forall i,
    0 <= i < count =>
    W32.to_uint (BArray32768.get32 a (base + i)) < uniform_q_i.

lemma frame8192_refl a base : frame8192 a a base.
proof. by rewrite /frame8192. qed.

lemma frame32768_refl a base : frame32768 a a base.
proof. by rewrite /frame32768. qed.

lemma frame8192_trans a b c base :
  frame8192 a b base => frame8192 b c base => frame8192 a c base.
proof.
rewrite /frame8192.
move=> hab hbc i hi hout.
by rewrite (hbc i hi hout) (hab i hi hout).
qed.

lemma frame32768_trans a b c base :
  frame32768 a b base => frame32768 b c base => frame32768 a c base.
proof.
rewrite /frame32768.
move=> hab hbc i hi hout.
by rewrite (hbc i hi hout) (hab i hi hout).
qed.

lemma frame8192_set32 before current base slot w :
  frame8192 before current base =>
  0 <= slot < uniform_poly_words_i =>
  frame8192 before (BArray8192.set32 current (base + slot) w) base.
proof.
rewrite /frame8192 /in_poly_bytes /uniform_poly_words_i.
move=> hframe hslot i hi hout.
rewrite BArray8192.get8_set32dE.
have -> /= :
  !(4 * (base + slot) <= i < 4 * (base + slot) + 4 /\
    0 <= i && i < BArray8192.size) by smt().
by apply hframe.
qed.

lemma frame32768_set32 before current base slot w :
  frame32768 before current base =>
  0 <= slot < uniform_poly_words_i =>
  frame32768 before (BArray32768.set32 current (base + slot) w) base.
proof.
rewrite /frame32768 /in_poly_bytes /uniform_poly_words_i.
move=> hframe hslot i hi hout.
rewrite BArray32768.get8_set32dE.
have -> /= :
  !(4 * (base + slot) <= i < 4 * (base + slot) + 4 /\
    0 <= i && i < BArray32768.size) by smt().
by apply hframe.
qed.

lemma bounded_prefix8192_zero a base : bounded_prefix8192 a base 0.
proof. by rewrite /bounded_prefix8192; smt(). qed.

lemma bounded_prefix32768_zero a base : bounded_prefix32768 a base 0.
proof. by rewrite /bounded_prefix32768; smt(). qed.

lemma base_counter_no_wrap8192 (base ctr : W64.t) :
  W64.to_uint base + uniform_poly_words_i <= BArray8192.size %/ 4 =>
  W64.to_uint ctr < uniform_poly_words_i =>
  W64.to_uint (base + ctr) = W64.to_uint base + W64.to_uint ctr.
proof.
rewrite /uniform_poly_words_i.
move=> hbase hctr.
by rewrite W64.to_uintD_small 1:/#.
qed.

lemma base_counter_no_wrap32768 (base ctr : W64.t) :
  W64.to_uint base + uniform_poly_words_i <= BArray32768.size %/ 4 =>
  W64.to_uint ctr < uniform_poly_words_i =>
  W64.to_uint (base + ctr) = W64.to_uint base + W64.to_uint ctr.
proof.
rewrite /uniform_poly_words_i.
move=> hbase hctr.
by rewrite W64.to_uintD_small 1:/#.
qed.

lemma frame8192_set32_word before current base_i (base ctr : W64.t) w :
  frame8192 before current base_i =>
  W64.to_uint base = base_i =>
  base_i + uniform_poly_words_i <= BArray8192.size %/ 4 =>
  W64.to_uint ctr < uniform_poly_words_i =>
  frame8192 before
    (BArray8192.set32 current (W64.to_uint (base + ctr)) w)
    base_i.
proof.
move=> hframe hbase hcap hctr.
have hcapw :
  W64.to_uint base + uniform_poly_words_i <= BArray8192.size %/ 4
  by rewrite hbase.
rewrite (base_counter_no_wrap8192 base ctr hcapw hctr) hbase.
apply frame8192_set32.
+ exact hframe.
by rewrite /uniform_poly_words_i; smt(W64.to_uint_cmp).
qed.

lemma frame32768_set32_word before current base_i (base ctr : W64.t) w :
  frame32768 before current base_i =>
  W64.to_uint base = base_i =>
  base_i + uniform_poly_words_i <= BArray32768.size %/ 4 =>
  W64.to_uint ctr < uniform_poly_words_i =>
  frame32768 before
    (BArray32768.set32 current (W64.to_uint (base + ctr)) w)
    base_i.
proof.
move=> hframe hbase hcap hctr.
have hcapw :
  W64.to_uint base + uniform_poly_words_i <= BArray32768.size %/ 4
  by rewrite hbase.
rewrite (base_counter_no_wrap32768 base ctr hcapw hctr) hbase.
apply frame32768_set32.
+ exact hframe.
by rewrite /uniform_poly_words_i; smt(W64.to_uint_cmp).
qed.

lemma bounded_prefix8192_succ a base count w :
  0 <= base =>
  base + uniform_poly_words_i <= BArray8192.size %/ 4 =>
  0 <= count < uniform_poly_words_i =>
  bounded_prefix8192 a base count =>
  W32.to_uint w < uniform_q_i =>
  bounded_prefix8192 (BArray8192.set32 a (base + count) w)
                     base (count + 1).
proof.
rewrite /bounded_prefix8192 /uniform_poly_words_i.
move=> hbase hcap hcount hprefix hw i hi.
rewrite BArray8192.get_set32E 1:/# 1:/#.
case (base + count = base + i) => heq.
+ exact hw.
by apply hprefix; smt().
qed.

lemma bounded_prefix32768_succ a base count w :
  0 <= base =>
  base + uniform_poly_words_i <= BArray32768.size %/ 4 =>
  0 <= count < uniform_poly_words_i =>
  bounded_prefix32768 a base count =>
  W32.to_uint w < uniform_q_i =>
  bounded_prefix32768 (BArray32768.set32 a (base + count) w)
                      base (count + 1).
proof.
rewrite /bounded_prefix32768 /uniform_poly_words_i.
move=> hbase hcap hcount hprefix hw i hi.
rewrite BArray32768.get_set32E 1:/# 1:/#.
case (base + count = base + i) => heq.
+ exact hw.
by apply hprefix; smt().
qed.

lemma bounded_prefix8192_set32_word a base_i (base ctr : W64.t) w :
  W64.to_uint base = base_i =>
  base_i + uniform_poly_words_i <= BArray8192.size %/ 4 =>
  W64.to_uint ctr < uniform_poly_words_i =>
  bounded_prefix8192 a base_i (W64.to_uint ctr) =>
  W32.to_uint w < uniform_q_i =>
  bounded_prefix8192
    (BArray8192.set32 a (W64.to_uint (base + ctr)) w)
    base_i (W64.to_uint (ctr + W64.one)).
proof.
move=> hbase hcap hctr hprefix hw.
have hcapw :
  W64.to_uint base + uniform_poly_words_i <= BArray8192.size %/ 4
  by rewrite hbase.
rewrite (base_counter_no_wrap8192 base ctr hcapw hctr).
rewrite hbase.
rewrite W64.to_uintD_small 1:/# W64.to_uint1.
apply bounded_prefix8192_succ.
+ by rewrite -hbase; smt(W64.to_uint_cmp).
+ exact hcap.
+ by smt(W64.to_uint_cmp).
+ exact hprefix.
exact hw.
qed.

lemma bounded_prefix32768_set32_word a base_i (base ctr : W64.t) w :
  W64.to_uint base = base_i =>
  base_i + uniform_poly_words_i <= BArray32768.size %/ 4 =>
  W64.to_uint ctr < uniform_poly_words_i =>
  bounded_prefix32768 a base_i (W64.to_uint ctr) =>
  W32.to_uint w < uniform_q_i =>
  bounded_prefix32768
    (BArray32768.set32 a (W64.to_uint (base + ctr)) w)
    base_i (W64.to_uint (ctr + W64.one)).
proof.
move=> hbase hcap hctr hprefix hw.
have hcapw :
  W64.to_uint base + uniform_poly_words_i <= BArray32768.size %/ 4
  by rewrite hbase.
rewrite (base_counter_no_wrap32768 base ctr hcapw hctr).
rewrite hbase.
rewrite W64.to_uintD_small 1:/# W64.to_uint1.
apply bounded_prefix32768_succ.
+ by rewrite -hbase; smt(W64.to_uint_cmp).
+ exact hcap.
+ by smt(W64.to_uint_cmp).
+ exact hprefix.
exact hw.
qed.

lemma uniform_candidates_snoc bytes pairs :
  0 <= pairs =>
  uniform_candidates bytes (pairs + 1) =
    rcons (uniform_candidates bytes pairs) (uniform_le16 bytes pairs).
proof.
by move=> hpairs; rewrite /uniform_candidates mkseqS.
qed.

lemma uniform_accepted_snoc bytes pairs :
  0 <= pairs =>
  uniform_accepted bytes (pairs + 1) =
    if uniform_le16 bytes pairs < uniform_q_i then
      rcons (uniform_accepted bytes pairs) (uniform_le16 bytes pairs)
    else uniform_accepted bytes pairs.
proof.
move=> hpairs.
by rewrite /uniform_accepted uniform_candidates_snoc 1:// filter_rcons.
qed.

lemma uniform_accepted_size_le bytes pairs :
  0 <= pairs => size (uniform_accepted bytes pairs) <= pairs.
proof.
move=> hpairs.
rewrite /uniform_accepted size_filter.
have hcount := count_size (fun x => x < uniform_q_i)
  (uniform_candidates bytes pairs).
rewrite /uniform_candidates size_mkseq in hcount.
by smt().
qed.

lemma uniform_accepted_zero bytes : uniform_accepted bytes 0 = [].
proof.
by rewrite /uniform_accepted /uniform_candidates mkseq0.
qed.

lemma uniform_candidates_cat_even xs ys lp rp :
  0 <= lp =>
  0 <= rp =>
  size xs = 2 * lp =>
  uniform_candidates (xs ++ ys) (lp + rp) =
    uniform_candidates xs lp ++ uniform_candidates ys rp.
proof.
move=> hlp hrp hsize.
rewrite /uniform_candidates mkseq_add 1:// 1://.
congr.
+ apply eq_in_mkseq => i hi.
  rewrite /uniform_le16 !nth_cat hsize.
  have -> : 2 * i < 2 * lp by smt().
  have -> : 2 * i + 1 < 2 * lp by smt().
  trivial.
apply eq_in_mkseq => i hi.
rewrite /= /uniform_le16 !nth_cat hsize.
have -> : !(2 * (lp + i) < 2 * lp) by smt().
have -> : !(2 * (lp + i) + 1 < 2 * lp) by smt().
congr; smt().
qed.

lemma uniform_accepted_cat_even xs ys lp rp :
  0 <= lp =>
  0 <= rp =>
  size xs = 2 * lp =>
  uniform_accepted (xs ++ ys) (lp + rp) =
    uniform_accepted xs lp ++ uniform_accepted ys rp.
proof.
move=> hlp hrp hsize.
rewrite /uniform_accepted
        uniform_candidates_cat_even 1:// 1:// 1:// filter_cat.
trivial.
qed.

lemma uniform_accepted_shake128_full_succ state blocks :
  0 <= blocks =>
  uniform_accepted
      (KeygenShakeStreamSpec.shake128_squeeze_bytes state (blocks + 1))
      ((blocks + 1) * uniform_block_pairs_i) =
    uniform_accepted
      (KeygenShakeStreamSpec.shake128_squeeze_bytes state blocks)
      (blocks * uniform_block_pairs_i) ++
    uniform_accepted
      (KeygenShakeStreamSpec.shake128_squeeze_block state blocks)
      uniform_block_pairs_i.
proof.
move=> hblocks.
rewrite KeygenShakeStreamSpec.shake128_squeeze_bytes_succ 1://.
have -> : (blocks + 1) * uniform_block_pairs_i =
    blocks * uniform_block_pairs_i + uniform_block_pairs_i by ring.
rewrite (uniform_accepted_cat_even
  (KeygenShakeStreamSpec.shake128_squeeze_bytes state blocks)
  (KeygenShakeStreamSpec.shake128_squeeze_block state blocks)
  (blocks * uniform_block_pairs_i) uniform_block_pairs_i).
+ rewrite /uniform_block_pairs_i; smt().
+ by rewrite /uniform_block_pairs_i.
+ rewrite /KeygenShakeStreamSpec.shake128_squeeze_bytes
           KeygenShakeStreamSpec.squeeze_bytes_iter_size 1:/# 1://
           /uniform_block_pairs_i.
  ring.
congr; ring.
qed.

lemma uniform_accepted_shake128_size_succ state blocks :
  0 <= blocks =>
  size (uniform_accepted
    (KeygenShakeStreamSpec.shake128_squeeze_bytes state blocks)
    (blocks * uniform_block_pairs_i)) <=
  size (uniform_accepted
    (KeygenShakeStreamSpec.shake128_squeeze_bytes state (blocks + 1))
    ((blocks + 1) * uniform_block_pairs_i)).
proof.
move=> hblocks.
rewrite uniform_accepted_shake128_full_succ 1:// size_cat.
by smt(size_ge0).
qed.

lemma uniform_accepted_shake128_size_mono state blocks extra :
  0 <= blocks =>
  0 <= extra =>
  size (uniform_accepted
    (KeygenShakeStreamSpec.shake128_squeeze_bytes state blocks)
    (blocks * uniform_block_pairs_i)) <=
  size (uniform_accepted
    (KeygenShakeStreamSpec.shake128_squeeze_bytes state (blocks + extra))
    ((blocks + extra) * uniform_block_pairs_i)).
proof.
move=> hblocks.
move: extra.
apply intind.
+ trivial.
move=> extra hextra ih.
have hstep := uniform_accepted_shake128_size_succ
  state (blocks + extra) _.
+ smt().
by smt().
qed.

lemma uniform_sufficient_prefix_limit seed seedoff nonce limit :
  uniform_sufficient_prefix seed seedoff nonce limit => 4 <= limit.
proof. by rewrite /uniform_sufficient_prefix; smt(). qed.

lemma uniform_sufficient_prefix_accepts seed seedoff nonce limit :
  uniform_sufficient_prefix seed seedoff nonce limit =>
  uniform_poly_words_i <=
    size (uniform_accepted
      (KeygenShakeStreamSpec.shake128_squeeze_bytes
        (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
          seed seedoff nonce) limit)
      (limit * uniform_block_pairs_i)).
proof. by rewrite /uniform_sufficient_prefix; smt(). qed.

lemma uniform_sufficient_prefix_mono seed seedoff nonce limit blocks :
  uniform_sufficient_prefix seed seedoff nonce limit =>
  limit <= blocks =>
  uniform_sufficient_prefix seed seedoff nonce blocks.
proof.
move=> hcert hle.
have hlimit := uniform_sufficient_prefix_limit
  seed seedoff nonce limit hcert.
have haccepts := uniform_sufficient_prefix_accepts
  seed seedoff nonce limit hcert.
have hmono := uniform_accepted_shake128_size_mono
  (KeygenShakeStreamSpec.shake128_seed_nonce_padded_state
    seed seedoff nonce)
  limit (blocks - limit) _ _.
+ smt().
+ smt().
rewrite (_ : limit + (blocks - limit) = blocks) 1:/# in hmono.
rewrite /uniform_sufficient_prefix.
split; first smt().
by smt().
qed.

lemma uniform_progress_prefix_sufficient seed seedoff nonce limit :
  uniform_progress_prefix seed seedoff nonce limit =>
  uniform_sufficient_prefix seed seedoff nonce limit.
proof. by rewrite /uniform_progress_prefix; smt(). qed.

lemma uniform_progress_prefix_limit seed seedoff nonce limit :
  uniform_progress_prefix seed seedoff nonce limit => 4 <= limit.
proof.
move=> hcert.
apply (uniform_sufficient_prefix_limit seed seedoff nonce limit).
exact (uniform_progress_prefix_sufficient seed seedoff nonce limit hcert).
qed.

lemma uniform_progress_prefix_step seed seedoff nonce limit blocks :
  uniform_progress_prefix seed seedoff nonce limit =>
  4 <= blocks < limit =>
  uniform_prefix_count seed seedoff nonce blocks < uniform_poly_words_i =>
  uniform_prefix_count seed seedoff nonce blocks <
    uniform_prefix_count seed seedoff nonce (blocks + 1).
proof. by rewrite /uniform_progress_prefix; smt(). qed.

lemma uniform_progress_prefix_endpoint seed seedoff nonce limit :
  uniform_progress_prefix seed seedoff nonce limit =>
  uniform_poly_words_i <= uniform_prefix_count seed seedoff nonce limit.
proof.
rewrite /uniform_progress_prefix /uniform_sufficient_prefix
        /uniform_prefix_count.
by smt().
qed.

lemma uniform_progress_prefix_before_limit
    seed seedoff nonce limit blocks :
  uniform_progress_prefix seed seedoff nonce limit =>
  4 <= blocks =>
  uniform_prefix_count seed seedoff nonce blocks < uniform_poly_words_i =>
  blocks < limit.
proof.
move=> hcert hblocks hincomplete.
case (blocks < limit) => // hnotlt.
have hsufficient := uniform_progress_prefix_sufficient
  seed seedoff nonce limit hcert.
have hsufficient_blocks := uniform_sufficient_prefix_mono
  seed seedoff nonce limit blocks hsufficient _.
+ smt().
have haccepts := uniform_sufficient_prefix_accepts
  seed seedoff nonce blocks hsufficient_blocks.
rewrite /uniform_prefix_count in hincomplete.
by smt().
qed.

lemma decoded_prefix8192_zero a base : decoded_prefix8192 a base [].
proof. by rewrite /decoded_prefix8192; smt(). qed.

lemma decoded_prefix32768_zero a base : decoded_prefix32768 a base [].
proof. by rewrite /decoded_prefix32768; smt(). qed.

lemma decoded_prefix8192_rcons a base values w value :
  0 <= base =>
  base + uniform_poly_words_i <= BArray8192.size %/ 4 =>
  0 <= size values < uniform_poly_words_i =>
  decoded_prefix8192 a base values =>
  W32.to_uint w = value =>
  decoded_prefix8192
    (BArray8192.set32 a (base + size values) w)
    base (rcons values value).
proof.
rewrite /decoded_prefix8192 /uniform_poly_words_i.
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

lemma decoded_prefix32768_rcons a base values w value :
  0 <= base =>
  base + uniform_poly_words_i <= BArray32768.size %/ 4 =>
  0 <= size values < uniform_poly_words_i =>
  decoded_prefix32768 a base values =>
  W32.to_uint w = value =>
  decoded_prefix32768
    (BArray32768.set32 a (base + size values) w)
    base (rcons values value).
proof.
rewrite /decoded_prefix32768 /uniform_poly_words_i.
move=> hbase hcap hsize hprefix hword i hi.
rewrite nth_rcons.
rewrite BArray32768.get_set32E 1:/# 1:/#.
case (i < size values) => hbefore.
+ have -> : !(base + size values = base + i) by smt().
  by rewrite (hprefix i) 1:/#.
have -> : base + size values = base + i by smt().
rewrite hword.
smt().
qed.

lemma decoded_prefix8192_set32_word
    a base_i (base ctr : W64.t) values w value :
  W64.to_uint base = base_i =>
  base_i + uniform_poly_words_i <= BArray8192.size %/ 4 =>
  W64.to_uint ctr = size values =>
  W64.to_uint ctr < uniform_poly_words_i =>
  decoded_prefix8192 a base_i values =>
  W32.to_uint w = value =>
  decoded_prefix8192
    (BArray8192.set32 a (W64.to_uint (base + ctr)) w)
    base_i (rcons values value).
proof.
move=> hbase hcap hctr hctrlt hprefix hword.
have hcapw :
  W64.to_uint base + uniform_poly_words_i <= BArray8192.size %/ 4
  by rewrite hbase.
rewrite (base_counter_no_wrap8192 base ctr hcapw hctrlt) hbase hctr.
apply decoded_prefix8192_rcons.
+ by rewrite -hbase; smt(W64.to_uint_cmp).
+ exact hcap.
+ rewrite -hctr; smt(W64.to_uint_cmp).
+ exact hprefix.
exact hword.
qed.

lemma decoded_prefix32768_set32_word
    a base_i (base ctr : W64.t) values w value :
  W64.to_uint base = base_i =>
  base_i + uniform_poly_words_i <= BArray32768.size %/ 4 =>
  W64.to_uint ctr = size values =>
  W64.to_uint ctr < uniform_poly_words_i =>
  decoded_prefix32768 a base_i values =>
  W32.to_uint w = value =>
  decoded_prefix32768
    (BArray32768.set32 a (W64.to_uint (base + ctr)) w)
    base_i (rcons values value).
proof.
move=> hbase hcap hctr hctrlt hprefix hword.
have hcapw :
  W64.to_uint base + uniform_poly_words_i <= BArray32768.size %/ 4
  by rewrite hbase.
rewrite (base_counter_no_wrap32768 base ctr hcapw hctrlt) hbase hctr.
apply decoded_prefix32768_rcons.
+ by rewrite -hbase; smt(W64.to_uint_cmp).
+ exact hcap.
+ rewrite -hctr; smt(W64.to_uint_cmp).
+ exact hprefix.
exact hword.
qed.

end KeygenUniformXofLeafSpec.
