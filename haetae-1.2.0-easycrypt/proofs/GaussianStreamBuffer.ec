require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import ApiTarget GaussianRefillCorrectness SHAKEBlockSpec.

(* The byte function is a continuous stream, independent of its current
   storage window. Offsets here are bytes, not output coefficient indices. *)
op gs_buffer_segment (stream : int -> W8.t) (buf : BArray8192.t)
    (memory_offset stream_offset length : int) : bool =
  forall j, 0 <= j < length =>
    BArray8192.get8 buf (memory_offset + j) = stream (stream_offset + j).

op gs_stream_attempts (blocks : int) : int = (136 * blocks - 32) %/ 26.
op gs_stream_tail (blocks : int) : int = (136 * blocks - 32) %% 26.

op gs_tail_matches (stream : int -> W8.t) (buf : BArray8192.t)
    (available : int) (has_prefix : bool) (blocks : int) : bool =
  0 <= available <= 6664 /\
  available + (if has_prefix then 32 else 0) <= 8192 /\
  available %% 26 = gs_stream_tail blocks /\
  gs_buffer_segment stream buf
    (available + (if has_prefix then 32 else 0) - available %% 26)
    (136 * blocks - available %% 26) (available %% 26).

op gs_signs_result (stream : int -> W8.t)
    (before after : BArray512.t) (offset : int) : bool =
  forall j, 0 <= j < 512 =>
    BArray512.get8 after j =
      if offset <= j < offset + 32 then stream (j - offset)
      else BArray512.get8 before j.

op gs_signs_prefix (stream : int -> W8.t)
    (before after : BArray512.t) (offset copied : int) : bool =
  forall j, 0 <= j < 512 =>
    BArray512.get8 after j =
      if offset <= j < offset + copied then stream (j - offset)
      else BArray512.get8 before j.

lemma gs_tail_carry_bounds stream buf available has_prefix blocks :
  gs_tail_matches stream buf available has_prefix blocks =>
  0 <= available <= 6664 /\
  available + (if has_prefix then 32 else 0) <= 8192 /\
  available %% 26 = gs_stream_tail blocks /\
  0 <= gs_stream_tail blocks < 26 /\ gs_stream_tail blocks <= available.
proof.
  move=> ht.
  have hb : 0 <= available by move: ht; rewrite /gs_tail_matches; smt().
  have hq : 0 <= available %/ 26 by rewrite divz_ge0.
  have hd := divz_eq available 26.
  have hr := modz_cmp available 26.
  move: ht; rewrite /gs_tail_matches; smt().
qed.

lemma gs_stream_position blocks :
  136 * blocks = 32 + 26 * gs_stream_attempts blocks + gs_stream_tail blocks.
proof.
  rewrite /gs_stream_attempts /gs_stream_tail.
  have := divz_eq (136 * blocks - 32) 26; smt().
qed.

lemma gs_stream_bounds blocks : 49 <= blocks =>
  0 <= gs_stream_attempts blocks /\ 0 <= gs_stream_tail blocks < 26.
proof.
  move=> hb; rewrite /gs_stream_attempts /gs_stream_tail.
  have := divz_ge0 (136 * blocks - 32) 26 _; first smt().
  have := modz_cmp (136 * blocks - 32) 26; smt().
qed.

lemma gs_stream_initial : gs_stream_attempts 49 = 255 /\ gs_stream_tail 49 = 2.
proof. by rewrite /gs_stream_attempts /gs_stream_tail. qed.

lemma gs_stream_advance blocks :
  gs_stream_attempts (blocks + 1) =
    gs_stream_attempts blocks + (136 + gs_stream_tail blocks) %/ 26 /\
  gs_stream_tail (blocks + 1) = (136 + gs_stream_tail blocks) %% 26.
proof.
  have hp := gs_stream_position blocks.
  have hn := gs_stream_position (blocks + 1).
  have hd := divz_eq (136 + gs_stream_tail blocks) 26.
  have hr := modz_cmp (136 + gs_stream_tail blocks) 26.
  have ht : 0 <= gs_stream_tail (blocks + 1) < 26 by
    rewrite /gs_stream_tail; exact (modz_cmp _ _).
  smt().
qed.

lemma gs_buffer_empty stream buf mo so : gs_buffer_segment stream buf mo so 0.
proof. rewrite /gs_buffer_segment; smt(). qed.

lemma gs_buffer_subsegment stream buf mo so length offset count :
  gs_buffer_segment stream buf mo so length =>
  0 <= offset => 0 <= count => offset + count <= length =>
  gs_buffer_segment stream buf (mo + offset) (so + offset) count.
proof.
  move=> hb ho hc hlen; rewrite /gs_buffer_segment => j hj.
  have h := hb (offset + j) _; first smt().
  have -> : mo + offset + j = mo + (offset + j) by ring.
  have -> : so + offset + j = so + (offset + j) by ring.
  exact h.
qed.

lemma gs_initial_tail stream buf :
  gs_buffer_segment stream buf 0 0 6664 =>
  gs_tail_matches stream buf 6632 true 49.
proof.
  move=> hb; rewrite /gs_tail_matches /gs_stream_tail /=.
  rewrite /gs_buffer_segment => j hj.
  have h := hb (6662 + j) _; first smt().
  by move: h; rewrite /=.
qed.

lemma gs_carry_prefix stream before after available has_prefix blocks :
  gs_tail_matches stream before available has_prefix blocks =>
  GaussianRefillCorrectness.gauss_carry_prefix before after
    (available + (if has_prefix then 32 else 0) - available %% 26) (available %% 26) =>
  gs_buffer_segment stream after 0 (136 * blocks - gs_stream_tail blocks)
    (gs_stream_tail blocks).
proof.
  move=> htail hc.
  have [hb [hcap [hr htbuf]]] : 0 <= available <= 6664 /\
    available + (if has_prefix then 32 else 0) <= 8192 /\
    available %% 26 = gs_stream_tail blocks /\
    gs_buffer_segment stream before
      (available + (if has_prefix then 32 else 0) - available %% 26)
      (136 * blocks - available %% 26) (available %% 26) by exact htail.
  rewrite /gs_buffer_segment => j hj.
  have ht := htbuf j _; first smt().
  have hm := modz_cmp available 26.
  have h := hc j _; first smt().
  smt().
qed.

lemma gs_refill_segment stream carried after blocks :
  49 <= blocks =>
  gs_buffer_segment stream carried 0 (136 * blocks - gs_stream_tail blocks)
    (gs_stream_tail blocks) =>
  (forall j, 0 <= j < 136 =>
    BArray8192.get8 after (gs_stream_tail blocks + j) = stream (136 * blocks + j)) =>
  SHAKEBlockSpec.rate_block_frame carried after (gs_stream_tail blocks) 136 =>
  gs_buffer_segment stream after 0 (136 * blocks - gs_stream_tail blocks)
    (136 + gs_stream_tail blocks).
proof.
  move=> hb hcarry hbytes hframe.
  have [_ ht] := gs_stream_bounds blocks hb.
  rewrite /gs_buffer_segment => j hj.
  case (j < gs_stream_tail blocks) => hfirst.
  + have h := hframe j _ _; first smt().
    + smt().
    have hc := hcarry j _; first smt().
    smt().
  have h := hbytes (j - gs_stream_tail blocks) _; first smt().
  smt().
qed.

lemma gs_refill_tail stream buf blocks :
  49 <= blocks =>
  gs_buffer_segment stream buf 0 (136 * blocks - gs_stream_tail blocks)
    (136 + gs_stream_tail blocks) =>
  gs_tail_matches stream buf (136 + gs_stream_tail blocks) false (blocks + 1).
proof.
  move=> hb hsegment.
  have [_ ht] := gs_stream_bounds blocks hb.
  have [_ hnext] := gs_stream_advance blocks.
  have hm := modz_cmp (136 + gs_stream_tail blocks) 26.
  rewrite /gs_tail_matches /= -hnext.
  do split; first 3 smt().
  rewrite /gs_buffer_segment => j hj.
  have h := hsegment (136 + gs_stream_tail blocks - gs_stream_tail (blocks + 1) + j) _.
  + smt().
  smt().
qed.

lemma gs_refill_buffer_ready stream before carried after available has_prefix blocks :
  49 <= blocks =>
  gs_tail_matches stream before available has_prefix blocks =>
  GaussianRefillCorrectness.gauss_carry_prefix before carried
    (available + (if has_prefix then 32 else 0) - gs_stream_tail blocks)
    (gs_stream_tail blocks) =>
  (forall j, 0 <= j < 136 =>
    BArray8192.get8 after (gs_stream_tail blocks + j) = stream (136 * blocks + j)) =>
  SHAKEBlockSpec.rate_block_frame carried after (gs_stream_tail blocks) 136 =>
  gs_buffer_segment (fun j => stream (32 + j)) after 0
    (26 * gs_stream_attempts blocks) (136 + gs_stream_tail blocks) /\
  gs_tail_matches stream after (136 + gs_stream_tail blocks) false (blocks + 1).
proof.
  move=> hb htail hcarry hbytes hframe.
  have [hav [hcap [hres hbounds]]] :=
    gs_tail_carry_bounds stream before available has_prefix blocks htail.
  have hc : GaussianRefillCorrectness.gauss_carry_prefix before carried
    (available + (if has_prefix then 32 else 0) - available %% 26) (available %% 26).
  + by rewrite hres.
  have hp := gs_stream_position blocks.
  have hcarried := gs_carry_prefix stream before carried available has_prefix blocks htail hc.
  have hsegment := gs_refill_segment stream carried after blocks hb hcarried hbytes hframe.
  split.
  + rewrite /gs_buffer_segment => j hj.
    have h := hsegment j hj; smt().
  exact (gs_refill_tail stream after blocks hb hsegment).
qed.

lemma gs_initial_block_extend stream before after blocks :
  0 <= blocks < 49 =>
  gs_buffer_segment stream before 0 0 (136 * blocks) =>
  (forall j, 0 <= j < 136 =>
    BArray8192.get8 after (136 * blocks + j) = stream (136 * blocks + j)) =>
  SHAKEBlockSpec.rate_block_frame before after (136 * blocks) 136 =>
  gs_buffer_segment stream after 0 0 (136 * (blocks + 1)).
proof.
  move=> hb hp hc hf; rewrite /gs_buffer_segment => j hj.
  case (j < 136 * blocks) => hold.
  + have h := hf j _ _; first smt().
    + smt().
    have hprev := hp j _; first smt().
    smt().
  have h := hc (j - 136 * blocks) _; first smt().
  smt().
qed.

lemma gs_signs_step stream before after offset copied :
  0 <= offset => 0 <= copied < 32 => offset + 32 <= 512 =>
  gs_signs_prefix stream before after offset copied =>
  gs_signs_prefix stream before
    (BArray512.set8 after (offset + copied) (stream copied)) offset (copied + 1).
proof.
  move=> ho hc he hp; rewrite /gs_signs_prefix => j hj.
  rewrite BArray512.get_set_if.
  have := hp j hj; smt().
qed.

module GS_Signer = ApiTarget.M(ApiTarget.Syscall).

lemma gs_copy_signs_correct stream before buf offset :
  hoare [GS_Signer.__sample_gauss_N_copy_signs_at :
    signsp = before /\ bufp = buf /\ signbytes = W64.of_int 32 /\
    W64.to_uint signoff = offset /\ 0 <= offset /\ offset + 32 <= 512 /\
    gs_buffer_segment stream buf 0 0 32
    ==>
    gs_signs_result stream before res offset].
proof.
  proc.
  while (bufp = buf /\ signbytes = W64.of_int 32 /\
    W64.to_uint signoff = offset /\ 0 <= offset /\ offset + 32 <= 512 /\
    gs_buffer_segment stream buf 0 0 32 /\
    0 <= W64.to_uint i <= 32 /\
    gs_signs_prefix stream before signsp offset (W64.to_uint i)).
  + auto => /> &hr ho he hb hi0 hi32 hp hguard.
    rewrite W64.ultE W64.of_uintK /= in hguard.
    rewrite W64.to_uintD_small 1:/#.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1.
    have hread := hb (W64.to_uint i{hr}) _; first smt().
    rewrite /= in hread; rewrite hread.
    split; first smt().
    apply gs_signs_step; smt().
  auto => /> &hr ho he hb.
  split; first by rewrite /gs_signs_prefix; smt().
  move=> i0 out0 hdone hi0 hi32 hp.
  rewrite W64.ultE W64.of_uintK /= in hdone.
  have hi : W64.to_uint i0 = 32 by smt().
  move: hp; rewrite hi; exact.
qed.

lemma gs_copy_signs_lossless : islossless GS_Signer.__sample_gauss_N_copy_signs_at.
proof.
  proc.
  while (W64.to_uint i <= W64.to_uint signbytes)
        (W64.to_uint signbytes - W64.to_uint i).
  + move=> z; auto => /> &hr hi hguard.
    rewrite W64.ultE in hguard.
    have := W64.to_uint_cmp signbytes{hr}.
    rewrite W64.to_uintD_small 1:/# W64.to_uint1; smt().
  auto => />; smt(W64.to_uint_cmp).
qed.

lemma gs_copy_signs_total stream before buf offset :
  phoare [GS_Signer.__sample_gauss_N_copy_signs_at :
    signsp = before /\ bufp = buf /\ signbytes = W64.of_int 32 /\
    W64.to_uint signoff = offset /\ 0 <= offset /\ offset + 32 <= 512 /\
    gs_buffer_segment stream buf 0 0 32
    ==>
    gs_signs_result stream before res offset] = 1%r.
proof. by conseq gs_copy_signs_lossless (gs_copy_signs_correct stream before buf offset). qed.
