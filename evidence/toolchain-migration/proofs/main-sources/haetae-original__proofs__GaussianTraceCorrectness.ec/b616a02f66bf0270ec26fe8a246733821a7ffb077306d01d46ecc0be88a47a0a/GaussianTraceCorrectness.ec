require import AllCore IntDiv List.
from Jasmin require import JModel_x86.
require import SamplerTarget GaussianTraceSpec GaussianConsumerCorrectness
  GaussianTraceProperties GaussianBufferLemmas SigmaCorrectness GaussianConsumerSpec.
import SLH64.

lemma gauss_trace_position_next (k : int) :
  W64.of_int (26 * k) + W64.of_int 26 = W64.of_int (26 * (k + 1)).
proof. by rewrite -W64.of_intD; congr; smt(). qed.

lemma gauss_trace_remaining_next (b k : int) :
  W64.of_int (b - 26 * k) - W64.of_int 26 =
  W64.of_int (b - 26 * (k + 1)).
proof. by rewrite -W64.of_intS; congr; smt(). qed.

lemma gauss_trace_remaining_uint (b k : int) :
  0 <= b <= 8192 => 0 <= 26 * k <= b =>
  W64.to_uint (W64.of_int (b - 26 * k)) = b - 26 * k.
proof. move=> hb hk; rewrite W64.of_uintK /=; apply modz_small; smt(). qed.

lemma gauss_trace_position_uint (b k : int) :
  0 <= b <= 8192 => 0 <= 26 * k <= b =>
  W64.to_uint (W64.of_int (26 * k)) = 26 * k.
proof. move=> hb hk; rewrite W64.of_uintK /=; apply modz_small; smt(). qed.

lemma gauss_trace_last_test (c : W64.t) (n : int) :
  0 < n <= 512 =>
  (c = W64.of_int (n - 1)) = (W64.to_uint c = n - 1).
proof.
  move=> hn.
  rewrite W64.to_uint_eq W64.of_uintK /=.
  have -> : (n - 1) %% 18446744073709551616 = n - 1 by
    apply modz_small; smt().
  trivial.
qed.

(* One imperative update agrees with the integer-count trace step, including
   the candidate write before acceptance and the dummy-last exception. *)
lemma gauss_trace_step_words (n : int) (dont : bool)
    (r : BArray4096.t) (lo hi count : W64.t) (event : gauss_event) :
  0 <= W64.to_uint count < n => n <= 512 =>
  0 <= W64.to_uint event.`4 <= 1 =>
  (if dont /\ count = W64.of_int n - W64.one then r
     else BArray4096.set64 r (W64.to_uint count) event.`1,
   lo + (event.`2 `&` (W64.zero - event.`4)),
   hi + (event.`3 `&` (W64.zero - event.`4)),
   W64.to_uint (count + event.`4)) =
  gauss_trace_step n dont (r, lo, hi, W64.to_uint count) event.
proof.
  move=> hc hn ha.
  rewrite /gauss_trace_step /=.
  have -> /= : !(n <= W64.to_uint count) by smt().
  rewrite gauss_trace_last_test 1:/# gauss_counter_add 1:/# 1:ha.
  trivial.
qed.

lemma gauss_trace_attempt_bounds (b k : int) :
  0 <= b <= 8192 => 0 <= k <= b %/ 26 =>
  0 <= 26 * k <= b /\ b %/ 26 <= 315.
proof.
  move=> hb hk.
  have := divz_eq b 26.
  have := modz_cmp b 26.
  smt().
qed.

lemma gauss_trace_exhausted (b k : int) :
  0 <= b => 0 <= k <= b %/ 26 => b - 26 * k < 26 => k = b %/ 26.
proof.
  move=> hb hk hs.
  have := divz_eq b 26.
  have := modz_cmp b 26.
  smt().
qed.

lemma gauss_trace_has_next (b k : int) :
  0 <= b => 0 <= k <= b %/ 26 => 26 <= b - 26 * k => k + 1 <= b %/ 26.
proof.
  move=> hb hk hs.
  have := divz_eq b 26.
  have := modz_cmp b 26.
  smt().
qed.

op gauss_trace_relation (buf : BArray8192.t) (n b : int) (dont : bool)
    (values : BArray4096.t) (squares : BArray16.t)
    (current : BArray4096.t) (sum : BArray16.t)
    (count pos bytes limit : W64.t) : bool =
  exists attempts,
    0 <= attempts <= b %/ 26 /\
    pos = W64.of_int (26 * attempts) /\
    bytes = W64.of_int (b - 26 * attempts) /\
    (limit = W64.of_int n \/
      (limit = count /\ W64.to_uint bytes < 26)) /\
    (current, BArray16.get64 sum 0, BArray16.get64 sum 1,
     W64.to_uint count) =
      gauss_trace_prefix buf n dont values squares attempts.

lemma gauss_trace_relation_done buf n b dont values squares current sum
    count pos bytes limit :
  0 <= n <= 512 => 0 <= b <= 8192 =>
  gauss_trace_relation buf n b dont values squares current sum count pos bytes limit =>
  !(count \ult limit) =>
  (current, BArray16.get64 sum 0, BArray16.get64 sum 1,
   W64.to_uint count) = gauss_trace_prefix buf n dont values squares (b %/ 26).
proof.
  move=> hn hb.
  rewrite /gauss_trace_relation.
  move=> [attempts [ha [hp [hbytes [hlimit hstate]]]]] hstop.
  have [hapos hmax] := gauss_trace_attempt_bounds b attempts hb ha.
  have hremaining := gauss_trace_remaining_uint b attempts hb hapos.
  have hn0 : 0 <= n by smt().
  have ha0 : 0 <= attempts by smt().
  have hbounds := gauss_trace_prefix_count_bounds buf n dont values squares
    attempts hn0 ha0.
  case: hlimit => [hlimit | [hlimit hshort]].
  + have hnword : W64.to_uint (W64.of_int n) = n by
      rewrite W64.of_uintK /=; apply modz_small; smt().
    have hcstop : n <= W64.to_uint count by smt(W64.ultE).
    have hfull : (gauss_trace_prefix buf n dont values squares attempts).`4 = n by
      smt().
    by rewrite (gauss_trace_prefix_full_stable buf n dont values squares
      attempts (b %/ 26) ha hfull) -hstate.
  rewrite hbytes hremaining in hshort.
  have heq : attempts = b %/ 26 by apply gauss_trace_exhausted; smt().
  by rewrite -heq.
qed.

lemma gauss_trace_relation_initial buf n b dont values squares :
  0 <= n <= 512 => 0 <= b <= 8192 =>
  gauss_trace_relation buf n b dont values squares values squares
    W64.zero W64.zero (W64.of_int b) (W64.of_int n).
proof.
  move=> hn hb; rewrite /gauss_trace_relation.
  exists 0; rewrite gauss_trace_prefix0 /gauss_trace_initial /=.
  have := divz_eq b 26.
  have := modz_cmp b 26.
  smt().
qed.

lemma gauss_trace_relation_step buf n b dont values squares current sum
    count pos bytes limit :
  0 <= n <= 512 => 0 <= b <= 8192 =>
  gauss_trace_relation buf n b dont values squares current sum count pos bytes limit =>
  count \ult limit => !(bytes \ult W64.of_int 26) =>
  let event = sigma76_spec (gauss_chunk buf (W64.to_uint pos)) in
  let mask = W64.zero - event.`4 in
  let updated = if dont /\ count = limit - W64.one then current
    else BArray4096.set64 current (W64.to_uint count) event.`1 in
  let low = BArray16.get64 sum 0 + (event.`2 `&` mask) in
  let high = BArray16.get64 sum 1 + (event.`3 `&` mask) in
  gauss_trace_relation buf n b dont values squares updated
    (BArray16.set64 (BArray16.set64 sum 0 low) 1 high)
    (count + event.`4) (pos + W64.of_int 26) (bytes - W64.of_int 26) limit.
proof.
  move=> hn hb hrel hloop hbytes.
  move: hrel; rewrite /gauss_trace_relation.
  move=> [attempts [ha [hp [hbytesword [hlimit hstate]]]]].
  have [hapos hmax] := gauss_trace_attempt_bounds b attempts hb ha.
  have hremaining := gauss_trace_remaining_uint b attempts hb hapos.
  have hposition := gauss_trace_position_uint b attempts hb hapos.
  have hlimitword : limit = W64.of_int n by smt(W64.ultE).
  have hnword : W64.to_uint (W64.of_int n) = n by
    rewrite W64.of_uintK /=; apply modz_small; smt().
  have hc : 0 <= W64.to_uint count < n by
    move: hloop; rewrite hlimitword W64.ultE hnword; smt(W64.to_uint_cmp).
  have hbytesint : 26 <= b - 26 * attempts by
    move: hbytes; rewrite W64.ultE hbytesword hremaining W64.of_uintK /=; smt().
  have hnextbound : attempts + 1 <= b %/ 26 by
    apply gauss_trace_has_next; smt().
  have hevent : sigma76_spec (gauss_chunk buf (W64.to_uint pos)) =
    gauss_event_at buf attempts by rewrite hp hposition /gauss_event_at.
  rewrite hevent /=.
  have hbit := gauss_event_accept_bit buf attempts.
  have hnmax : n <= 512 by smt().
  have ha0 : 0 <= attempts by smt().
  have hstep := gauss_trace_step_words n dont current
    (BArray16.get64 sum 0) (BArray16.get64 sum 1) count
    (gauss_event_at buf attempts) hc hnmax hbit.
  have hnext := gauss_trace_prefixS buf n dont values squares attempts ha0.
  rewrite -hstate -hstep in hnext.
  exists (attempts + 1).
  rewrite hp hbytesword hlimitword gauss_trace_position_next
    gauss_trace_remaining_next /=.
  move: hnext; rewrite /= => hnext.
  smt().
qed.

lemma gauss_trace_relation_active_offset buf n b dont values squares current sum
    count pos bytes limit :
  0 <= b <= 8192 =>
  gauss_trace_relation buf n b dont values squares current sum count pos bytes limit =>
  !(bytes \ult W64.of_int 26) => 0 <= W64.to_uint pos <= 8166.
proof.
  move=> hb; rewrite /gauss_trace_relation.
  move=> [attempts [ha [hp [hbytes [hlimit hstate]]]]] hguard.
  have [hapos hmax] := gauss_trace_attempt_bounds b attempts hb ha.
  have hremaining := gauss_trace_remaining_uint b attempts hb hapos.
  have hposition := gauss_trace_position_uint b attempts hb hapos.
  move: hguard; rewrite hbytes W64.ultE hremaining W64.of_uintK /=.
  rewrite hp hposition; smt().
qed.

lemma gauss_trace_relation_result buf n b dont values squares count0 current sum
    count pos bytes limit :
  0 <= n <= 512 => 0 <= b <= 8192 =>
  gauss_trace_relation buf n b dont values squares current sum count pos bytes limit =>
  !(count \ult limit) =>
  (current,
   BArray16.set64
     (BArray16.set64 sum 0 (BArray16.get64 sum 0 `&` W64.of_int 281474976710655))
     1 (BArray16.get64 sum 1 + (BArray16.get64 sum 0 `>>>` 48)),
   BArray8.set64 count0 0 count) =
  gauss_trace_result buf n b dont values squares count0.
proof.
  move=> hn hb hrel hstop.
  have hstate := gauss_trace_relation_done buf n b dont values squares
    current sum count pos bytes limit hn hb hrel hstop.
  rewrite /gauss_trace_result -hstate /gauss_normalize /=.
  by rewrite (gauss_square_overwrite sum squares).
qed.

lemma sample_gauss_trace_correct (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  hoare [SamplerTarget.M._sample_gauss :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192
    ==>
    res = gauss_trace_result buf n b (d <> W64.zero) values squares count0].
proof.
  proc; wp.
  while (0 <= n <= 512 /\ 0 <= b <= 8192 /\
    sbufp = buf /\ sdont = d /\ scoefcntp = count0 /\
    coefcnt = scoefcnt /\ len = slen /\
    gauss_trace_relation buf n b (d <> W64.zero) values squares
      srp ssqsump scoefcnt spos sbytecnt slen).
  + wp; sp 1; if.
    - auto => />.
      move=> &hr hn0 hnmax hb0 hbmax attempts ha0 haK hlimit hstate hloop hbytes.
      have hshort : W64.to_uint (W64.of_int (b - 26 * attempts)) < 26 by
        move: hbytes; rewrite W64.ultE (W64.of_uintK 26) /=.
      rewrite /gauss_trace_relation; exists attempts.
      split; first by split.
      split; first done.
      split; first done.
      split; first by right; split.
      exact hstate.
    wp; ecall (sigma76_regs_correct randp).
    while (0 <= k <= 26 /\ 0 <= W64.to_uint pos <= 8166 /\
      gauss_chunk_prefix bufp_tmp randp (W64.to_uint pos) k).
    - auto => />.
      move=> &hr hk0 hk26 hp0 hpmax hprefix hguard.
      have hpos : 0 <= W64.to_uint pos{hr} <= 8166 by split.
      have hk : 0 <= k{hr} < 26 by split.
      have hindex := gauss_chunk_word_index (W64.to_uint pos{hr}) k{hr} hpos hk.
      rewrite W64.to_uintK in hindex.
      rewrite hindex.
      split; first smt().
      exact (gauss_chunk_prefix_step bufp_tmp{hr} randp{hr}
        (W64.to_uint pos{hr}) k{hr} hk hprefix).
    auto => />.
    move=> &hr hn0 hnmax hb0 hbmax attempts ha0 haK hlimit hstate hloop hbytes.
    have hn : 0 <= n <= 512 by split.
    have hb : 0 <= b <= 8192 by split.
    have hrel : gauss_trace_relation buf n b (d <> W64.zero) values squares
      srp{hr} ssqsump{hr} scoefcnt{hr} (W64.of_int (26 * attempts))
      (W64.of_int (b - 26 * attempts)) slen{hr}.
    - rewrite /gauss_trace_relation; exists attempts.
      split; first by split.
      split; first done.
      split; first done.
      split; first exact hlimit.
      exact hstate.
    have hpos := gauss_trace_relation_active_offset buf n b (d <> W64.zero)
      values squares srp{hr} ssqsump{hr} scoefcnt{hr}
      (W64.of_int (26 * attempts)) (W64.of_int (b - 26 * attempts))
      slen{hr} hb hrel hbytes.
    split.
    - split; first smt().
      exact (gauss_chunk_prefix0 buf randp{hr} (W64.to_uint (W64.of_int (26 * attempts)))).
    move=> k0 randp0 hdone hk0 hk26 hp0 hpmax hprefix.
    have hk : k0 = 26 by smt().
    move: hprefix; rewrite hk => hprefix.
    have hcopied := gauss_chunk_prefix_full buf randp0
      (W64.to_uint (W64.of_int (26 * attempts))) hprefix.
    have hstep := gauss_trace_relation_step buf n b (d <> W64.zero)
      values squares srp{hr} ssqsump{hr} scoefcnt{hr}
      (W64.of_int (26 * attempts)) (W64.of_int (b - 26 * attempts))
      slen{hr} hn hb hrel hloop hbytes.
    move: hstep; rewrite -hcopied /= => hstep.
    rewrite /protect_64 /protect_ptr.
    smt().
  auto => />.
  move=> &hr hn0 hnmax hb0 hbmax.
  have hn : 0 <= gauss_requested counts{hr} <= 512 by split.
  have hb : 0 <= gauss_available counts{hr} <= 8192 by split.
  split.
  + have hinit := gauss_trace_relation_initial buf (gauss_requested counts{hr})
      (gauss_available counts{hr}) (d <> W64.zero) values squares hn hb.
    have hbytes : W64.of_int (gauss_available counts{hr}) =
      counts{hr} `>>>` 32 by rewrite /gauss_available W64.to_uintK.
    have hlimit : W64.of_int (gauss_requested counts{hr}) =
      counts{hr} `&` W64.of_int 4294967295 by rewrite /gauss_requested W64.to_uintK.
    by move: hinit; rewrite hbytes hlimit.
  move=> scoefcnt0 slen0 srp0 ssqsump0 hstop attempts ha0 haK hlimit hstate.
  have hrel : gauss_trace_relation buf (gauss_requested counts{hr})
    (gauss_available counts{hr}) (d <> W64.zero) values squares
    srp0 ssqsump0 scoefcnt0 (W64.of_int (26 * attempts))
    (W64.of_int (gauss_available counts{hr} - 26 * attempts)) slen0.
  - rewrite /gauss_trace_relation; exists attempts.
    split; first by split.
    split; first done.
    split; first done.
    split; first exact hlimit.
    exact hstate.
  exact (gauss_trace_relation_result buf (gauss_requested counts{hr})
    (gauss_available counts{hr}) (d <> W64.zero) values squares count0
    srp0 ssqsump0 scoefcnt0 (W64.of_int (26 * attempts))
    (W64.of_int (gauss_available counts{hr} - 26 * attempts)) slen0 hn hb hrel hstop).
qed.

lemma sample_gauss_jazz_trace_correct (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  hoare [SamplerTarget.M.sample_gauss_jazz :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192
    ==>
    res = gauss_trace_result buf n b (d <> W64.zero) values squares count0].
proof.
  proc; call (sample_gauss_trace_correct buf n b d values squares count0).
  wp; skip; auto => />.
qed.

lemma sample_gauss_trace_total_correct (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  phoare [SamplerTarget.M._sample_gauss :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192
    ==>
    res = gauss_trace_result buf n b (d <> W64.zero) values squares count0] = 1%r.
proof.
  by conseq sample_gauss_lossless
    (sample_gauss_trace_correct buf n b d values squares count0).
qed.

lemma sample_gauss_jazz_trace_total_correct (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  phoare [SamplerTarget.M.sample_gauss_jazz :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b <= 8192
    ==>
    res = gauss_trace_result buf n b (d <> W64.zero) values squares count0] = 1%r.
proof.
  by conseq sample_gauss_jazz_lossless
    (sample_gauss_jazz_trace_correct buf n b d values squares count0).
qed.

lemma sample_gauss_jazz_packed_trace_total (buf : BArray8192.t) (n b : int) (d : W64.t)
    (values : BArray4096.t) (squares : BArray16.t) (count0 : BArray8.t) :
  phoare [SamplerTarget.M.sample_gauss_jazz :
    bufp = buf /\ rp = values /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ counts = W64.of_int (b * 4294967296 + n) /\
    0 <= n <= 512 /\ 0 <= b <= 8192
    ==>
    res = gauss_trace_result buf n b (d <> W64.zero) values squares count0] = 1%r.
proof.
  conseq (sample_gauss_jazz_trace_total_correct buf n b d values squares count0) => />.
  smt(gauss_counts_encode).
qed.
