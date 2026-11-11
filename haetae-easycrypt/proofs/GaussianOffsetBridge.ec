require import AllCore IntDiv.
from Jasmin require import JModel_x86.
require import ApiTarget SamplerTarget GaussianConsumerSpec GaussianWindowSpec
               GaussianConsumerCorrectness SigningSamplerBridge
               GaussianTraceSpec GaussianTraceCorrectness.
import SLH64.

theory GaussianOffsetBridge.

module Signer = ApiTarget.M(ApiTarget.Syscall).
module Sampler = SamplerTarget.M.

lemma offset_sigma_equiv_bounded :
  equiv [Signer.__sample_gauss_sigma76_regs ~ Sampler.__sample_gauss_sigma76_regs :
    ={randp} ==> ={res} /\ 0 <= W64.to_uint res{1}.`4 <= 1].
proof.
by conseq SigningSamplerBridge.signer_sigma76_equiv _ gauss_sigma_accept_bit => /#.
qed.

lemma sample_gauss_at_window_equiv
    (initial : BArray32768.t) (buf : BArray8192.t) (n b bo oo : int) :
  equiv [Signer.__sample_gauss_at ~ Sampler._sample_gauss :
    ={counts, dont_write_last, sqsump, coefcntp} /\
    gauss_requested counts{1} = n /\ gauss_available counts{1} = b /\
    0 <= n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff{1} = bo /\ W64.to_uint outoff{1} = oo /\
    bufp{1} = buf /\ bufp{2} = gauss_input_window buf bo /\
    rp{1} = initial /\ rp{2} = gauss_output_window initial oo
    ==>
    res{1}.`2 = res{2}.`2 /\ res{1}.`3 = res{2}.`3 /\
    res{2}.`1 = gauss_output_window res{1}.`1 oo /\
    gauss_big_output_frame initial res{1}.`1 oo n].
proof.
proc; wp.
while (={ssqsump, scoefcntp, sdont, slen, sbytecnt, spos, scoefcnt, coefcnt, len, randp} /\
  coefcnt{1} = scoefcnt{1} /\ len{1} = slen{1} /\
  W64.to_uint sbufoff{1} = bo /\ W64.to_uint soutoff{1} = oo /\
  sbufp{1} = buf /\ sbufp{2} = gauss_input_window buf bo /\
  srp{2} = gauss_output_window srp{1} oo /\
  gauss_big_output_frame initial srp{1} oo n /\
  gauss_window_bounds n b bo oo (W64.to_uint scoefcnt{1}) (W64.to_uint slen{1})
    (W64.to_uint spos{1}) (W64.to_uint sbytecnt{1})).
+ wp; sp 1 1; if.
  - by auto => />.
  - auto => />; smt(gauss_window_bounds_short).
  - wp; call offset_sigma_equiv_bounded.
    while (={k, randp, pos} /\ 0 <= k{1} <= 26 /\
      bufp_tmp{1} = buf /\ bufp_tmp{2} = gauss_input_window buf bo /\
      W64.to_uint sbufoff{1} = bo /\ base{1} = sbufoff{1} + pos{1} /\
      W64.to_uint sbufoff{1} + W64.to_uint pos{1} + 26 <= 8192).
    + auto => />; smt(gauss_input_window_read).
    auto => />.
    move=> &1 &2 hframe hn0 hn512 hb0 hbo hboend hoo hooend
      hc0 hcl hln hp0 hbytes0 hloop hbytes.
    rewrite W64.ultE in hloop.
    rewrite W64.ultE W64.of_uintK /= in hbytes.
    split; first smt().
    move=> k hk1 hk2 hk0 hk26 hchunk result ha0 ha1.
    rewrite /protect_64 /protect_ptr
      gauss_counter_add 1:/# 1:/# gauss_bytes_subtract 1:/#
      gauss_window_index_uint 1:/# 1:// gauss_window_output_uint 1:/# 1:/#
      gauss_output_window_set 1:/# 1:/#.
    have hnew := gauss_big_output_frame_set initial srp{1}
      (W64.to_uint soutoff{1}) n (W64.to_uint scoefcnt{2}) result.`1 _ hframe;
      first smt().
    smt().
auto => />; rewrite /gauss_requested /gauss_available /gauss_window_bounds
  /gauss_big_output_frame; smt().
qed.

lemma sample_gauss_at_total_frame
    (initial : BArray32768.t) (buf : BArray8192.t) (n b bo oo : int) :
  phoare [Signer.__sample_gauss_at :
    gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo /\
    bufp = buf /\ rp = initial
    ==>
    gauss_big_output_frame initial res.`1 oo n] = 1%r.
proof.
conseq (sample_gauss_at_window_equiv initial buf n b bo oo)
  sample_gauss_lossless => />.
move=> &1 _ _ _ _ _ _ _.
exists (gauss_output_window rp{1} (W64.to_uint outoff{1}),
  sqsump{1}, coefcntp{1}, gauss_input_window bufp{1} (W64.to_uint bufoff{1}),
  counts{1}, dont_write_last{1}).
trivial.
qed.

(* Exact finite-consumer semantics at the actual production helper.  The
   trace retains rejected speculative writes, the dummy-last rule, early
   requested-count completion, byte exhaustion, and final normalization. *)
lemma sample_gauss_at_trace_correct
    (initial : BArray32768.t) (buf : BArray8192.t) (n b bo oo : int)
    (d : W64.t) (squares : BArray16.t) (count0 : BArray8.t) :
  hoare [Signer.__sample_gauss_at :
    rp = initial /\ bufp = buf /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo
    ==>
    (gauss_output_window res.`1 oo, res.`2, res.`3) =
      gauss_trace_result (gauss_input_window buf bo) n b (d <> W64.zero)
        (gauss_output_window initial oo) squares count0 /\
    gauss_big_output_frame initial res.`1 oo n].
proof.
conseq (sample_gauss_at_window_equiv initial buf n b bo oo)
  (sample_gauss_trace_correct (gauss_input_window buf bo) n b d
    (gauss_output_window initial oo) squares count0) => />.
+ move=> &1 hn0 hn512 hb0 hbo hboend hoo hooend.
  exists (gauss_output_window rp{1} (W64.to_uint outoff{1}),
    sqsump{1}, coefcntp{1}, gauss_input_window bufp{1} (W64.to_uint bufoff{1}),
    counts{1}, dont_write_last{1}).
  smt().
+ smt().
qed.

lemma sample_gauss_at_trace_total_correct
    (initial : BArray32768.t) (buf : BArray8192.t) (n b bo oo : int)
    (d : W64.t) (squares : BArray16.t) (count0 : BArray8.t) :
  phoare [Signer.__sample_gauss_at :
    rp = initial /\ bufp = buf /\ sqsump = squares /\ coefcntp = count0 /\
    dont_write_last = d /\ gauss_requested counts = n /\ gauss_available counts = b /\
    0 <= n <= 512 /\ 0 <= b /\ 0 <= bo /\ bo + b <= 8192 /\
    0 <= oo /\ oo + n <= 4096 /\
    W64.to_uint bufoff = bo /\ W64.to_uint outoff = oo
    ==>
    (gauss_output_window res.`1 oo, res.`2, res.`3) =
      gauss_trace_result (gauss_input_window buf bo) n b (d <> W64.zero)
        (gauss_output_window initial oo) squares count0 /\
    gauss_big_output_frame initial res.`1 oo n] = 1%r.
proof.
by conseq (sample_gauss_at_total_frame initial buf n b bo oo)
  (sample_gauss_at_trace_correct initial buf n b bo oo d squares count0) => />.
qed.

end GaussianOffsetBridge.
