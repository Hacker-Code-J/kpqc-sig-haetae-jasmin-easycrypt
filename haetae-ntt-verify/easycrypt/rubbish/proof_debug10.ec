require import AllCore List IntDiv Ring StdOrder BitEncoding.

theory Debug10.

lemma ntt_init_progress len0 :
  (len0 <= 0 => ! 1 <= len0) /\ true.
proof.
  split; trivial.
  print goal 1.
abort.

end Debug10.
