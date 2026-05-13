require import AllCore List IntDiv Ring StdOrder BitEncoding.

theory Debug13.

lemma ntt_init_progress len0 :
  (len0 <= 0 => ! 1 <= len0) /\ true.
proof.
  split.
  + move=> h.
    have h' : ! 1 <= len0.
    + print goal 1.
abort.

end Debug13.
