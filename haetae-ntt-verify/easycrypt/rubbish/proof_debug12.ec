require import AllCore List IntDiv Ring StdOrder BitEncoding.

theory Debug12.

lemma ntt_init_progress len0 :
  (len0 <= 0 => ! 1 <= len0) /\ true.
proof.
  split.
  + move=> h.
    have h' : ! 1 <= len0.
    + rewrite lezNgt.
      exact h.
    exact h'.
  + trivial.
qed.

end Debug12.
