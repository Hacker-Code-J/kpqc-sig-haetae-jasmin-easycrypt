require import AllCore List IntDiv Ring StdOrder BitEncoding.

theory Debug4.

lemma ntt_outer_progress z :
  1 <= z =>
  0 < z /\
  forall start0,
    (0 < z => 256 - start0 <= 0 => ! start0 < 256) /\
    (! start0 < 256 => 0 < z => z %/ 2 < z).
proof.
  move=> hz1; split.
  + move: hz1.
    rewrite -ltzS.
    trivial.
  move=> start0.
  print goal 1.
abort.

end Debug4.
