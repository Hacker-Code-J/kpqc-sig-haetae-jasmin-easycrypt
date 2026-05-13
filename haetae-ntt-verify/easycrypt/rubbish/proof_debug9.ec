require import AllCore.

theory Debug9.

lemma tail_shape len0 : (len0 <= 0 => ! 1 <= len0) /\ true.
proof.
split.
print goal 1.
abort.

end Debug9.
