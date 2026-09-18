require import AllCore IntDiv.

(* Pure arithmetic witnesses for prescribed repeated coefficient vectors.
   The guards fix those vectors' length and coefficient. These lemmas do not
   assert that any SHAKE seed generates the corresponding candidate stream. *)
lemma hyperball_mode2_prescribed_norm_boundary (count coefficient : int) :
  count = 1536 => coefficient = -1704795102 =>
  let total = count * (coefficient * coefficient) in
  total = 4464117257937700460544 /\
  total = 242 * 18446744073709551616 + 5192099988969472 /\
  total %% 18446744073709551616 = 5192099988969472 /\
  0 <= 5192099988969472 <= 6505809026482176 /\
  6505809026482176 < 18446744073709551616 <= total.
proof. by move=> -> ->; rewrite /=. qed.

lemma hyperball_mode3_prescribed_norm_boundary (count coefficient : int) :
  count = 2304 => coefficient = -334802028 =>
  let total = count * (coefficient * coefficient) in
  total = 258260884883511054336 /\
  total = 14 * 18446744073709551616 + 6467851577331712 /\
  total %% 18446744073709551616 = 6467851577331712 /\
  0 <= 6467851577331712 <= 22510896139993088 /\
  22510896139993088 < 18446744073709551616 <= total.
proof. by move=> -> ->; rewrite /=. qed.

lemma hyperball_mode5_prescribed_norm_boundary (count coefficient : int) :
  count = 2816 => coefficient = -632138900 =>
  let total = count * (coefficient * coefficient) in
  total = 1125272442323279360000 /\
  total = 61 * 18446744073709551616 + 21053826996711424 /\
  total %% 18446744073709551616 = 21053826996711424 /\
  0 <= 21053826996711424 <= 33503371683954688 /\
  33503371683954688 < 18446744073709551616 <= total.
proof. by move=> -> ->; rewrite /=. qed.
