require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import KeygenMode2ParentTarget.

theory PackedKeyPrefix.

module Parent = KeygenMode2ParentTarget.M.

op mode2_vkbytes : int = 992.

op vk_prefix_eq
    (sk : BArray2752.t) (vk : BArray2080.t) (n : int) : bool =
  forall j, 0 <= j < n =>
    BArray2752.get8 sk j = BArray2080.get8 vk j.

op copied_prefix
    (sk : BArray2752.t) (vk : BArray2080.t) (count : int) : bool =
  0 <= count <= mode2_vkbytes /\
  forall j, 0 <= j < count =>
    BArray2752.get8 sk j = BArray2080.get8 vk j.

lemma vk_prefix_eq_set_after
    (sk : BArray2752.t) (vk : BArray2080.t)
    (n p : int) (b : W8.t) :
  vk_prefix_eq sk vk n =>
  n <= p =>
  vk_prefix_eq (BArray2752.set8 sk p b) vk n.
proof.
move=> hpref hafter.
rewrite /vk_prefix_eq in hpref.
rewrite /vk_prefix_eq => j hj.
rewrite BArray2752.get_set_if.
have -> : !(0 <= p < BArray2752.size /\ j = p) by smt().
exact (hpref j hj).
qed.

lemma copied_prefix_step
    (sk : BArray2752.t) (vk : BArray2080.t) (count : int) :
  copied_prefix sk vk count =>
  count < mode2_vkbytes =>
  copied_prefix
    (BArray2752.set8 sk count (BArray2080.get8 vk count))
    vk (count + 1).
proof.
move=> [hcount hpref] hlt.
rewrite /copied_prefix.
split; first smt().
move=> j hj.
rewrite BArray2752.get_setE 1:/#.
case: (j = count) => [-> // | hne].
rewrite hpref 1:/#.
trivial.
qed.

lemma copied_prefix_complete sk vk :
  copied_prefix sk vk mode2_vkbytes =>
  vk_prefix_eq sk vk mode2_vkbytes.
proof.
by rewrite /copied_prefix /vk_prefix_eq => -[_ h].
qed.

end PackedKeyPrefix.
