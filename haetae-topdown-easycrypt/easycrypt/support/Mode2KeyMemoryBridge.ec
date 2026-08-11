require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

import SLH64.

require import PackedKeyPrefix.

theory Mode2KeyMemoryBridge.

op vk_buffer_at
    (mem : global_mem_t) (base : int) (vk : BArray2080.t) : bool =
  forall i, 0 <= i < PackedKeyPrefix.mode2_vkbytes =>
    loadW8 mem (base + i) = BArray2080.get8 vk i.

op sk_hash_prefix_at
    (mem : global_mem_t) (base : int) (sk : BArray2752.t) : bool =
  forall i, 0 <= i < PackedKeyPrefix.mode2_vkbytes =>
    loadW8 mem (base + i) = BArray2752.get8 sk i.

lemma keygen_prefix_marshaled_to_sign_verify_hash_input sk vk mem base :
  PackedKeyPrefix.vk_prefix_eq
    sk vk PackedKeyPrefix.mode2_vkbytes =>
  vk_buffer_at mem base vk =>
  sk_hash_prefix_at mem base sk.
proof.
move=> hpref hvk.
rewrite /sk_hash_prefix_at => i hi.
rewrite (hvk i hi).
by rewrite (hpref i hi).
qed.

lemma stored_vk_buffer_at mem base vk :
  vk_buffer_at
    (stores mem base
      (take PackedKeyPrefix.mode2_vkbytes (BArray2080.to_list vk)))
    base vk.
proof.
rewrite /vk_buffer_at => i hi.
rewrite /loadW8 get_storesE.
have hsize :
    size (take PackedKeyPrefix.mode2_vkbytes (BArray2080.to_list vk)) =
    PackedKeyPrefix.mode2_vkbytes by
  rewrite size_take 1:/# BArray2080.size_to_list
          /PackedKeyPrefix.mode2_vkbytes /=.
have hin :
    base <= base + i <
    base +
      size (take PackedKeyPrefix.mode2_vkbytes (BArray2080.to_list vk))
  by rewrite hsize; smt().
rewrite hin /=.
rewrite nth_take 1:/# 1:/#.
have -> : base + i - base = i by ring.
by rewrite BArray2080.get_to_list.
qed.

lemma keygen_prefix_memory_relation_is_constructible sk vk mem base :
  PackedKeyPrefix.vk_prefix_eq
    sk vk PackedKeyPrefix.mode2_vkbytes =>
  sk_hash_prefix_at
    (stores mem base
      (take PackedKeyPrefix.mode2_vkbytes (BArray2080.to_list vk)))
    base sk.
proof.
move=> hpref.
apply (keygen_prefix_marshaled_to_sign_verify_hash_input
         sk vk
         (stores mem base
           (take PackedKeyPrefix.mode2_vkbytes (BArray2080.to_list vk)))
         base hpref).
exact (stored_vk_buffer_at mem base vk).
qed.

end Mode2KeyMemoryBridge.
