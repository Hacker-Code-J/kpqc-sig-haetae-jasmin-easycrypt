require import AllCore IntDiv List Distr DList DProd Finite StdOrder.
from Jasmin require import JModel_x86.
require import GaussianUniformBytes HyperballIidPayloadSpec HyperballIidPayloadBatch
  HyperballIidSquareLaw GaussianRenyiConditioning IidExponentialTail.

(* The first two calls retain 257 accepted payloads each. Every later call
   retains 256. Each call has its own independent 32-byte sign block. *)
type hrj_block = int list * W8.t list.
type hrj_input = hrj_block * (hrj_block * hrj_block list).

op hrj_blockd (payload : int distr) (n : int) : hrj_block distr =
  dlist payload n `*` gbc_bytes 32.

op hrj_source (payload : int distr) (mode : int) : hrj_input distr =
  hrj_blockd payload 257 `*`
    (hrj_blockd payload 257 `*` dlist (hrj_blockd payload 256) (hip_polys mode-2)).

op hrj_blocks (input : hrj_input) : hrj_block list =
  input.`1 :: input.`2.`1 :: input.`2.`2.

lemma hrj_mode_budget mode : hip_mode mode =>
  0 <= hip_polys mode-2 <= 9 /\ 0 <= hip_total mode <= 2818 /\
  257+257+256*(hip_polys mode-2)=hip_total mode.
proof.
  move=> hm; have hp := hip_mode_polys mode hm.
  rewrite /hip_total /hip_count; smt().
qed.

lemma hrj_block_ll payload n : is_lossless payload => is_lossless (hrj_blockd payload n).
proof.
  move=> hp; by rewrite /hrj_blockd dprod_ll (dlist_ll payload n hp) (gbc_bytes_ll 32).
qed.

lemma hrj_source_ll payload mode : is_lossless payload => is_lossless (hrj_source payload mode).
proof.
  move=> hp; rewrite /hrj_source !dprod_ll.
  have h257 := hrj_block_ll payload 257 hp.
  have ht := dlist_ll _ (hip_polys mode-2) (hrj_block_ll payload 256 hp).
  smt().
qed.

lemma hrj_block_finite payload n : is_finite (support payload) => 0<=n =>
  is_finite (support (hrj_blockd payload n)).
proof.
  move=> hp hn; rewrite /hrj_blockd; apply finite_dprod.
  + exact (iet_finite_dlist payload n hp hn).
  rewrite /gbc_bytes; apply iet_finite_dlist; last trivial.
  rewrite /W8.dword; exact finite_duniform.
qed.

lemma hrj_source_finite payload mode : is_finite (support payload) => hip_mode mode =>
  is_finite (support (hrj_source payload mode)).
proof.
  move=> hp hm; have [hn _] := hrj_mode_budget mode hm.
  rewrite /hrj_source; apply finite_dprod.
  + exact (hrj_block_finite payload 257 hp _); trivial.
  apply finite_dprod.
  + exact (hrj_block_finite payload 257 hp _); trivial.
  apply iet_finite_dlist; last smt().
  exact (hrj_block_finite payload 256 hp _); trivial.
qed.
