require import AllCore IntDiv.

from Jasmin require import JModel_x86.

import SLH64.

require import ApiKeyMemoryBridge.

theory RawApiAddressBridge.

(* Claim OBL-API-ADDRESS-BINDING: integer ABI addresses and W64 exporter
   addresses denote the same byte address only on the canonical range. *)

op canonical_ui64_address (a : int) : bool =
  0 <= a < W64.modulus.

op canonical_region (a n : int) : bool =
  0 <= a /\ 0 <= n /\ a + n <= W64.modulus.

op example_addr : int = 1474.
op mode2_vkbytes : int = 992.
op mode2_skbytes : int = 1408.
op mode2_sigbytes : int = 1474.

lemma canonical_ui64_address_roundtrip (a : int) :
  canonical_ui64_address a =>
  W64.to_uint (W64.of_int a) = a.
proof.
move=> ha.
rewrite /canonical_ui64_address in ha.
rewrite W64.of_uintK /=.
smt().
qed.

lemma canonical_region_valid_region_int (a n : int) :
  canonical_region a n =>
  ApiKeyMemoryBridge.valid_region_int a n.
proof.
rewrite /canonical_region /ApiKeyMemoryBridge.valid_region_int.
smt().
qed.

lemma canonical_region_valid_region_w64 (a n : int) :
  canonical_region a n =>
  ApiKeyMemoryBridge.valid_region_w64
    (W64.of_int a) (W64.of_int n).
proof.
move=> hcanon.
rewrite /ApiKeyMemoryBridge.valid_region_w64.
rewrite W64.of_uintK W64.of_uintK /=.
move: hcanon; rewrite /canonical_region.
smt().
qed.

lemma importer_exporter_address_equality (a : int) :
  canonical_ui64_address a =>
  W64.to_uint (W64.of_int a) = a.
proof.
exact (canonical_ui64_address_roundtrip a).
qed.

lemma importer_addr_to_exporter_w64
    (a : int) :
  canonical_ui64_address a =>
  W64.to_uint (W64.of_int (W64.to_uint (W64.of_int a))) = a.
proof.
move=> ha.
have hround := canonical_ui64_address_roundtrip a ha.
by rewrite hround.
qed.

lemma canonical_address_992 :
  W64.to_uint (W64.of_int 992) = 992.
proof.
rewrite W64.of_uintK /=.
smt().
qed.

lemma canonical_address_1408 :
  W64.to_uint (W64.of_int 1408) = 1408.
proof.
rewrite W64.of_uintK /=.
smt().
qed.

lemma canonical_address_1474 :
  W64.to_uint (W64.of_int example_addr) = example_addr.
proof.
rewrite /example_addr W64.of_uintK /=.
smt().
qed.

lemma canonical_region_1474_992 :
  canonical_region example_addr 992.
proof.
rewrite /canonical_region /example_addr /=.
rewrite /W64.modulus /=.
smt().
qed.

lemma canonical_region_1474_1408 :
  canonical_region example_addr 1408.
proof.
rewrite /canonical_region /example_addr /=.
rewrite /W64.modulus /=.
smt().
qed.

lemma canonical_region_vk_992 :
  canonical_region 0 mode2_vkbytes.
proof.
rewrite /mode2_vkbytes /canonical_region /=.
rewrite /W64.modulus /=.
smt().
qed.

lemma canonical_region_sk_1408 :
  canonical_region 0 mode2_skbytes.
proof.
rewrite /mode2_skbytes /canonical_region /=.
rewrite /W64.modulus /=.
smt().
qed.

lemma canonical_region_sig_1474 :
  canonical_region 0 mode2_sigbytes.
proof.
rewrite /mode2_sigbytes /canonical_region /=.
rewrite /W64.modulus /=.
smt().
qed.

lemma canonical_region_1474_1408_valid_region_int :
  ApiKeyMemoryBridge.valid_region_int example_addr 1408.
proof.
exact (canonical_region_valid_region_int
         example_addr 1408
         canonical_region_1474_1408).
qed.

lemma canonical_region_1474_1408_valid_region_w64 :
  ApiKeyMemoryBridge.valid_region_w64
    (W64.of_int example_addr)
    (W64.of_int 1408).
proof.
exact (canonical_region_valid_region_w64
         example_addr 1408
         canonical_region_1474_1408).
qed.

lemma canonical_region_vk_992_valid_region_w64 :
  ApiKeyMemoryBridge.valid_region_w64
    (W64.of_int 0) (W64.of_int mode2_vkbytes).
proof.
exact (canonical_region_valid_region_w64
         0 mode2_vkbytes
         canonical_region_vk_992).
qed.

lemma canonical_region_sk_1408_valid_region_w64 :
  ApiKeyMemoryBridge.valid_region_w64
    (W64.of_int 0) (W64.of_int mode2_skbytes).
proof.
exact (canonical_region_valid_region_w64
         0 mode2_skbytes
         canonical_region_sk_1408).
qed.

lemma canonical_region_sig_1474_valid_region_w64 :
  ApiKeyMemoryBridge.valid_region_w64
    (W64.of_int 0) (W64.of_int mode2_sigbytes).
proof.
exact (canonical_region_valid_region_w64
         0 mode2_sigbytes
         canonical_region_sig_1474).
qed.

lemma canonical_region_has_witness :
  exists a n, canonical_region a n.
proof.
exists example_addr.
exists 1408.
exact canonical_region_1474_1408.
qed.

lemma mode2_vk_region_bridge (a : int) :
  canonical_region a 992 =>
  canonical_ui64_address a /\
  ApiKeyMemoryBridge.valid_region_int a 992 /\
  ApiKeyMemoryBridge.valid_region_w64 (W64.of_int a) (W64.of_int 992) /\
  W64.to_uint (W64.of_int a) = a.
proof.
rewrite /canonical_region /canonical_ui64_address
        /ApiKeyMemoryBridge.valid_region_int
        /ApiKeyMemoryBridge.valid_region_w64.
rewrite !W64.of_uintK /= /W64.modulus.
smt().
qed.

lemma mode2_sk_region_bridge (a : int) :
  canonical_region a 1408 =>
  canonical_ui64_address a /\
  ApiKeyMemoryBridge.valid_region_int a 1408 /\
  ApiKeyMemoryBridge.valid_region_w64 (W64.of_int a) (W64.of_int 1408) /\
  W64.to_uint (W64.of_int a) = a.
proof.
rewrite /canonical_region /canonical_ui64_address
        /ApiKeyMemoryBridge.valid_region_int
        /ApiKeyMemoryBridge.valid_region_w64.
rewrite !W64.of_uintK /= /W64.modulus.
smt().
qed.

lemma mode2_sig_region_bridge (a : int) :
  canonical_region a 1474 =>
  canonical_ui64_address a /\
  ApiKeyMemoryBridge.valid_region_int a 1474 /\
  ApiKeyMemoryBridge.valid_region_w64 (W64.of_int a) (W64.of_int 1474) /\
  W64.to_uint (W64.of_int a) = a.
proof.
rewrite /canonical_region /canonical_ui64_address
        /ApiKeyMemoryBridge.valid_region_int
        /ApiKeyMemoryBridge.valid_region_w64.
rewrite !W64.of_uintK /= /W64.modulus.
smt().
qed.

end RawApiAddressBridge.
