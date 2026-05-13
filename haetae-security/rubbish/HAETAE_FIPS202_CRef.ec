require import AllCore IntDiv List.
require import HAETAE_Params HAETAE_FIPS202 HAETAE_Keccak1600.

theory HAETAE_FIPS202_CRef.

import HAETAE_Params.
import HAETAE_FIPS202.
import HAETAE_Keccak1600.

op cref_shake256_state_bytes : int = fips202_state_bytes.
op cref_shake256_rate_bytes : int = shake256_rate_bytes.
op cref_shake256_domain_separator : fips_byte = shake256_domain_separator.
op cref_shake256_final_padding_byte : fips_byte = fips202_final_padding_byte.

op cref_shake256_absorb_data_byte
   (input : fips_byte list) (inlen i : int) : fips_byte =
  if 0 <= i /\ i < inlen then nth 0 input i else 0.

op cref_shake256_absorb_padding_byte (inlen i : int) : fips_byte =
  if i = inlen /\ i = cref_shake256_rate_bytes - 1 then
    cref_shake256_domain_separator + cref_shake256_final_padding_byte
  else if i = inlen then cref_shake256_domain_separator
  else if i = cref_shake256_rate_bytes - 1 then
    cref_shake256_final_padding_byte
  else 0.

op cref_shake256_absorb_block_byte
   (input : fips_byte list) (inlen i : int) : fips_byte =
  if 0 <= i /\ i < inlen
  then cref_shake256_absorb_data_byte input inlen i
  else cref_shake256_absorb_padding_byte inlen i.

op cref_shake256_absorb_state
   (input : fips_byte list) (inlen : int) : fips202_state =
  mkseq
    (fun i =>
       if i < cref_shake256_rate_bytes
       then cref_shake256_absorb_block_byte input inlen i
       else 0)
    cref_shake256_state_bytes.

op cref_shake256_absorb_once
   (input : fips_byte list) (inlen : int) : fips202_state =
  fips202_keccak_f1600 (cref_shake256_absorb_state input inlen).

op cref_shake256_squeeze
   (st : fips202_state) (outlen : int) : fips_byte list =
  mkseq (fun i => nth 0 st i) outlen.

op cref_shake256
   (input : fips_byte list) (inlen outlen : int) : fips_byte list =
  cref_shake256_squeeze
    (cref_shake256_absorb_once input inlen)
    outlen.

type cref_keccak_state = fips202_state * int.

op cref_load64_lane (input : fips_byte list) (off : int) : keccak_lane =
  mkseq
    (fun bit =>
       keccak_byte_bit
         (nth 0 input (off + bit %/ 8))
         (bit %% 8))
    keccak_lane_bits.

op cref_store64_lane (lane : keccak_lane) : fips_byte list =
  mkseq (fun byte => keccak_lane_to_byte lane byte) 8.

op cref_shake256_absorb_state_lanes
   (input : fips_byte list) (inlen : int) : keccak_state =
  keccak_lanes_of_bytes (cref_shake256_absorb_state input inlen).

op cref_shake256_permuted_state_lanes
   (input : fips_byte list) (inlen : int) : keccak_state =
  keccak_f1600_lanes (cref_shake256_absorb_state_lanes input inlen).

op cref_shake256_permuted_state_bytes
   (input : fips_byte list) (inlen : int) : fips202_state =
  keccak_bytes_of_lanes (cref_shake256_permuted_state_lanes input inlen).

op cref_shake256_c_absorb_once
   (input : fips_byte list) (inlen : int) : cref_keccak_state =
  (cref_shake256_absorb_state input inlen, cref_shake256_rate_bytes).

op cref_shake256_c_squeeze_short
   (state : cref_keccak_state) (outlen : int) : fips_byte list =
  if state.`2 = cref_shake256_rate_bytes
  then cref_shake256_squeeze (fips202_keccak_f1600 state.`1) outlen
  else cref_shake256_squeeze state.`1 outlen.

op cref_shake256_c_api_short
   (input : fips_byte list) (inlen outlen : int) : fips_byte list =
  cref_shake256_c_squeeze_short
    (cref_shake256_c_absorb_once input inlen)
    outlen.

op cref_haetae_keygen_xof_absorb_bytes : int = seedbytes.
op cref_haetae_keygen_xof_squeeze_bytes : int = 2 * seedbytes + crhbytes.

lemma cref_shake256_state_bytesE :
  cref_shake256_state_bytes = 200.
proof. by rewrite /cref_shake256_state_bytes fips202_state_bytesE. qed.

lemma cref_shake256_rate_bytesE :
  cref_shake256_rate_bytes = 136.
proof. by rewrite /cref_shake256_rate_bytes shake256_rate_bytesE. qed.

lemma cref_shake256_domain_separatorE :
  cref_shake256_domain_separator = 31.
proof.
by rewrite /cref_shake256_domain_separator shake256_domain_separatorE.
qed.

lemma cref_shake256_final_padding_byteE :
  cref_shake256_final_padding_byte = 128.
proof.
by rewrite /cref_shake256_final_padding_byte fips202_final_padding_byteE.
qed.

lemma cref_shake256_absorb_block_byteE input inlen i :
  cref_shake256_absorb_block_byte input inlen i =
  shake256_absorb_once_short_block_byte input inlen i.
proof.
rewrite /cref_shake256_absorb_block_byte
        /cref_shake256_absorb_data_byte
        /cref_shake256_absorb_padding_byte
        /shake256_absorb_once_short_block_byte
        /cref_shake256_rate_bytes
        /cref_shake256_domain_separator
        /cref_shake256_final_padding_byte.
by case (0 <= i /\ i < inlen).
qed.

lemma cref_shake256_absorb_stateE input inlen :
  cref_shake256_absorb_state input inlen =
  shake256_absorb_once_short_state input inlen.
proof.
rewrite /cref_shake256_absorb_state
        /shake256_absorb_once_short_state
        /cref_shake256_state_bytes
        /cref_shake256_rate_bytes.
apply eq_mkseq => i.
by case (i < shake256_rate_bytes); rewrite cref_shake256_absorb_block_byteE.
qed.

lemma cref_shake256_absorb_state_size input inlen :
  size (cref_shake256_absorb_state input inlen) = fips202_state_bytes.
proof. by rewrite cref_shake256_absorb_stateE
                  shake256_absorb_once_short_state_size. qed.

lemma cref_shake256_absorb_onceE input inlen :
  cref_shake256_absorb_once input inlen =
  shake256_absorb_once input inlen.
proof.
by rewrite /cref_shake256_absorb_once /shake256_absorb_once
           cref_shake256_absorb_stateE.
qed.

lemma cref_load64_laneE input lane :
  cref_load64_lane input (8 * lane) =
  keccak_bytes_to_lane input lane.
proof.
rewrite /cref_load64_lane /keccak_bytes_to_lane.
apply eq_mkseq => bit.
by smt().
qed.

lemma cref_store64_lane_size lane :
  size (cref_store64_lane lane) = 8.
proof. by rewrite /cref_store64_lane size_mkseq. qed.

lemma cref_shake256_absorb_state_lanes_size input inlen :
  size (cref_shake256_absorb_state_lanes input inlen) =
  keccak_state_lanes.
proof.
by rewrite /cref_shake256_absorb_state_lanes keccak_lanes_of_bytes_size.
qed.

lemma cref_shake256_permuted_state_bytesE input inlen :
  cref_shake256_permuted_state_bytes input inlen =
  cref_shake256_absorb_once input inlen.
proof.
by rewrite /cref_shake256_permuted_state_bytes
           /cref_shake256_permuted_state_lanes
           /cref_shake256_absorb_state_lanes
           /cref_shake256_absorb_once
           /fips202_keccak_f1600
           /keccak_f1600_bytes.
qed.

lemma cref_shake256_c_absorb_once_pos input inlen :
  (cref_shake256_c_absorb_once input inlen).`2 =
  cref_shake256_rate_bytes.
proof. by rewrite /cref_shake256_c_absorb_once. qed.

lemma cref_shake256_c_absorb_once_state input inlen :
  (cref_shake256_c_absorb_once input inlen).`1 =
  cref_shake256_absorb_state input inlen.
proof. by rewrite /cref_shake256_c_absorb_once. qed.

lemma cref_shake256_c_squeeze_short_after_absorbE input inlen outlen :
  cref_shake256_c_squeeze_short
    (cref_shake256_c_absorb_once input inlen)
    outlen =
  cref_shake256 input inlen outlen.
proof.
by rewrite /cref_shake256_c_squeeze_short
           /cref_shake256_c_absorb_once
           /cref_shake256
           /cref_shake256_absorb_once.
qed.

lemma cref_shake256_c_api_shortE input inlen outlen :
  cref_shake256_c_api_short input inlen outlen =
  shake256 input inlen outlen.
proof.
by rewrite /cref_shake256_c_api_short
           /cref_shake256_c_squeeze_short
           /cref_shake256_c_absorb_once
           /cref_shake256_rate_bytes
           /shake256
           /shake256_absorb_once
           /cref_shake256_squeeze
           /shake256_squeeze
           cref_shake256_absorb_stateE.
qed.

lemma cref_shake256_squeezeE st outlen :
  cref_shake256_squeeze st outlen = shake256_squeeze st outlen.
proof. by rewrite /cref_shake256_squeeze /shake256_squeeze. qed.

lemma cref_shake256E input inlen outlen :
  cref_shake256 input inlen outlen = shake256 input inlen outlen.
proof.
by rewrite /cref_shake256 /shake256
           cref_shake256_absorb_onceE cref_shake256_squeezeE.
qed.

lemma cref_haetae_keygen_xof_absorb_bytesE :
  cref_haetae_keygen_xof_absorb_bytes = seedbytes.
proof. by rewrite /cref_haetae_keygen_xof_absorb_bytes. qed.

lemma cref_haetae_keygen_xof_squeeze_bytesE :
  cref_haetae_keygen_xof_squeeze_bytes = 2 * seedbytes + crhbytes.
proof. by rewrite /cref_haetae_keygen_xof_squeeze_bytes. qed.

lemma cref_haetae_keygen_xof_domain :
  shake256_absorb_once_short_domain
    (nseq seedbytes 0)
    cref_haetae_keygen_xof_absorb_bytes.
proof.
by rewrite /shake256_absorb_once_short_domain
           cref_haetae_keygen_xof_absorb_bytesE
           shake256_rate_bytesE /seedbytes.
qed.

lemma cref_haetae_keygen_xof_squeeze_lt_rate :
  cref_haetae_keygen_xof_squeeze_bytes < cref_shake256_rate_bytes.
proof.
by rewrite cref_haetae_keygen_xof_squeeze_bytesE
           /cref_shake256_rate_bytes shake256_rate_bytesE
           /seedbytes /crhbytes.
qed.

end HAETAE_FIPS202_CRef.
