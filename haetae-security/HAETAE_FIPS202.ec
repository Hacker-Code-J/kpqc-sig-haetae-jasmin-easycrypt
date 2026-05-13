require import AllCore IntDiv List.
require import HAETAE_Keccak1600.

theory HAETAE_FIPS202.

import HAETAE_Keccak1600.

type fips_byte = int.
type fips202_state = fips_byte list.

op fips202_state_bytes : int = 200.
op shake256_rate_bytes : int = 136.
op shake256_capacity_bytes : int = 64.
op shake256_domain_separator : fips_byte = 31.
op fips202_final_padding_byte : fips_byte = 128.

op fips202_keccak_f1600 (st : fips202_state) : fips202_state =
  keccak_f1600_bytes st.

op shake256_absorb_once_short_domain
   (_ : fips_byte list) (inlen : int) : bool =
  0 <= inlen /\ inlen < shake256_rate_bytes.

op shake256_absorb_once_short_block_byte
   (input : fips_byte list) (inlen i : int) : fips_byte =
  if 0 <= i /\ i < inlen then nth 0 input i
  else if i = inlen /\ i = shake256_rate_bytes - 1 then
    shake256_domain_separator + fips202_final_padding_byte
  else if i = inlen then shake256_domain_separator
  else if i = shake256_rate_bytes - 1 then fips202_final_padding_byte
  else 0.

op shake256_absorb_once_short_state
   (input : fips_byte list) (inlen : int) : fips202_state =
  mkseq
    (fun i =>
       if i < shake256_rate_bytes
       then shake256_absorb_once_short_block_byte input inlen i
       else 0)
    fips202_state_bytes.

op shake256_absorb_once
   (input : fips_byte list) (inlen : int) : fips202_state =
  fips202_keccak_f1600
    (shake256_absorb_once_short_state input inlen).

op shake256_squeeze (st : fips202_state) (outlen : int) : fips_byte list =
  mkseq (fun i => nth 0 st i) outlen.

op shake256
   (input : fips_byte list) (inlen outlen : int) : fips_byte list =
  shake256_squeeze (shake256_absorb_once input inlen) outlen.

lemma fips202_state_bytesE :
  fips202_state_bytes = 200.
proof. by rewrite /fips202_state_bytes. qed.

lemma shake256_rate_bytesE :
  shake256_rate_bytes = 136.
proof. by rewrite /shake256_rate_bytes. qed.

lemma shake256_capacity_bytesE :
  shake256_capacity_bytes = 64.
proof. by rewrite /shake256_capacity_bytes. qed.

lemma shake256_domain_separatorE :
  shake256_domain_separator = 31.
proof. by rewrite /shake256_domain_separator. qed.

lemma fips202_final_padding_byteE :
  fips202_final_padding_byte = 128.
proof. by rewrite /fips202_final_padding_byte. qed.

lemma shake256_rate_capacity_state_bytesE :
  shake256_rate_bytes + shake256_capacity_bytes = fips202_state_bytes.
proof.
by rewrite /shake256_rate_bytes /shake256_capacity_bytes
           /fips202_state_bytes.
qed.

lemma shake256_absorb_once_short_state_size input inlen :
  size (shake256_absorb_once_short_state input inlen) =
  fips202_state_bytes.
proof.
by rewrite /shake256_absorb_once_short_state size_mkseq.
qed.

lemma shake256_squeeze_size st outlen :
  0 <= outlen =>
  size (shake256_squeeze st outlen) = outlen.
proof.
move=> ge0_outlen.
rewrite /shake256_squeeze size_mkseq.
by smt().
qed.

lemma shake256_size input inlen outlen :
  0 <= outlen =>
  size (shake256 input inlen outlen) = outlen.
proof.
move=> ge0_outlen.
by rewrite /shake256 shake256_squeeze_size.
qed.

end HAETAE_FIPS202.
