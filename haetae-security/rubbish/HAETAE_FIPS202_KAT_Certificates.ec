require import AllCore IntDiv List.
require import HAETAE_FIPS202 HAETAE_FIPS202_CRef.
require import HAETAE_FIPS202_TestVectors HAETAE_Keccak1600.

theory HAETAE_FIPS202_KAT_Certificates.

import HAETAE_FIPS202.
import HAETAE_FIPS202_CRef.
import HAETAE_FIPS202_TestVectors.
import HAETAE_Keccak1600.

op kat_round_constant (i : int) : int =
  nth 0 keccak_round_constants i.

op shake256_empty_padded_state_cert : fips202_state =
  mkseq (fun i => if i = 0 then 31 else if i = 135 then 128 else 0) 200.

op shake256_empty_round00_lanes_cert : keccak_state =
  keccak_lanes_of_bytes shake256_empty_padded_state_cert.
op shake256_empty_round01_lanes_cert : keccak_state =
  keccak_round shake256_empty_round00_lanes_cert
    (keccak_lane_of_int (kat_round_constant 0)).
op shake256_empty_round02_lanes_cert : keccak_state =
  keccak_round shake256_empty_round01_lanes_cert
    (keccak_lane_of_int (kat_round_constant 1)).
op shake256_empty_round03_lanes_cert : keccak_state =
  keccak_round shake256_empty_round02_lanes_cert
    (keccak_lane_of_int (kat_round_constant 2)).
op shake256_empty_round04_lanes_cert : keccak_state =
  keccak_round shake256_empty_round03_lanes_cert
    (keccak_lane_of_int (kat_round_constant 3)).
op shake256_empty_round05_lanes_cert : keccak_state =
  keccak_round shake256_empty_round04_lanes_cert
    (keccak_lane_of_int (kat_round_constant 4)).
op shake256_empty_round06_lanes_cert : keccak_state =
  keccak_round shake256_empty_round05_lanes_cert
    (keccak_lane_of_int (kat_round_constant 5)).
op shake256_empty_round07_lanes_cert : keccak_state =
  keccak_round shake256_empty_round06_lanes_cert
    (keccak_lane_of_int (kat_round_constant 6)).
op shake256_empty_round08_lanes_cert : keccak_state =
  keccak_round shake256_empty_round07_lanes_cert
    (keccak_lane_of_int (kat_round_constant 7)).
op shake256_empty_round09_lanes_cert : keccak_state =
  keccak_round shake256_empty_round08_lanes_cert
    (keccak_lane_of_int (kat_round_constant 8)).
op shake256_empty_round10_lanes_cert : keccak_state =
  keccak_round shake256_empty_round09_lanes_cert
    (keccak_lane_of_int (kat_round_constant 9)).
op shake256_empty_round11_lanes_cert : keccak_state =
  keccak_round shake256_empty_round10_lanes_cert
    (keccak_lane_of_int (kat_round_constant 10)).
op shake256_empty_round12_lanes_cert : keccak_state =
  keccak_round shake256_empty_round11_lanes_cert
    (keccak_lane_of_int (kat_round_constant 11)).
op shake256_empty_round13_lanes_cert : keccak_state =
  keccak_round shake256_empty_round12_lanes_cert
    (keccak_lane_of_int (kat_round_constant 12)).
op shake256_empty_round14_lanes_cert : keccak_state =
  keccak_round shake256_empty_round13_lanes_cert
    (keccak_lane_of_int (kat_round_constant 13)).
op shake256_empty_round15_lanes_cert : keccak_state =
  keccak_round shake256_empty_round14_lanes_cert
    (keccak_lane_of_int (kat_round_constant 14)).
op shake256_empty_round16_lanes_cert : keccak_state =
  keccak_round shake256_empty_round15_lanes_cert
    (keccak_lane_of_int (kat_round_constant 15)).
op shake256_empty_round17_lanes_cert : keccak_state =
  keccak_round shake256_empty_round16_lanes_cert
    (keccak_lane_of_int (kat_round_constant 16)).
op shake256_empty_round18_lanes_cert : keccak_state =
  keccak_round shake256_empty_round17_lanes_cert
    (keccak_lane_of_int (kat_round_constant 17)).
op shake256_empty_round19_lanes_cert : keccak_state =
  keccak_round shake256_empty_round18_lanes_cert
    (keccak_lane_of_int (kat_round_constant 18)).
op shake256_empty_round20_lanes_cert : keccak_state =
  keccak_round shake256_empty_round19_lanes_cert
    (keccak_lane_of_int (kat_round_constant 19)).
op shake256_empty_round21_lanes_cert : keccak_state =
  keccak_round shake256_empty_round20_lanes_cert
    (keccak_lane_of_int (kat_round_constant 20)).
op shake256_empty_round22_lanes_cert : keccak_state =
  keccak_round shake256_empty_round21_lanes_cert
    (keccak_lane_of_int (kat_round_constant 21)).
op shake256_empty_round23_lanes_cert : keccak_state =
  keccak_round shake256_empty_round22_lanes_cert
    (keccak_lane_of_int (kat_round_constant 22)).
op shake256_empty_round24_lanes_cert : keccak_state =
  keccak_round shake256_empty_round23_lanes_cert
    (keccak_lane_of_int (kat_round_constant 23)).

op shake256_empty_round24_bytes_cert : fips202_state =
  keccak_bytes_of_lanes shake256_empty_round24_lanes_cert.

op shake256_empty_64_certificate_output : fips_byte list =
  mkseq (fun i => nth 0 shake256_empty_round24_bytes_cert i) 64.

op shake256_empty_64_certificate_known_answer : bool =
  shake256_empty_64_certificate_output = shake256_empty_64_expected.

lemma kat_round_constant_size :
  size keccak_round_constants = 24.
proof. by apply keccak_round_constants_size. qed.

lemma shake256_empty_padded_state_cert_size :
  size shake256_empty_padded_state_cert = fips202_state_bytes.
proof.
by rewrite /shake256_empty_padded_state_cert size_mkseq
           fips202_state_bytesE.
qed.

lemma shake256_empty_padded_state_certE :
  shake256_empty_padded_state_cert =
  cref_shake256_absorb_state shake256_empty_input 0.
proof.
rewrite /shake256_empty_padded_state_cert
        /cref_shake256_absorb_state
        /shake256_empty_input
        /cref_shake256_state_bytes
        /cref_shake256_rate_bytes.
apply eq_mkseq => i.
rewrite /cref_shake256_absorb_block_byte
        /cref_shake256_absorb_data_byte
        /cref_shake256_absorb_padding_byte
        /cref_shake256_domain_separator
        /cref_shake256_final_padding_byte
        /shake256_domain_separator
        /fips202_final_padding_byte.
by smt().
qed.

lemma shake256_empty_round00_lanes_certE :
  shake256_empty_round00_lanes_cert =
  cref_shake256_absorb_state_lanes shake256_empty_input 0.
proof.
by rewrite /shake256_empty_round00_lanes_cert
           /cref_shake256_absorb_state_lanes
           shake256_empty_padded_state_certE.
qed.

lemma shake256_empty_round01_lanes_cert_step :
  shake256_empty_round01_lanes_cert =
  keccak_round shake256_empty_round00_lanes_cert
    (keccak_lane_of_int (kat_round_constant 0)).
proof. by rewrite /shake256_empty_round01_lanes_cert. qed.

lemma shake256_empty_round02_lanes_cert_step :
  shake256_empty_round02_lanes_cert =
  keccak_round shake256_empty_round01_lanes_cert
    (keccak_lane_of_int (kat_round_constant 1)).
proof. by rewrite /shake256_empty_round02_lanes_cert. qed.

lemma shake256_empty_round03_lanes_cert_step :
  shake256_empty_round03_lanes_cert =
  keccak_round shake256_empty_round02_lanes_cert
    (keccak_lane_of_int (kat_round_constant 2)).
proof. by rewrite /shake256_empty_round03_lanes_cert. qed.

lemma shake256_empty_round04_lanes_cert_step :
  shake256_empty_round04_lanes_cert =
  keccak_round shake256_empty_round03_lanes_cert
    (keccak_lane_of_int (kat_round_constant 3)).
proof. by rewrite /shake256_empty_round04_lanes_cert. qed.

lemma shake256_empty_round05_lanes_cert_step :
  shake256_empty_round05_lanes_cert =
  keccak_round shake256_empty_round04_lanes_cert
    (keccak_lane_of_int (kat_round_constant 4)).
proof. by rewrite /shake256_empty_round05_lanes_cert. qed.

lemma shake256_empty_round06_lanes_cert_step :
  shake256_empty_round06_lanes_cert =
  keccak_round shake256_empty_round05_lanes_cert
    (keccak_lane_of_int (kat_round_constant 5)).
proof. by rewrite /shake256_empty_round06_lanes_cert. qed.

lemma shake256_empty_round07_lanes_cert_step :
  shake256_empty_round07_lanes_cert =
  keccak_round shake256_empty_round06_lanes_cert
    (keccak_lane_of_int (kat_round_constant 6)).
proof. by rewrite /shake256_empty_round07_lanes_cert. qed.

lemma shake256_empty_round08_lanes_cert_step :
  shake256_empty_round08_lanes_cert =
  keccak_round shake256_empty_round07_lanes_cert
    (keccak_lane_of_int (kat_round_constant 7)).
proof. by rewrite /shake256_empty_round08_lanes_cert. qed.

lemma shake256_empty_round09_lanes_cert_step :
  shake256_empty_round09_lanes_cert =
  keccak_round shake256_empty_round08_lanes_cert
    (keccak_lane_of_int (kat_round_constant 8)).
proof. by rewrite /shake256_empty_round09_lanes_cert. qed.

lemma shake256_empty_round10_lanes_cert_step :
  shake256_empty_round10_lanes_cert =
  keccak_round shake256_empty_round09_lanes_cert
    (keccak_lane_of_int (kat_round_constant 9)).
proof. by rewrite /shake256_empty_round10_lanes_cert. qed.

lemma shake256_empty_round11_lanes_cert_step :
  shake256_empty_round11_lanes_cert =
  keccak_round shake256_empty_round10_lanes_cert
    (keccak_lane_of_int (kat_round_constant 10)).
proof. by rewrite /shake256_empty_round11_lanes_cert. qed.

lemma shake256_empty_round12_lanes_cert_step :
  shake256_empty_round12_lanes_cert =
  keccak_round shake256_empty_round11_lanes_cert
    (keccak_lane_of_int (kat_round_constant 11)).
proof. by rewrite /shake256_empty_round12_lanes_cert. qed.

lemma shake256_empty_round13_lanes_cert_step :
  shake256_empty_round13_lanes_cert =
  keccak_round shake256_empty_round12_lanes_cert
    (keccak_lane_of_int (kat_round_constant 12)).
proof. by rewrite /shake256_empty_round13_lanes_cert. qed.

lemma shake256_empty_round14_lanes_cert_step :
  shake256_empty_round14_lanes_cert =
  keccak_round shake256_empty_round13_lanes_cert
    (keccak_lane_of_int (kat_round_constant 13)).
proof. by rewrite /shake256_empty_round14_lanes_cert. qed.

lemma shake256_empty_round15_lanes_cert_step :
  shake256_empty_round15_lanes_cert =
  keccak_round shake256_empty_round14_lanes_cert
    (keccak_lane_of_int (kat_round_constant 14)).
proof. by rewrite /shake256_empty_round15_lanes_cert. qed.

lemma shake256_empty_round16_lanes_cert_step :
  shake256_empty_round16_lanes_cert =
  keccak_round shake256_empty_round15_lanes_cert
    (keccak_lane_of_int (kat_round_constant 15)).
proof. by rewrite /shake256_empty_round16_lanes_cert. qed.

lemma shake256_empty_round17_lanes_cert_step :
  shake256_empty_round17_lanes_cert =
  keccak_round shake256_empty_round16_lanes_cert
    (keccak_lane_of_int (kat_round_constant 16)).
proof. by rewrite /shake256_empty_round17_lanes_cert. qed.

lemma shake256_empty_round18_lanes_cert_step :
  shake256_empty_round18_lanes_cert =
  keccak_round shake256_empty_round17_lanes_cert
    (keccak_lane_of_int (kat_round_constant 17)).
proof. by rewrite /shake256_empty_round18_lanes_cert. qed.

lemma shake256_empty_round19_lanes_cert_step :
  shake256_empty_round19_lanes_cert =
  keccak_round shake256_empty_round18_lanes_cert
    (keccak_lane_of_int (kat_round_constant 18)).
proof. by rewrite /shake256_empty_round19_lanes_cert. qed.

lemma shake256_empty_round20_lanes_cert_step :
  shake256_empty_round20_lanes_cert =
  keccak_round shake256_empty_round19_lanes_cert
    (keccak_lane_of_int (kat_round_constant 19)).
proof. by rewrite /shake256_empty_round20_lanes_cert. qed.

lemma shake256_empty_round21_lanes_cert_step :
  shake256_empty_round21_lanes_cert =
  keccak_round shake256_empty_round20_lanes_cert
    (keccak_lane_of_int (kat_round_constant 20)).
proof. by rewrite /shake256_empty_round21_lanes_cert. qed.

lemma shake256_empty_round22_lanes_cert_step :
  shake256_empty_round22_lanes_cert =
  keccak_round shake256_empty_round21_lanes_cert
    (keccak_lane_of_int (kat_round_constant 21)).
proof. by rewrite /shake256_empty_round22_lanes_cert. qed.

lemma shake256_empty_round23_lanes_cert_step :
  shake256_empty_round23_lanes_cert =
  keccak_round shake256_empty_round22_lanes_cert
    (keccak_lane_of_int (kat_round_constant 22)).
proof. by rewrite /shake256_empty_round23_lanes_cert. qed.

lemma shake256_empty_round24_lanes_cert_step :
  shake256_empty_round24_lanes_cert =
  keccak_round shake256_empty_round23_lanes_cert
    (keccak_lane_of_int (kat_round_constant 23)).
proof. by rewrite /shake256_empty_round24_lanes_cert. qed.

lemma shake256_empty_round24_lanes_certE :
  shake256_empty_round24_lanes_cert =
  keccak_f1600_lanes shake256_empty_round00_lanes_cert.
proof.
by rewrite /shake256_empty_round24_lanes_cert
           /shake256_empty_round23_lanes_cert
           /shake256_empty_round22_lanes_cert
           /shake256_empty_round21_lanes_cert
           /shake256_empty_round20_lanes_cert
           /shake256_empty_round19_lanes_cert
           /shake256_empty_round18_lanes_cert
           /shake256_empty_round17_lanes_cert
           /shake256_empty_round16_lanes_cert
           /shake256_empty_round15_lanes_cert
           /shake256_empty_round14_lanes_cert
           /shake256_empty_round13_lanes_cert
           /shake256_empty_round12_lanes_cert
           /shake256_empty_round11_lanes_cert
           /shake256_empty_round10_lanes_cert
           /shake256_empty_round09_lanes_cert
           /shake256_empty_round08_lanes_cert
           /shake256_empty_round07_lanes_cert
           /shake256_empty_round06_lanes_cert
           /shake256_empty_round05_lanes_cert
           /shake256_empty_round04_lanes_cert
           /shake256_empty_round03_lanes_cert
           /shake256_empty_round02_lanes_cert
           /shake256_empty_round01_lanes_cert
           /keccak_f1600_lanes
           /kat_round_constant
           /keccak_round_constants.
qed.

lemma shake256_empty_round24_bytes_certE :
  shake256_empty_round24_bytes_cert =
  fips202_keccak_f1600 shake256_empty_padded_state_cert.
proof.
by rewrite /shake256_empty_round24_bytes_cert
           /fips202_keccak_f1600
           /keccak_f1600_bytes
           shake256_empty_round24_lanes_certE
           /shake256_empty_round00_lanes_cert.
qed.

lemma shake256_empty_64_certificate_output_size :
  size shake256_empty_64_certificate_output = 64.
proof.
by rewrite /shake256_empty_64_certificate_output size_mkseq.
qed.

lemma shake256_empty_64_certificate_known_answer_from_nth :
  (forall i, 0 <= i < 64 =>
     nth 0 shake256_empty_64_certificate_output i =
     nth 0 shake256_empty_64_expected i) =>
  shake256_empty_64_certificate_known_answer.
proof.
move=> H.
rewrite /shake256_empty_64_certificate_known_answer.
apply (eq_from_nth 0).
+ by rewrite shake256_empty_64_certificate_output_size
             shake256_empty_64_expected_size.
move=> i i_range.
by apply H; smt(shake256_empty_64_certificate_output_size).
qed.

lemma shake256_empty_64_certificate_outputE :
  shake256_empty_64_certificate_output =
  shake256_empty_64_actual.
proof.
by rewrite /shake256_empty_64_certificate_output
           /shake256_empty_64_actual
           /shake256
           /shake256_squeeze
           /shake256_absorb_once
           /fips202_keccak_f1600
           /keccak_f1600_bytes
           /shake256_empty_round24_bytes_cert
           shake256_empty_round24_lanes_certE
           /shake256_empty_round00_lanes_cert
           shake256_empty_padded_state_certE
           cref_shake256_absorb_stateE.
qed.

lemma shake256_empty_64_known_answer_certificateE :
  shake256_empty_64_known_answer =
  shake256_empty_64_certificate_known_answer.
proof.
by rewrite /shake256_empty_64_known_answer
           /shake256_empty_64_certificate_known_answer
           shake256_empty_64_certificate_outputE.
qed.

lemma shake256_empty_64_known_answer_from_certificate_nth :
  (forall i, 0 <= i < 64 =>
     nth 0 shake256_empty_64_certificate_output i =
     nth 0 shake256_empty_64_expected i) =>
  shake256_empty_64_known_answer.
proof.
move=> H.
rewrite shake256_empty_64_known_answer_certificateE.
by apply shake256_empty_64_certificate_known_answer_from_nth.
qed.

end HAETAE_FIPS202_KAT_Certificates.
