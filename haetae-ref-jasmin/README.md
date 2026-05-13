# HAETAE Jasmin Variant

This directory contains a buildable HAETAE implementation derived from
`../haetae-ref`.  The production scheme implementation is Jasmin source under
`jasmin/`, assembled from `jasminc` output.  C source files are retained only
for tests, KAT generation, and benchmark harnesses.

The public HAETAE API in `include/api.h` is intentionally small:
`crypto_sign_keypair`, `crypto_sign`, and `crypto_sign_verify`.  `crypto_sign`
is the detached-signature operation paired with `crypto_sign_verify`.  Because
Jasmin x86-64 exports are limited to six register arguments, the signing and
verification wrappers pack pointer/length descriptors and call private Jasmin
descriptor backends.  The keypair API fits the Jasmin export ABI directly.

The current Jasmin entry points are:

- `randombytes_seed32_jazz`
- `keccak_load64_jazz`
- `keccak_store64_jazz`
- `keccak_init_state_jazz`
- `keccakf1600_statepermute_jazz`
- `keccak_finalize_jazz`
- `keccak_absorb_jazz`
- `keccak_squeeze_jazz`
- `keccak_absorb_once_jazz`
- `keccak_squeezeblocks_jazz`
- `fips202_shake128_init_jazz`
- `fips202_shake128_absorb_jazz`
- `fips202_shake128_finalize_jazz`
- `fips202_shake128_squeeze_jazz`
- `fips202_shake128_absorb_once_jazz`
- `fips202_shake128_squeezeblocks_jazz`
- `fips202_shake256_init_jazz`
- `fips202_shake256_absorb_jazz`
- `fips202_shake256_finalize_jazz`
- `fips202_shake256_squeeze_jazz`
- `fips202_shake256_absorb_once_jazz`
- `fips202_shake256_squeezeblocks_jazz`
- `fips202_shake128_jazz`
- `fips202_shake256_jazz`
- `fips202_sha3_256_jazz`
- `fips202_sha3_512_jazz`
- `shake_store_nonce_jazz`
- `fft_init_and_bitrev_jazz`
- `fft_butterfly_jazz`
- `fft_full_jazz`
- `complex_fp_sqabs_jazz`
- `shake128_stream_init_jazz`
- `shake256_stream_init_jazz`
- `shake256_absorb_twice_jazz`
- `shake256_absorb_twice_start_jazz`
- `shake256_absorb_final_jazz`
- `shake256_absorb_thrice_jazz`
- `poly_uniform_jazz`
- `poly_uniform_eta_jazz`
- `polyveck_expand_vecA_jazz`
- `polyvec_expand_eta_jazz`
- `polymatkl_expand_matA_jazz`
- `polymatkm_expand_matA_jazz`
- `poly_ntt_jazz`
- `poly_invntt_jazz`
- `polyvec_ntt_jazz`
- `polyvec_invntt_jazz`
- `poly_basemul_jazz`
- `poly_add_jazz`
- `poly_sub_jazz`
- `poly_double_jazz`
- `poly_double_negate_jazz`
- `poly_frommont_jazz`
- `poly_cneg_jazz`
- `poly_caddq_jazz`
- `poly_cadddq2alpha_m23_jazz`
- `poly_cadddq2alpha_m5_jazz`
- `poly_csubdq2alpha_m23_jazz`
- `poly_csubdq2alpha_m5_jazz`
- `poly_mul_alpha_m23_jazz`
- `poly_mul_alpha_m5_jazz`
- `poly_div2_jazz`
- `polyvec_pointwise_acc_jazz`
- `polyvec_poly_pointwise_jazz`
- `polyvec_sqnorm2_jazz`
- `polyvec_add_jazz`
- `polyvec_sub_jazz`
- `polyvec_reduce2q_jazz`
- `polyvec_freeze_jazz`
- `polyvec_freeze2q_jazz`
- `polyvec_double_jazz`
- `polyvec_double_negate_jazz`
- `polyvec_frommont_jazz`
- `polyvec_cneg_jazz`
- `polyvec_caddq_jazz`
- `polyvec_cadddq2alpha_m23_jazz`
- `polyvec_cadddq2alpha_m5_jazz`
- `polyvec_csubdq2alpha_m23_jazz`
- `polyvec_csubdq2alpha_m5_jazz`
- `polyvec_mul_alpha_m23_jazz`
- `polyvec_mul_alpha_m5_jazz`
- `polyvec_div2_jazz`
- `polymat_pointwise_acc_jazz`
- `polymatkl_double_jazz`
- `polymat_set_first_column_jazz`
- `polyfix_add_jazz`
- `polyfixfix_sub_jazz`
- `polyfix_double_jazz`
- `polyfix_round_jazz`
- `polyfixveclk_sqnorm2_jazz`
- `polyfixveclk_scale_samples_jazz`
- `polyfixveclk_scale_and_check_jazz`
- `polyfixveclk_hyperball_b_jazz`
- `polyfixveclk_sample_hyperball_mode2_jazz`
- `polyfixveclk_sample_hyperball_mode3_jazz`
- `polyfixveclk_sample_hyperball_mode5_jazz`
- `poly_challenge_m23_init_jazz`
- `poly_challenge_m23_frombytes_jazz`
- `poly_challenge_m5_frombytes_jazz`
- `poly_challenge_m23_jazz`
- `poly_challenge_m5_jazz`
- `fixpoint_add_jazz`
- `fixpoint_square_jazz`
- `fixpoint_mul_jazz`
- `fixpoint_mul_rnd13_jazz`
- `fixpoint_mul_high_jazz`
- `fixpoint_half_round_jazz`
- `fixpoint_newton_invsqrt_jazz`
- `poly_lsb_jazz`
- `poly_compose_jazz`
- `poly_mismatch_jazz`
- `polyvec_compose_jazz`
- `poly_highbits_jazz`
- `poly_lowbits_jazz`
- `polyvec_highbits_jazz`
- `polyvec_lowbits_jazz`
- `polyvec_decompose_z1_jazz`
- `poly_highbits_hint_m23_jazz`
- `poly_highbits_hint_m5_jazz`
- `polyvec_highbits_hint_m23_jazz`
- `polyvec_highbits_hint_m5_jazz`
- `poly_decompose_vk_jazz`
- `polyvec_decompose_vk_jazz`
- `poly_fromcrt_jazz`
- `poly_fromcrt0_jazz`
- `polyveck_poly_fromcrt_jazz`
- `poly_reduce2q_jazz`
- `poly_freeze_jazz`
- `poly_freeze2q_jazz`
- `poly_decomposed_pack_jazz`
- `poly_decomposed_unpack_jazz`
- `pack_poly_lsb_jazz`
- `pack_poly_eta_jazz`
- `unpack_poly_eta_jazz`
- `pack_poly2_eta_jazz`
- `unpack_poly2_eta_jazz`
- `pack_poly_q_m23_jazz`
- `unpack_poly_q_m23_jazz`
- `pack_poly_q_m5_jazz`
- `unpack_poly_q_m5_jazz`
- `pack_poly_highbits_m23_jazz`
- `pack_poly_highbits_m5_jazz`
- `pack_vec_highbits_m23_jazz`
- `pack_vec_highbits_m5_jazz`
- `pack_vk_m23_jazz`
- `pack_vk_m5_jazz`
- `unpack_vk_m23_jazz`
- `unpack_vk_m5_jazz`
- `unpack_vk_m23_full_jazz`
- `unpack_vk_m5_full_jazz`
- `pack_sk_mode2_jazz`
- `pack_sk_mode3_jazz`
- `pack_sk_mode5_jazz`
- `unpack_sk_mode2_jazz`
- `unpack_sk_mode3_jazz`
- `unpack_sk_mode5_jazz`
- `unpack_sk_mode2_full_jazz`
- `unpack_sk_mode3_full_jazz`
- `unpack_sk_mode5_full_jazz`
- `pack_sig_prefix_jazz`
- `unpack_sig_prefix_jazz`
- `pack_sig_suffix_jazz`
- `pack_sig_size_offsets_jazz`
- `pack_sig_finish_jazz`
- `pack_sig_mode2_full_jazz`
- `pack_sig_mode3_full_jazz`
- `pack_sig_mode5_full_jazz`
- `unpack_sig_size_offsets_jazz`
- `unpack_sig_finish_jazz`
- `unpack_sig_mode2_full_jazz`
- `unpack_sig_mode3_full_jazz`
- `unpack_sig_mode5_full_jazz`
- `sig_zero_padding_nonzero_jazz`
- `rej_uniform_jazz`
- `rej_eta_jazz`
- `sample_gauss16_jazz`
- `approx_exp_jazz`
- `sample_gauss_sigma76_jazz`
- `sample_gauss_jazz`
- `sample_gauss_N_copy_signs_jazz`
- `sample_gauss_N_carry_jazz`
- `sample_gauss_N_full_jazz`
- `sign_prepare_pre_jazz`
- `sign_move_message_to_sm_jazz`
- `sign_open_copy_message_jazz`
- `sign_open_zero_message_jazz`
- `keypair_expand_seedbuf_jazz`
- `keypair_m23_matrix_jazz`
- `keypair_m5_matrix_jazz`
- `keypair_copy_ntt_jazz`
- `sign_expand_seedbuf_jazz`
- `sign_round_lk_copy0_mode2_jazz`
- `sign_round_lk_copy0_mode3_jazz`
- `sign_round_lk_copy0_mode5_jazz`
- `sign_prepare_cs_jazz`
- `sign_compute_cs1_tail_jazz`
- `sign_compute_cs2_jazz`
- `sign_challenge_mode2_jazz`
- `sign_challenge_mode3_jazz`
- `sign_challenge_mode5_jazz`
- `sign_verify_prepare_z1_wprime_jazz`
- `sign_verify_matrix_ntt_acc_jazz`
- `sign_verify_crt_freeze_jazz`
- `sign_verify_recover_w_z2_m23_jazz`
- `sign_verify_recover_w_z2_m5_jazz`
- `sign_verify_norm_reject_jazz`
- `sign_verify_tail_mode2_jazz`
- `sign_verify_tail_mode3_jazz`
- `sign_verify_tail_mode5_jazz`
- `sign_verify_internal_mode2_jazz`
- `sign_verify_internal_mode3_jazz`
- `sign_verify_internal_mode5_jazz`
- `sign_make_hint_m23_jazz`
- `sign_make_hint_m5_jazz`
- `keypair_finalize_m23_jazz`
- `keypair_finalize_m5_jazz`
- `crypto_sign_keypair_mode2_jazz`
- `crypto_sign_keypair_mode3_jazz`
- `crypto_sign_keypair_mode5_jazz`
- `sign_add_cs_and_check_jazz`
- `sign_add_double_z2rnd_jazz`
- `sk_singular_value_accumulate_fft_sqabs_jazz`
- `sk_singular_value_finish_m2_jazz`
- `sk_singular_value_finish_m3_jazz`
- `sk_singular_value_finish_m5_jazz`
- `sk_singular_value_full_m2_jazz`
- `sk_singular_value_full_m3_jazz`
- `sk_singular_value_full_m5_jazz`
- `encode_h_prepare_jazz`
- `encode_hb_z1_prepare_jazz`
- `encode_h_mode2_full_jazz`
- `encode_h_mode3_full_jazz`
- `encode_h_mode5_full_jazz`
- `encode_hb_z1_mode2_full_jazz`
- `encode_hb_z1_mode3_full_jazz`
- `encode_hb_z1_mode5_full_jazz`
- `decode_h_mode2_full_jazz`
- `decode_h_mode3_full_jazz`
- `decode_h_mode5_full_jazz`
- `decode_hb_z1_mode2_full_jazz`
- `decode_hb_z1_mode3_full_jazz`
- `decode_hb_z1_mode5_full_jazz`
- `rans_encode_jazz`
- `rans_decode_jazz`
- `decode_h_apply_jazz`
- `decode_hb_z1_apply_jazz`

The top-level public API is:

- `crypto_sign_keypair`
- `crypto_sign`
- `crypto_sign_verify`

Jasmin descriptor backends remain available to the test and KAT harnesses for
deterministic `.req`/`.fax` validation, but they are not part of the public
header API.

Randomized keypair and signing call Jasmin `#randombytes`, which resolves to
an application-provided `__jasmin_syscall_randombytes__`.  The test and KAT
harnesses provide that symbol; production users should provide their own RNG
binding.

## Build

```sh
make all
```

This builds all three parameter sets:

- `build/mode2/lib/libhaetae-mode2-jazz.so`
- `build/mode3/lib/libhaetae-mode3-jazz.so`
- `build/mode5/lib/libhaetae-mode5-jazz.so`

## Test

```sh
make test
```

The test target runs:

- the HAETAE sign/verify smoke test for modes 2, 3, and 5
- deterministic KAT generation for modes 2, 3, and 5
- byte-for-byte diffs against `kat/PQCsignKAT_haetae_*.req` and
  `kat/PQCsignKAT_haetae_*.fax`

To run only the deterministic KAT comparison, use:

```sh
make kat
```

That target requires OpenSSL's `libcrypto`, matching the reference KAT driver.
