# 검증 범위와 남은 의무

이 문서는 함수별 정리의 범위를 기록한다. 추출물의 로딩 성공, KAT 성공,
구성요소 정리와 전체 API 정확성을 구분한다.

## 현재 정리

| 정리 파일 | 대표 정리 | 정확한 범위 |
| --- | --- | --- |
| [SamplerConstants](proofs/SamplerConstants.ec) | `cdt83_hi_matches_reference`, `cdt83_lo_matches_reference`, `approx_exp_matches_reference` | 고정된 C에서 독립 생성한 CDT·다항식 상수와 Jasmin 명세 연결 |
| [CDTCorrectness](proofs/CDTCorrectness.ec) | `sample_gauss83_jazz_total`, `sample_gauss83_max83_total` | 입력 정수보다 작은 166개 임계값의 개수; 범위와 최대 입력 166; 확률 1 종료·결과 |
| [CDTTermination](proofs/CDTTermination.ec) | `sample_gauss83_ll` | 실제 두 bounded loop의 종료성 |
| [CDTDistribution](proofs/CDTDistribution.ec) | `cdt_distribution_mass`, `uniform_cdt_law` | 균등 정수 입력에서 strict 임계값 비교의 정확한 출력 확률: 각 구간 길이/M; 경계 +1, support, 종료 |
| [CDTDistributionBridge](proofs/CDTDistributionBridge.ec) | `uniform83_jasmin_law`, `uniform83_jasmin_mass`, `uniform83_jasmin_endpoint` | 균등 83비트 입력을 실제 Jasmin CDT에 전달한 확률 실험; 정확한 분포·종료, support 0…166, Pr[166]=2^-83 |
| [HalfGaussianProperties](proofs/HalfGaussianProperties.ec) | `hg16_pmf_sum`, `hg16_distr_ll`, `hg16_normalizer_truncation256` | 구현과 독립인 rho(k)=exp(-k²/512), k≥0의 무한 정규화·총확률 1·꼬리 상한 |
| [ExpIntervalCorrectness](proofs/ExpIntervalCorrectness.ec) / [CDTGaussianEnclosure](proofs/CDTGaussianEnclosure.ec) | `ei_square_q_sound`, `ei_weights_sound`, `gi_normalizer_interval`, `gi_pmf_interval` | 실제 실수 지수함수의 유리수 구간과 외향 반올림 인증서의 건전성; 무한 정규화 분모와 각 목표 확률의 수치 구간; 구체적 수치 의무는 검사된 정수 인증서로 해소 |
| [CDTGaussianApproximation](proofs/CDTGaussianApproximation.ec) | `cdt83_half_gaussian_statistical_distance`, `uniform83_jasmin_half_gaussian_error` | 실제 Jasmin CDT의 균등 83비트 입력 실험과 공식 목표인 비음수 Gaussian(σ=16)의 통계적 거리 <2^-78; 임의 출력 집합에 대한 확률 차이도 같은 상한 |
| [FixedPointCorrectness](proofs/FixedPointCorrectness.ec) | `smulh48_jazz_total_correct`, `smulh48_jazz_signed_correct`, `approx_exp_jazz_reference_correct` | 모든 word 입력의 올림 결과 modulo 2^64; signed 결과는 명시적 fit 전제; C-derived 10차 word Horner 계산 |
| [SigmaExpInputBounds](proofs/SigmaExpInputBounds.ec) | `sigma_exp_argument_bound`, `sigma_exp_argument_two_thirds` | 모든 26바이트 입력에서 실제 지수 인자 uint(xi)≤183103063064576, 3·uint(xi)≤2·2^48; 차감·병합·반올림 범위 의무 해소 |
| [ApproxExpWordCorrectness](proofs/ApproxExpWordCorrectness.ec) | `ae_intermediate_signed64`, `ae_rounding_error3`, `ae_sigma_approx_exp_total` | 정수 ceil-Horner와 실제 word 실행 연결; 모든 Horner prefix·올림 곱셈 결과의 signed64 적합성, 최종 unsigned 해석; 다항식 대비 올림 오차 0…3/2^48 |
| [Bernstein10Correctness](proofs/Bernstein10Correctness.ec) / [ApproxExpCertificateChecks](proofs/ApproxExpCertificateChecks.ec) | `bernstein10_checked_nonnegative`, `aec_upper_0_identity` 등 | 정수 인증서의 기저 변환·부호와 실제 계수 다항식의 6개 구간 부등식; 66개 제어 계수 검사 |
| [ExponentialGridComparison](proofs/ExponentialGridComparison.ec) / [ApproxExpPolynomialBound](proofs/ApproxExpPolynomialBound.ec) | `eg_exp_grid_abs`, `approx_exp_polynomial_error` | 입력 정수 격자에서 실제 계수 다항식과 exp(-x/2^48)의 오차≤24/2^48; 분석적 점화 조건을 인증서로 해소 |
| [ApproxExpNumericalCorrectness](proofs/ApproxExpNumericalCorrectness.ec) | `approx_exp_signer_numerical_total`, `sigma76_approx_exp_numerical_total` | 실제 Jasmin의 정규화 출력과 실수 지수함수 사이 절대오차≤27/2^48<2^-43 및 종료; 모든 sigma76 입력에서는 별도 범위·fit 전제 없음 |
| [Rejection48Correctness](proofs/Rejection48Correctness.ec) / [SigmaRejection48Bridge](proofs/SigmaRejection48Bridge.ec) | `rejection48_word_probability`, `sigma_rejection48_actual_probability` | 균등 48비트 거부 입력의 정확한 even 비교·포화·실제 rounded-zero 확률; 실제 sigma 프로시저 호출과 연결 |
| [SigmaExpAcceptanceCorrectness](proofs/SigmaExpAcceptanceCorrectness.ec) | `sigma_exp_acceptance_error`, `sigma_exp_acceptance_error_strict` | 후보 바이트를 고정한 실제 sigma 호출의 승인 확률과 α(rounded)·exp(-uint(xi)/2^48)의 차이≤α·28/2^48<2^-43; 48비트 거부 입력의 균등성은 실험에 명시 |
| [SigmaSquareExact](proofs/SigmaSquareExact.ec) / [SigmaRawExponentCorrectness](proofs/SigmaRawExponentCorrectness.ec) | `sigma_square_word_exact`, `sigma_raw_exponent_exact`, `sigma_raw_exponent_error` | 실제 square limbs의 정수 의미와 모든 26바이트 입력에서 xi=floor((y(y+2^73x)+2^104)/2^105); 반올림 전 지수 대비 정규화 오차≤2^-49 |
| [SigmaRawDensityIdentity](proofs/SigmaRawDensityIdentity.ec) | `sr_gaussian_weight_identity`, `sr_gaussian_density_ratio` | 독립적인 비음수 Gaussian σ=16의 비정규화 가중치와 exp(-E)의 곱이 Z=y+2^72x의 σ=2^76 Gaussian 비정규화 가중치와 일치 |
| [SigmaRawZeroCorrectness](proofs/SigmaRawZeroCorrectness.ec) / [SigmaRawNoiseSpec](theories/SigmaRawNoiseSpec.ec) | `sr_zero_tests_differ`, `sr_zero_factor_difference`, `sr_noise_mismatch_probability` | rounded-zero와 raw-zero가 달라지는 조건은 x=0·1≤y<32768; 균등 72비트 잡음의 예외 확률과 최대 반 보정 효과<2^-58 |
| [SigmaRawAcceptanceCorrectness](proofs/SigmaRawAcceptanceCorrectness.ec) | `sr_actual_acceptance_error`, `sr_actual_acceptance_regular` | 고정 후보의 실제 승인 확률과 raw Gaussian 수락식의 차이≤57/(2·2^48)+예외 지시함수/2; 예외 밖에서는 <2^-43 |
| [ExponentialLipschitz](proofs/ExponentialLipschitz.ec) / [FiniteExpectationError](proofs/FiniteExpectationError.ec) | `exp_neg_lipschitz`, `finite_expectation_error` | 비음수 실수에서 지수함수 오차 전달; 유한 분포의 점별 오차·예외 질량을 평균 오차로 합성 |
| [SigmaNoise72Bridge](proofs/SigmaNoise72Bridge.ec) / [SigmaRawAverageCorrectness](proofs/SigmaRawAverageCorrectness.ec) | `sigma_noise72_actual_probability`, `sr_average_acceptance_error_strict` | CDT 바이트 고정·독립 균등 72비트 잡음과 48비트 거부 입력을 실제 sigma에 전달; raw Gaussian 수락식의 평균과 승인 확률 차이<29/2^48<2^-43 |
| [SigmaCorrectness](proofs/SigmaCorrectness.ec) | `sigma76_regs_total_correct`, `sigma76_jazz_total_correct` | 모든 26바이트 입력의 `(rounded, square_low, square_high, accepted)`가 pure word 명세와 일치하며 종료 |
| [SigmaRoundingCorrectness](proofs/SigmaRoundingCorrectness.ec) | `sigma76_spec_rounding`, `sigma76_regs_rounding_correct`, `sigma76_jazz_rounding_correct` | 실제 rounded 출력과 정수 반올림식 일치, byte 조립·shift·최종 합의 무래핑, 최대 CDT 값 166 포함 |
| [GaussianConsumerCorrectness](proofs/GaussianConsumerCorrectness.ec) | `sample_gauss_jazz_bounded_total`, `sample_gauss_jazz_normalized_total` | 요청 `n≤512`, 입력 byte 수 `b≤8192`일 때 승인 수 `c≤n`, `26c≤b`, 요청 범위 밖 출력 보존; 하위 제곱합 limb의 `[0,2^48)` 범위; 유한 종료 |
| [GaussianTraceCorrectness](proofs/GaussianTraceCorrectness.ec) | `sample_gauss_jazz_trace_total_correct`, `sample_gauss_jazz_packed_trace_total` | 실제 유한 소비기의 전체 반환 튜플이 26바이트 후보에 대한 명세 fold와 일치; 요청 도달 시 정지, 거부 후보의 임시 쓰기·dummy 생략·word 제곱합 포함 |
| [GaussianTraceProperties](proofs/GaussianTraceProperties.ec) | `gauss_trace_prefix_count_exact`, `gauss_trace_prefix_accepted_sequence`, `gauss_trace_prefix_full_stable` | 승인 비트로 filter한 후보 중 앞 `n`개의 개수와 순서, 요청 개수 도달 후 fold 불변 |
| [SigmaSquareBounds](proofs/SigmaSquareBounds.ec) | `sigma76_square_high_bound` | 모든 26바이트 입력에서 실제 square-high의 unsigned 값 `<2^38`; 실수 제곱과의 오차 정리는 아님 |
| [GaussianAccumulatorCorrectness](proofs/GaussianAccumulatorCorrectness.ec) | `gauss_trace_prefix_uint_sums`, `gauss_trace_result_canonical_both_exact` | 각 raw limb의 독립적인 mod `2^64` 합; 초기 두 limb가 각각 `<2^48`, `n≤512`이면 최종 `low + 2^48×high`가 승인 후보의 limb 합과 정수로 일치 |
| [GaussianOffsetBridge](proofs/GaussianOffsetBridge.ec) | `sample_gauss_at_trace_total_correct` | 실제 signer `__sample_gauss_at`과 입력·출력 window 명세의 정확한 튜플 동치·종료; `bo+b≤8192`, `oo+n≤4096`; 요청 영역 밖 보존 |
| [GaussianSequenceCorrectness](proofs/GaussianSequenceCorrectness.ec) | `sample_gauss_jazz_sequence_total`, `sample_gauss_jazz_accumulator_exact_total`, `sample_gauss_at_sequence_total` | 공개 유한 소비기와 실제 signer offset 소비기의 승인 개수·저장된 승인 순서, 공개 소비기의 정확한 정수 제곱합 |
| [GaussianValueCorrectness](proofs/GaussianValueCorrectness.ec) | `sample_gauss_at_value_total` | 실제 signer offset 소비기의 반환 square 버퍼에 정수 합 정리를 전달; 초기 두 limb `<2^48`, 요청 `n≤512`, 유효 window 조건 |
| [GaussianStreamAccumulator](proofs/GaussianStreamAccumulator.ec) | `gauss_trace_result_stream_accumulator`, `sample_gauss_at_stream_accumulator_correct`, `gauss_stream_finite_partitions` | 누적 승인 개수 `≤512`에 따른 정수 예산으로 호출 간 누적합과 오버플로 여유 보존; 매 호출 후 상위 limb가 48비트라는 가정을 요구하지 않음 |
| [GaussianStreamSequence](proofs/GaussianStreamSequence.ec) | `gauss_stream_events_append_available`, `gauss_visible_output_concat`, `sample_gauss_at_dummy_last_total` | 연속 byte 함수의 후보열 분할·결합, 승인 순서와 동일 dummy flag 유지, 실제 offset 소비기의 dummy 슬롯 보존 |
| [GaussianStreamBuffer](proofs/GaussianStreamBuffer.ec) | `gs_stream_advance`, `gs_refill_segment`, `gs_copy_signs_total` | 초기 49블록과 refill의 후보 수·잔여 바이트 대응, 연속 스트림의 버퍼 구간 연결, 실제 32바이트 부호 복사·frame·종료 |
| [GaussianStreamSpec](theories/GaussianStreamSpec.ec) | `gs_selected_complete_stable`, `gs_stream_result_unique` | 충분한 후보 prefix 이후 처음 `n`개 승인 결과가 불변이며, 같은 초기값과 스트림을 만족하는 전체 반환 튜플은 유일함 |
| [GaussianStreamComposition](proofs/GaussianStreamComposition.ec) | `gs_progress_consume`, `gs_progress_consume_correct` | 실제 offset 소비 호출을 연속 스트림의 다음 후보 구간에 연결; 승인 개수·저장 순서·dummy·출력 frame·정확한 제곱합 불변식 보존 |
| [GaussianStreamCorrectness](proofs/GaussianStreamCorrectness.ec) | `sample_gauss_N_full_at_correct` | 실제 `_sf_sample_gauss_N_full_at`가 종료하면 seed·nonce의 word SHAKE 스트림에서 처음 승인된 `n`개 후보와 동일한 결과를 반환; 초기 49블록·부호 복사·반복 refill 전체 포함; `n=256/257`, 유효 offset, 초기 두 limb `<2^48`인 Hoare 부분 정확성 |
| [GaussianRefillCorrectness](proofs/GaussianRefillCorrectness.ec) | `gauss_carry_total`, `gauss_carry_squeeze_layout` | 실제 carry가 첫 블록의 부호 prefix 여부를 반영해 잔여 바이트를 보존하며 종료; carry·블록 직렬화 계약을 결합한 유한 버퍼 배치 |
| [SHAKEBlockCorrectness](proofs/SHAKEBlockCorrectness.ec) | `keccakf1600_word_total`, `squeeze256_word_total` | 실제 signer의 24라운드 word 순열 대응과 136바이트 출력·외부 영역 보존·종료; 출력 offset `0…8056` |
| [SHAKESeedInitCorrectness](proofs/SHAKESeedInitCorrectness.ec) | `seed_init_total`, `shake_block_stream_total` | 실제 초기화가 seed 64바이트·nonce 하위 16비트·domain/padding의 전체 200바이트 상태와 일치하며 종료; 각 squeeze가 word 스트림의 정확한 다음 136바이트와 대응 |
| [HyperballGaussianBounds](proofs/HyperballGaussianBounds.ec) | `hb_sigma76_square_high_bound`, `hb_cumulative_canonical`, `hb_sample_gauss_N_full_at_correct` | square-high `<2^36`으로 범위를 강화; 0에서 최대 2,818개 승인 후보를 누적해도 두 초기 limb `<2^48` 유지; 여러 Gaussian 호출의 전제 연결 |
| [HyperballFixedPointCorrectness](proofs/HyperballFixedPointCorrectness.ec) | `hb_newton_total`, `hb_half_round_integer_total`, `hb_mul_rnd13_signed_fit` | 곱셈·조건부 부호·정규화·초기 추정과 Newton 6회 반복의 정확한 word 계산과 종료; canonical low에서 정수 올림 반분, 명시적 fit 아래 signed W32 의미 |
| [HyperballScaleCorrectness](proofs/HyperballScaleCorrectness.ec) / [HyperballNormCorrectness](proofs/HyperballNormCorrectness.ec) | `hb_scale_samples_total`, `hb_scale_and_check_total` | 전역 sample/sign 인덱스, 출력 분할·보존, signed32 제곱합의 mod `2^64` 계산과 unsigned 승인 판정·종료; 정수 norm 해석은 별도 조건부 정리 |
| [HyperballBatchCorrectness](proofs/HyperballBatchCorrectness.ec) / [HyperballHistoryCorrectness](proofs/HyperballHistoryCorrectness.ec) | `hb_batch_call_correct`, `hb_history_append`, `hb_history_finish` | 처음 두 번 257개·나머지 256개 승인 후보, 정확한 누적합, 실제 호출 연결; 이전 시도의 거부 이력과 최초 승인 결과·카운터 연결 |
| [HyperballByteCorrectness](proofs/HyperballByteCorrectness.ec) | `hyperball_b_raw_array_total` | 마지막 nonce의 seed SHAKE 첫 바이트와 실제 반환 배열 일치·종료 |
| [HyperballCorrectness](proofs/HyperballCorrectness.ec) | `hyperball_full_correct`, `hyperball_mode2_correct`, `hyperball_mode3_correct`, `hyperball_mode5_correct` | 실제 전체 함수와 mode 2·3·5의 word 명세에 대한 Hoare 부분 정확성; Gaussian 배치·고정소수점 scaling·모듈러 norm·retry·최종 byte/counter; mode 상수는 C에서 독립 생성 |
| [HyperballResultUniqueness](proofs/HyperballResultUniqueness.ec) / [HyperballResultProperties](proofs/HyperballResultProperties.ec) | `hb_result_unique`, `hb_result_modular_norm`, `hb_result_integer_norm` | 미사용 scratch 영역·블록 증인과 무관한 전체 반환값 유일성, 출력 보존 및 모듈러 norm; 수학적 norm은 `<2^64` 또는 명시적 좌표 범위에서 연결 |
| [HyperballNormBoundary](proofs/HyperballNormBoundary.ec) | `hyperball_mode{2,3,5}_prescribed_norm_boundary` | 구성한 좌표 벡터의 정수 제곱합·64비트 나머지·bound 비교를 확인하는 산술 정리; 실제 SHAKE 시드 도달 가능성 주장은 없음 |
| [SigningSamplerBridge](proofs/SigningSamplerBridge.ec) | `signer_cdt83_total_correct`, `signer_smulh48_total_correct`, `signer_approx_exp_reference_total_correct`, `signer_sigma76_total_correct` | 위 CDT·올림·Horner·단일 시도 결과를 실제 mode 2/3/5 서명 추출물의 내부 함수에 전달 |
| [NTTCorrectness](proofs/NTTCorrectness.ec) | `target_poly_ntt_jazz_total`, `target_poly_invntt_jazz_total`, `target_poly_invntt_jazz_total18` | 입력 계수 범위와 기록된 산술 가정 아래 `NTTFullSpec.full_ntt/full_invntt` 대응과 종료; 역변환의 Montgomery 인자 포함 |
| [ApiBoundaryCorrectness](proofs/ApiBoundaryCorrectness.ec) | `api_copy_addr_to_addr_backward_correct`, `api_zero_raw_len64_correct` | canonical/no-wrap 주소, 안전한 alias 조건 아래 원래 byte 복사·영 초기화와 frame; 일반 `_api_prepare_pre_raw` 결과는 현재 사용되지 않는 소스 helper에 한정 |
| [ProductionApiCorrectness](proofs/ProductionApiCorrectness.ec) | `production_sf_prepare_pre_raw_total_correct`, `production_sign_backward_copy_total_correct`, `production_verify_zero_total_correct` | 실제 호출되는 signer 문맥 helper, Sign 역방향 복사, Verify 영 초기화의 정확성·종료성 |

`phoare [...] = 1`인 결정적 함수의 정리는 해당 전제 아래 종료와 결과를 함께
보장한다. 이것을 난수 입력 분포나 완전한 서명 성공 확률에 대한 정리로 해석하지
않는다. `sigma76_from_cdt_contract` 같은 중간 합성 정리의 CDT 전제는 최종
`sigma76_*_correct` 정리에서 실제 CDT 정리로 해소했다.

## 중요한 전제와 한계

- CDT 분포 정리는 `Uniform83Jasmin.sample`의 명시적 균등 정수 입력에 관한 것이다.
  비교 대상은 공식 명세 260904 §5.1.1과 그 참고문헌 [21]의 정의에서 가져온
  `exp(-k²/512)/sum_{j≥0}exp(-j²/512)`이다. 구현 테이블을 사용해 목표 분포를
  정의하거나 C 주석의 floor-CDF 공식을 가정하지 않았다. 무한 합의 정규화와
  수치 인증서도 증명했다. [명세 대응과 증명 경계](docs/cdt-distribution-correspondence.md)에
  출처·해시·연결 과정을 기록한다.
- 이 단일 CDT의 통계적 거리 상한은 SHAKE의 균등성·독립성이나 sigma76의
  거부 샘플링 분포를 자동으로 보장하지 않는다. 공식 명세는 별도 CDT 오차
  예산을 명시하지 않으며, 지수 다항식 거부에 대한 Rényi 경계는 다른 의무다.
  `RealExp`·`RealSeries`·`Distr`·`SDist`의 표준 분석·확률 기반도 신뢰 범위에 포함된다.
- 지수함수 오차 정리는 실제 고정소수점 입력 xi/2^48의 정수 격자를 대상으로 한다.
  실제 C 계수 다항식의 오차와 실행 중 올림 오차를 함께 포함한다.
  [수학적 경계와 연결](docs/approx-exp-mathematical-bound.md)에 입력 범위,
  인증서와 실제 프로시저 정리를 기록했다. Horner 중간 결과의 signed64 의미를
  정당화했지만, smulh48 내부의 의도된 unsigned word 연산까지 무래핑이라고
  부르지는 않는다.
- 승인 확률 정리는 실제 sigma 함수를 호출하며 거부 바이트만 균등하게 바꾼다.
  비교 대상은 실제 양자화된 xi와 실제 반올림 출력이 0일 때의 α=1/2 보정을
  유지한다. 이후 raw 지수 오차와 raw-zero 보정 차이는 아래 새 정리로 연결했다. C 주석의
  단방향 ceiling, 공식 Rényi 오차, 승인된 전체 Gaussian 표본 분포는 별도 의무다.
- NTT의 `poly_repr_bound rp p s`는 각 signed word가 `p`의 계수를 mod 64513으로
  나타내고 `[-2^s,2^s)`에 있다는 뜻이다. 순변환은 `s=16→24`, 역변환은
  `s=16/18→16`이다. 출력 24-bit 범위를 그대로 역변환 전제로 넣는 정리는 없다.
- Gaussian 소비기는 승인되기 전에 후보를 써 놓을 수 있다. 따라서 보존 범위는
  반환 승인 수가 아닌 **요청 길이 `n` 이후**이다. 승인 표본열 정리는 반환
  승인 수와 저장 가능 길이의 최솟값까지만 읽는다. `dont_write_last≠0`이면 마지막
  dummy 후보도 승인 개수와 제곱합에는 포함되지만 해당 슬롯은 원래 값을 보존한다.
- 제곱합은 초기값과 **승인 후보가 반환한 square limbs**의 합이다. 이를 반올림된
  출력값의 제곱이나 이상적인 실수 제곱의 합이라고 부르지 않는다. 초기 낮은 limb가
  임의의 64비트 값이면 덧셈 때 유실되는 carry 때문에 전체 합의 무조건적인
  mod `2^112` 동치도 성립하지 않는다. 일반 정리는 headroom을 명시하고, 초기
  두 limb가 각각 48비트이면 그 전제를 구체적 범위 정리로 해소한다.
- 초기 49블록은 `49×136−32=6632=255×26+2`바이트의 후보 입력을 제공한다.
  실제 길이 256·257 요청은 refill이 필요하다. 각 refill에서 남는 0…25바이트와
  새 136바이트의 배치를 실제 `_sf_sample_gauss_N_full_at`의 전체 반복문에
  연결했다. 반환 시 보이는 표본은 256개, 부호는 32바이트이며, 257번째 dummy는
  제곱합에 포함되고 출력 슬롯은 보존된다.
- 호출 간 누적합 정리는 `gauss_stream_acc_ok`의 총 정수 예산을 사용한다.
  상위 limb의 48비트 범위가 매번 유지된다고 가정하지 않는다. 한 Gaussian 호출
  안의 반복 refill에는 이 불변식을 연결했다. Hyperball에서는 더 강한 square-high
  상한과 `256*i + min(i,2)`의 누적 승인 개수로 각 polynomial 호출의 초기 두 limb
  조건을 증명했다. mode 5의 최대 개수는 2,818이다.
- 전체 Gaussian 함수 정리는 **종료한 실행의 반환값**에 관한 것이다. 고정된
  seed가 항상 충분한 승인 후보를 공급한다는 전제나 무조건 종료 정리를 추가하지
  않았다. 결과 명세의 유한 prefix 증인은 `gs_stream_result_unique`에 의해
  서로 다른 반환값을 허용하지 않는다.
- Hyperball 전체 정리도 종료한 실행의 **word 명세 대응**이다. 모든 이전 시도의
  거부와 마지막 승인을 이력에 기록하고, 미사용 scratch 영역을 제외한 모든 입력을
  구체적인 Gaussian 스트림에 연결한다. 반환값 유일성은 nonce의 단사성을 가정하지
  않는다. 실제 내부 카운터는 W64 덧셈이며 SHAKE에는 하위 16비트만 들어간다.
- Hyperball의 norm 승인은 `N mod 2^64 <= bound`이다. `N`은 저장된 signed32
  계수의 수학적 제곱합이다. `N < 2^64`가 있어야 정수 반경 판정으로 해석할 수
  있다. 모든 좌표 절댓값 `<=2^26`, 총 2,816개 이하라는 충분조건도 증명했지만,
  실제 모든 scaling 출력이 이를 충족한다는 전제는 추가하지 않았다.
  [수치 경계와 재현](docs/hyperball-numerical-boundary.md)에 구성한 후보열의
  C/Jasmin 동일 wrap 사례를 기록했다. 실제 SHAKE 시드 반례는 제시하지 않는다.
- Newton 정리는 초기 추정과 6회 갱신의 정확한 word 계산을 증명한다. 실수
  역제곱근 수렴·근사 오차나 모든 중간 계산의 무오버플로를 뜻하지 않는다.
  C 참조 코드도 드물게 첫 추정값이 음수일 수 있음을 명시한다.
- 단일 SHAKE 블록은 [word 명세](theories/SHAKEBlockSpec.ec)의 24라운드 순열과
  연결했다. [스트림 명세](theories/SHAKEStreamSpec.ec)는 64바이트 seed와 nonce
  하위 2바이트의 흡수·패딩 및 반복 squeeze를 포함한다. 임의 길이 입력의 sponge나
  FIPS 202의 bit 명세와의 별도 동치는 포함하지 않는다. 재사용한 정의·증명의 출처는
  [SHAKE 출처 목록](manifests/shake-support-origin.tsv)에 기록했다.
- rounded 표본에는 새 정수 연결과 무래핑 정리가 있다. 이를 전체 제곱·Horner
  계산의 모든 중간값이나 실수 Gaussian 계산의 무오버플로 정리로 확대하지 않는다.
- `_api_prepare_pre_raw`와 실제 `_sf_prepare_pre_raw`는 다른 구현이다.
  현재 production 문맥 주장은 후자를 직접 검증한 정리에 근거한다.
- 메모리는 `Glob.mem`의 총 byte map이다. canonical/no-wrap과 alias 조건은
  실제 OS 할당·메모리 접근 권한이나 caller의 C ABI 검증을 대체하지 않는다.
- NTT의 남은 산술 가정은 [별도 목록](manifests/ntt-assumptions.md)에 명시한다.
  새 샘플러/API 정리에 알고리즘 정확성을 가정하는 공리는 추가하지 않았다.

반올림 전 수락식 정리는 [별도 수식 기록](docs/raw-gaussian-acceptance.md)의
`Z=y+2^72x`, `E=y(y+2^73x)/2^153`을 비교 대상으로 사용한다. 고정 후보가
예외 구간에 있으면 승인 확률 차이가 약 1/2일 수 있으므로, 모든 고정 후보에서
작은 raw-reference 오차가 성립한다고 주장하지 않는다. 평균 정리는 명시적인
균등 72비트 잡음과 독립 균등 48비트 거부 입력의 실제 단일 시도에 관한 것으로,
승인 후 표본 분포나 실제 SHAKE에 대한 정리가 아니다.

## 아직 증명하지 않은 부분

| 의무 | 현재 경계와 다음 연결 |
| --- | --- |
| Gaussian 분포 합성 | CDT 근사·실제 xi의 raw 지수 오차·두 zero 규칙의 예외·명시적 균등 입력의 평균 승인 확률까지 연결. 다음에는 승인된 출력의 부분확률 질량, CDT 분포, 출력 반올림·부호, 거부 정규화·반복 표본을 합성. 공식 Rényi 오차와 이상적 XOF 연결은 별도 증명 |
| 별도 Gaussian 경로 | raw seed 주소를 받는 `_sample_gauss_N_full_at`와 서명용 `_sf_sample_gauss_N_full_at`의 대응 및 메모리 계약 연결; 현재 전체 함수 정리는 후자에 한정 |
| SHAKE sponge | 검증된 고정 길이 seed/nonce word 스트림과 bit/FIPS 명세의 별도 동치, 임의 길이 입력의 sponge |
| Hyperball의 수학·확률 의미 | 실제 seed에 대한 수치 범위/예외 사건, 실수 Newton 수렴·오차, 이상적인 분포와 종료성; word 승인을 무조건적인 기하학적 반경 보장으로 승격하지 않음 |
| KeyGen 전체 | `_keypair_full_m23/m5`의 샘플링·행렬·FFT guard·packing·retry를 공개 키/비밀 키 관계와 합성 |
| Sign 전체 | `_sf_signature_core_mode{2,3,5}`의 challenge·응답·norm·hint·packing과 retry를 서명 명세로 합성 |
| Verify 전체 | `_verify_full_mode{2,3,5}`의 decode·matrix/CRT·norm·challenge와 반환 판정을 검증 명세로 합성 |
| Sign→Verify | 정당한 KeyGen/Sign 결과가 같은 메시지·문맥에서 실제 Verify에 의해 승인됨을 증명 |
| 최종 연결 | C descriptor 래퍼·난수 바인딩·실제 메모리 계약과 컴파일된 어셈블리 연결; 전체 구현 보안 |

따라서 이 프로젝트의 검증 게이트 PASS는 **등록된 구성요소 정리의 성공**이다.
전체 HAETAE-1.2.0 구현 정확성 완료를 나타내는 상태로 사용하지 않는다.
