# 검증 범위와 남은 의무

이 문서는 함수별 정리의 범위를 기록한다. 추출물의 로딩 성공, KAT 성공,
구성요소 정리와 전체 API 정확성을 구분한다.

## 현재 정리

| 정리 파일 | 대표 정리 | 정확한 범위 |
| --- | --- | --- |
| [SamplerConstants](proofs/SamplerConstants.ec) | `cdt83_hi_matches_reference`, `cdt83_lo_matches_reference`, `approx_exp_matches_reference` | 고정된 C에서 독립 생성한 CDT·다항식 상수와 Jasmin 명세 연결 |
| [CDTCorrectness](proofs/CDTCorrectness.ec) | `sample_gauss83_jazz_total`, `sample_gauss83_max83_total` | 입력 정수보다 작은 166개 임계값의 개수; 범위와 최대 입력 166; 확률 1 종료·결과 |
| [CDTTermination](proofs/CDTTermination.ec) | `sample_gauss83_ll` | 실제 두 bounded loop의 종료성 |
| [FixedPointCorrectness](proofs/FixedPointCorrectness.ec) | `smulh48_jazz_total_correct`, `smulh48_jazz_signed_correct`, `approx_exp_jazz_reference_correct` | 모든 word 입력의 올림 결과 modulo 2^64; signed 결과는 명시적 fit 전제; C-derived 10차 word Horner 계산 |
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
| [SigningSamplerBridge](proofs/SigningSamplerBridge.ec) | `signer_cdt83_total_correct`, `signer_smulh48_total_correct`, `signer_approx_exp_reference_total_correct`, `signer_sigma76_total_correct` | 위 CDT·올림·Horner·단일 시도 결과를 실제 mode 2/3/5 서명 추출물의 내부 함수에 전달 |
| [NTTCorrectness](proofs/NTTCorrectness.ec) | `target_poly_ntt_jazz_total`, `target_poly_invntt_jazz_total`, `target_poly_invntt_jazz_total18` | 입력 계수 범위와 기록된 산술 가정 아래 `NTTFullSpec.full_ntt/full_invntt` 대응과 종료; 역변환의 Montgomery 인자 포함 |
| [ApiBoundaryCorrectness](proofs/ApiBoundaryCorrectness.ec) | `api_copy_addr_to_addr_backward_correct`, `api_zero_raw_len64_correct` | canonical/no-wrap 주소, 안전한 alias 조건 아래 원래 byte 복사·영 초기화와 frame; 일반 `_api_prepare_pre_raw` 결과는 현재 사용되지 않는 소스 helper에 한정 |
| [ProductionApiCorrectness](proofs/ProductionApiCorrectness.ec) | `production_sf_prepare_pre_raw_total_correct`, `production_sign_backward_copy_total_correct`, `production_verify_zero_total_correct` | 실제 호출되는 signer 문맥 helper, Sign 역방향 복사, Verify 영 초기화의 정확성·종료성 |

`phoare [...] = 1`인 결정적 함수의 정리는 해당 전제 아래 종료와 결과를 함께
보장한다. 이것을 난수 입력 분포나 완전한 서명 성공 확률에 대한 정리로 해석하지
않는다. `sigma76_from_cdt_contract` 같은 중간 합성 정리의 CDT 전제는 최종
`sigma76_*_correct` 정리에서 실제 CDT 정리로 해소했다.

## 중요한 전제와 한계

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
  안의 반복 refill에는 이 불변식을 연결했다. Hyperball에서 여러 polynomial
  호출에 걸쳐 각 호출의 초기 두 limb 조건을 충족하는 정리는 아직 별도 의무다.
- 전체 Gaussian 함수 정리는 **종료한 실행의 반환값**에 관한 것이다. 고정된
  seed가 항상 충분한 승인 후보를 공급한다는 전제나 무조건 종료 정리를 추가하지
  않았다. 결과 명세의 유한 prefix 증인은 `gs_stream_result_unique`에 의해
  서로 다른 반환값을 허용하지 않는다.
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

## 아직 증명하지 않은 부분

| 의무 | 현재 경계와 다음 연결 |
| --- | --- |
| 별도 Gaussian 경로 | raw seed 주소를 받는 `_sample_gauss_N_full_at`와 서명용 `_sf_sample_gauss_N_full_at`의 대응 및 메모리 계약 연결; 현재 전체 함수 정리는 후자에 한정 |
| SHAKE sponge | 검증된 고정 길이 seed/nonce word 스트림과 bit/FIPS 명세의 별도 동치, 임의 길이 입력의 sponge |
| Hyperball | 여러 Gaussian 호출의 초기 제곱합 범위 충족, `_sf_hyperball_full`의 scaling·inverse square root·norm·retry, 분포와 종료 의무 |
| KeyGen 전체 | `_keypair_full_m23/m5`의 샘플링·행렬·FFT guard·packing·retry를 공개 키/비밀 키 관계와 합성 |
| Sign 전체 | `_sf_signature_core_mode{2,3,5}`의 challenge·응답·norm·hint·packing과 retry를 서명 명세로 합성 |
| Verify 전체 | `_verify_full_mode{2,3,5}`의 decode·matrix/CRT·norm·challenge와 반환 판정을 검증 명세로 합성 |
| Sign→Verify | 정당한 KeyGen/Sign 결과가 같은 메시지·문맥에서 실제 Verify에 의해 승인됨을 증명 |
| 최종 연결 | C descriptor 래퍼·난수 바인딩·실제 메모리 계약과 컴파일된 어셈블리 연결; 전체 구현 보안 |

따라서 이 프로젝트의 검증 게이트 PASS는 **등록된 구성요소 정리의 성공**이다.
전체 HAETAE-1.2.0 구현 정확성 완료를 나타내는 상태로 사용하지 않는다.
