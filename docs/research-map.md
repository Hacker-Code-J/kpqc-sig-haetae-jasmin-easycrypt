# 논문–아티팩트 대응표

이 표는 연구 주장에 해당하는 구현·정리·검사 명령을 찾기 위한 색인이다.
정리가 파일에 존재한다는 사실과 현재 공개 소스로 그 정리를 재검사한 사실은
구분한다. 실행 결과는 [검증 기록](../haetae-easycrypt/VALIDATION.md)과 해당
실행의 소스 해시·대상 목록을 확인한다.

논문 식별자는 현재 원고의 LaTeX label이다. 장·절·정리 번호가 바뀌어도 같은
주장을 찾을 수 있도록 번호 대신 label을 적었다. 원고와 최종 출판 정보 자체를
이 저장소에 포함했다는 뜻은 아니다. 이 저장소의 대상은 HAETAE이며 논문의
NTRU+ 결과는 여기에 포함되지 않는다.

## 주장과 증명

아래 경로의 `E`는 `haetae-easycrypt`, `H`는 `haetae-hardened`를 뜻한다.
실제 파일로 이동하는 링크와 대표 공개 정리 이름을 함께 적었다. 대표 정리만
읽으면 의존 증명이나 전제 검사가 생략될 수 있으므로 재현에는 검증기를 사용한다.

| 논문에서 찾을 주장·label | 구현 또는 모형 | 대표 정리·파일 | 범위와 전제 | 재현 |
| --- | --- | --- | --- | --- |
| HAETAE NTT 곱셈, `thm:haetae-ntt-composition` | `poly_ntt_jazz`, pointwise 곱, `poly_invntt_jazz` | [`NTTCompositionInstance.ec`](../haetae-easycrypt/proofs/NTTCompositionInstance.ec): `haetae_ntt_product_total` | 계수 표현·범위와 Montgomery 배율을 포함한 합성; [산술 가정](../haetae-easycrypt/manifests/ntt-assumptions.md) 확인 | N |
| 실제 도전 다항식·행렬 곱의 연결, `sec:haetae-ntt-composition` | `sign_compute_cs2_jazz`, `keypair_m23_matrix_jazz`, `keypair_m5_matrix_jazz` | [`NTTProductCorrectness.ec`](../haetae-easycrypt/proofs/NTTProductCorrectness.ec): `sign_compute_cs2_total`; [`NTTMatrixProductCorrectness.ec`](../haetae-easycrypt/proofs/NTTMatrixProductCorrectness.ec): `matrix_m23_export_total`, `matrix_m5_export_total` | 배열 크기·표현·계수 범위 계약을 만족하는 호출 | N |
| Gaussian 후보 산술, `prop:gaussian-candidate-contracts` | `sample_gauss83_jazz`, `approx_exp_jazz`, sigma76 경로 | [`CDTCorrectness.ec`](../haetae-easycrypt/proofs/CDTCorrectness.ec): `sample_gauss83_jazz_total`; [`ApproxExpNumericalCorrectness.ec`](../haetae-easycrypt/proofs/ApproxExpNumericalCorrectness.ec): `sigma76_approx_exp_numerical_total` | 정수·워드 계산과 종료; 지수근사의 입력 구간과 반올림을 포함 | E |
| CDT와 Gaussian 기준 분포, `sec:gaussian-correctness` | 균등 83비트 입력 실험 | [`CDTGaussianApproximation.ec`](../haetae-easycrypt/proofs/CDTGaussianApproximation.ec): `uniform83_jasmin_half_gaussian_error` | 비음수 이산 Gaussian과 통계적 거리 `<2^-78`; 구체적 SHAKE 분포에 대한 명제가 아님 | E |
| 부호 있는 버퍼 출력, `prop:gaussian-signed` | iid 바이트·carry·부호 모형과 실제 소비 함수 | [`GaussianSignedCorrectness.ec`](../haetae-easycrypt/proofs/GaussianSignedCorrectness.ec): `gsc_actual_gaussian_event` | `gib_bounds n offset signoff` 아래 256개 signed 정수 관측의 거리 `<2^-31`; signed32 저장 의미에는 별도 fit 조건 | E |
| 거부율·기대 후보 시도 횟수, `sec:gaussian-rejection-counts` | `SigmaJoint203Experiment`, 독립 후보 재시도 | [`GaussianAcceptanceActual.ec`](../haetae-hardened/easycrypt/proofs/GaussianAcceptanceActual.ec): `gaa_extracted_rejection`; [`GaussianAttemptExpectation.ec`](../haetae-hardened/easycrypt/proofs/GaussianAttemptExpectation.ec): `gae_actual_expected_count_bound` | 평균 거부율 `<1/20`, 성공까지 기대 후보 수 `<20/19`; 고정 후보별 하한이나 Hyperball 외부 반복 비용과 구분 | G |
| 원본 반지름 검사 반례, `sec:hyperball-witnesses` | 실제 Gaussian 소비·Newton·scale·norm 호출 | [`HyperballWitnessReplay.ec`](../haetae-easycrypt/proofs/HyperballWitnessReplay.ec): `hbwr_accepted_outside_radius_total` | 구성한 후보열에서의 승인과 정수 반지름 위반; 대응 SHAKE seed의 존재·도달성은 주장하지 않음 | E, W |
| 원본 한 시도의 반지름 위반 확률, `prop:hyperball-unsafe-attempt` | `HyperballIidAttempt.sample` | [`HyperballIidAttemptSafety.ec`](../haetae-easycrypt/proofs/HyperballIidAttemptSafety.ec): `hia_accepted_outside_bound`, `hia_terminates` | iid 한 시도에서 승인 AND 반지름 위반이라는 결합 사건; 수락 조건부·외부 반복 경계와 구분 | E |
| 보강 판정의 전체 정확성, `prop:checked-acceptance` | `_hb_checked_scale_and_check_values` | [`CheckedAcceptanceCorrectness.ec`](../haetae-hardened/easycrypt/proofs/CheckedAcceptanceCorrectness.ec): `hca_scale_and_check_total` | 배열 길이 계약 아래 항상 종료하며 승인하면 실제 정수 제곱합 ≤ 상한; 사전 무오버플로 가정 없음 | H |
| 보강된 실제 반환 경로, `prop:checked-production` | 서명용·독립 Hyperball·공개 phase 경로 | [`CheckedProductionCorrectness.ec`](../haetae-hardened/easycrypt/proofs/CheckedProductionCorrectness.ec): `hpc_signer_full_safe`, `hpc_standalone_full_safe` | 전체 Hyperball에서는 반환한 실행의 안전성; 외부 반복 종료를 포함하지 않음 | H, W |
| 지수근사·한 시도 출력의 Rényi 비교 | exact-exponential 기준, 보강 후보와 승인 비트 | [`GaussianRenyiProduction.ec`](../haetae-hardened/easycrypt/proofs/GaussianRenyiProduction.ec): `grp_renyi_bounds`; [`HyperballRenyiProduction.ec`](../haetae-hardened/easycrypt/proofs/HyperballRenyiProduction.ec): `hrf_common_bound` | 정수 차수 2–1024, 명시한 iid 한 시도 법칙; 전체 이상적 마스크·승인 조건부분포·UF-CMA로 자동 확대하지 않음 | R |
| CT/SCT 공개 정책, `sec:haetae-implementation-security` | 보강 산술 검사와 명시적 declassification | [`check-ct.sh`](../haetae-hardened/scripts/check-ct.sh) | 해당 검사 도구·선택 함수·허용한 공개 정보에 상대적인 결과 | C |

Rényi 행은 관련 연구 증명의 위치를 안내한다. 현재 원고의
`sec:haetae-security-composition`에서 설명하는 최종 서명 보안 합성의 남은
의무를 이 행으로 대체하지 않는다. API 관련 증명도 전체 API의 증명과 구분한다.
예를 들어 [`ProductionApiCorrectness.ec`](../haetae-easycrypt/proofs/ProductionApiCorrectness.ec)는
복사·초기화 등 메모리 보조함수의 계약을 다룬다.

## 재현 명령

명령은 저장소 루트에서 [환경 안내](../env/README.md)에 따라 환경을 활성화한
뒤 실행한다. 전체 묶음은 `bash scripts/reproduce.sh full`을 사용한다.
개별 증명 파일을 검사하는 것만으로 전체 의존 증명의 재검사를 대신하지 않는다.
보강안 명령을 개별 실행할 때에는 먼저
`python3 haetae-hardened/scripts/materialize.py`로 검증 대상 구현을 구성한다.

| 코드 | 실행 명령 |
| --- | --- |
| E | `make -C haetae-easycrypt verify-new` |
| N | `make -C haetae-easycrypt verify-ntt` |
| H | `python3 haetae-hardened/scripts/verify.py --group all` |
| G | `python3 haetae-hardened/scripts/verify.py --group gaussian-rate` |
| R | `python3 haetae-hardened/scripts/verify.py --group gaussian-renyi`와 `--group hyperball-renyi` |
| W | `make -C haetae-easycrypt test-hyperball-boundary`; 보강안은 `make -C haetae-jasmin libs`와 `make -C haetae-hardened libs` 후 `python3 haetae-hardened/tests/checked-hyperball.py` |
| C | `bash haetae-hardened/scripts/check-ct.sh` |

공식 KAT·서명·API·상호운용의 유한 실행 검사는 `make -C haetae-jasmin test`와
`make -C haetae-hardened test`로 재현한다. 이 결과는 위 정리의 전제나 전체
암호학적 안전성 증명을 대체하지 않는다.

## 공통 신뢰 경계

- 프로그램 정리는 Jasmin 추출 모형과 명시한 배열·포인터 계약에 대한 것이다.
  임의 포인터의 native 실행, ABI 전체, 컴파일러·검증기 자체의 정확성은 별도 경계다.
- iid 분포 결과와 구체적 seeded SHAKE 실행을 구분한다. 부분 정확성은 종료한
  실행의 결과에 대한 것이며, 종료 정리는 명시된 모형·전제 아래에서만 적용한다.
- [원본의 상세 범위](../haetae-easycrypt/CLAIMS.md)와
  [보강안의 상세 범위](../haetae-hardened/README.md)를 함께 읽는다.
- 릴리스별로 이 대응표와 실제 검증 대상·소스 해시를 함께 고정한다. 새 연구 파일을
  추가했다고 과거 실행 기록의 대상 수나 성공 범위가 늘어나는 것은 아니다.
